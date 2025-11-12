package edu.uchicago.cs.systems.wasabi;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.io.EOFException;
import java.io.FileNotFoundException;
import java.net.BindException;
import java.net.ConnectException;
import java.net.SocketException;
import java.net.SocketTimeoutException;
import java.net.UnknownHostException;
import java.lang.InterruptedException;
import java.sql.SQLException;
import java.sql.SQLTransientException;

import java.util.concurrent.ConcurrentHashMap;
import java.util.Set;

import org.apache.cassandra.exceptions.MarshalException;
import org.apache.cassandra.exceptions.InvalidRequestException;
import org.apache.cassandra.exceptions.RequestFailureException;
import org.apache.cassandra.exceptions.RequestTimeoutException;
import org.apache.cassandra.exceptions.UnavailableException;
import org.apache.cassandra.exceptions.SSTableAcquisitionException;

import edu.uchicago.cs.systems.wasabi.ConfigParser;
import edu.uchicago.cs.systems.wasabi.WasabiLogger;
import edu.uchicago.cs.systems.wasabi.WasabiContext;
import edu.uchicago.cs.systems.wasabi.InjectionPolicy;
import edu.uchicago.cs.systems.wasabi.StackSnapshot;
import edu.uchicago.cs.systems.wasabi.InjectionPoint;
import edu.uchicago.cs.systems.wasabi.ExecutionTrace;

public aspect InterceptCassandra {
  private WasabiContext wasabiCtx = null;

  private static final String UNKNOWN = "UNKNOWN";

  private static final WasabiLogger LOG = new WasabiLogger();
  private static final String configFile = (System.getProperty("configFile") != null) ? System.getProperty("configFile") : "default.conf";
  private static final ConfigParser configParser = new ConfigParser(LOG, configFile);

  private Set<String> activeInjectionLocations = ConcurrentHashMap.newKeySet(); 
  private String testMethodName = UNKNOWN;

  pointcut testMethod():
    (@annotation(org.junit.Test) || 
     @annotation(org.junit.jupiter.api.Test)) &&
     !within(org.apache.hadoop.*.TestDFSClientFailover.*) &&
     !within(org.apache.hadoop.hdfs.*.TestOfflineImageViewer.*) &&
     !within(org.apache.hadoop.example.ITUseHadoopCodec.*);


  before() : testMethod() {
    this.wasabiCtx = new WasabiContext(LOG, configParser);
    this.LOG.printMessage(
      WasabiLogger.LOG_LEVEL_WARN, 
      String.format("[TEST-BEFORE]: Test ---%s--- started", thisJoinPoint.toString())
    );

    if (this.testMethodName != this.UNKNOWN) {
      this.LOG.printMessage(
        WasabiLogger.LOG_LEVEL_WARN, 
        String.format("[TEST-BEFORE]: [ALERT]: Test method ---%s--- executes concurrentlly with test method ---%s---", 
          this.testMethodName, thisJoinPoint.toString())
      ); 
    }

    this.testMethodName = thisJoinPoint.toString();
  }

  after() returning: testMethod() {
    if (this.wasabiCtx == null) { // This happens for non-test methods (e.g. config) inside test code
      return; // Ignore retry in "before" and "after" annotated methods
    }
    
    this.LOG.printMessage(
      WasabiLogger.LOG_LEVEL_WARN, 
      String.format("[TEST-AFTER]: [SUCCESS]: Test ---%s--- done", thisJoinPoint.toString())
    );

    this.wasabiCtx.printExecTrace(this.LOG, String.format(" Test: %s", this.testMethodName));

    this.testMethodName = this.UNKNOWN;
    this.wasabiCtx = null;
    this.activeInjectionLocations.clear();
  }

  after() throwing (Throwable t): testMethod() {
    if (this.wasabiCtx == null) { // This happens for non-test methods (e.g. config) inside test code
      return; // Ignore retry in "before" and "after" annotated methods
    }
    
    this.wasabiCtx.printExecTrace(this.LOG, String.format(" Test: %s", this.testMethodName));

    StringBuilder exception = new StringBuilder();
    for (Throwable e = t; e != null; e = e.getCause()) {
      exception.append(e);
      exception.append(" :-: ");
    }

    StackSnapshot stackSnapshot = new StackSnapshot();
    this.LOG.printMessage(
      WasabiLogger.LOG_LEVEL_WARN, 
      String.format("[TEST-AFTER] [FAILURE] Test ---%s--- | Failure message :-: %s| Stack trace:\n%s\n:-:-:\n\n", 
          thisJoinPoint.toString(), exception.toString(), stackSnapshot.toString())
    );
     
    this.testMethodName = this.UNKNOWN;
    this.activeInjectionLocations.clear();
  }

  /* 
   * Callback before calling Thread.sleep(...)
   */

   pointcut recordThreadSleep():
    (call(* java.lang.Object.wait(..)) ||
    call(* java.lang.Thread.sleep(..)) ||
    call(* java.util.concurrent.locks.LockSupport.parkNanos(..)) ||
    call(* java.util.concurrent.locks.LockSupport.parkUntil(..)) ||
    call(* java.util.concurrent.ScheduledExecutorService.schedule(..)) ||
    call(* java.util.concurrent.TimeUnit.*scheduledExecutionTime(..)) ||
    call(* java.util.concurrent.TimeUnit.*sleep(..)) ||
    call(* java.util.concurrent.TimeUnit.*timedWait(..)) ||
    call(* java.util.Timer.schedule*(..)) ||
    call(* java.util.TimerTask.wait(..)) ||
    call(* org.apache.hadoop.hbase.*.Procedure.suspend(..))) &&
    !within(edu.uchicago.cs.systems.wasabi.*);

  before() : recordThreadSleep() {
    try {
      if (this.wasabiCtx == null) { // This happens for non-test methods (e.g. config) inside test code
        return; // Ignore retry in "before" and "after" annotated methods
      }
    
      StackSnapshot stackSnapshot = new StackSnapshot();  
      for (String retryCallerFunction : this.activeInjectionLocations) {
        if (stackSnapshot.hasFrame(retryCallerFunction.split("\\(", 2)[0])) {
          String sleepLocation = String.format("%s(%s:%d)",
                      retryCallerFunction.split("\\(", 2)[0],
                      thisJoinPoint.getSourceLocation().getFileName(),
                      thisJoinPoint.getSourceLocation().getLine());

          this.wasabiCtx.addToExecTrace(sleepLocation, OpEntry.THREAD_SLEEP_OP, stackSnapshot);
          LOG.printMessage(
            WasabiLogger.LOG_LEVEL_WARN, 
            String.format("[THREAD-SLEEP] Test ---%s--- | Sleep location ---%s--- | Retry location ---%s---\n",
              this.testMethodName, 
              sleepLocation, 
              retryCallerFunction.split("\\(", 2)[0])
          );
        }
      }
    } catch (Exception e) {
      this.LOG.printMessage(
        WasabiLogger.LOG_LEVEL_ERROR, 
        String.format("Exception occurred in recordThreadSleep(): %s", e.getMessage())
      );
      e.printStackTrace();
    }
  }

  
  /* Inject IOException */

  pointcut injectIOException():
    ((withincode(* org.apache.cassandra.db.compaction.Scrubber.scrub(..)) && 
    call(* org.apache.cassandra.db.compaction.Scrubber.*ScrubInfo.getCompactionInfo(..) throws *Exception*)) ||
    (withincode(* org.apache.cassandra.db.compaction.Scrubber.scrub(..)) && 
    call(* org.apache.cassandra.utils.ByteBufferUtil.readWithShortLength(..) throws *Exception*)) ||
    (withincode(* org.apache.cassandra.hadoop.cql3.CqlRecordWriter.*RangeClient.run(..)) && 
    call(* org.apache.cassandra.hadoop.cql3.CqlRecordWriter.*RangeClient.preparedStatement(..) throws *Exception*)) ||
    (withincode(* org.apache.cassandra.hadoop.cql3.CqlRecordWriter.*RangeClient.run(..)) && 
    call(* java.util.concurrent.BlockingQueue.*.take(..) throws *Exception*)) ||
    (withincode(* org.apache.cassandra.hadoop.cql3.CqlRecordWriter.*RangeClient.run(..)) && 
    call(* org.apache.cassandra.hadoop.cql3.CqlRecordWriter.*RangeClient.preparedStatement(..) throws *Exception*)) ||
    (withincode(* org.apache.cassandra.service.StorageService.repairPaxosForTopologyChange(..)) && 
    call(* org.apache.cassandra.service.StorageService.tryRepairPaxosForTopologyChange(..) throws *Exception*)) ||
    (withincode(* org.apache.cassandra.utils.binlog.ExternalArchiver.ExternalArchiver(..)) && 
    call(* org.apache.cassandra.utils.binlog.ExternalArchiver.archiveFile(..) throws *Exception*))) &&
    !within(edu.uchicago.cs.systems.wasabi.*);

  after() throws IOException : injectIOException() {
    StackSnapshot stackSnapshot = new StackSnapshot();
    String retryCallerFunction = stackSnapshot.getSize() > 0 ? stackSnapshot.getFrame(0) : "???";
    String injectionSite = thisJoinPoint.toString();
    String retryException = "IOException";
    String injectionSourceLocation = String.format("%s:%d",
                  thisJoinPoint.getSourceLocation().getFileName(),
                  thisJoinPoint.getSourceLocation().getLine());

    if (this.wasabiCtx == null) {
      LOG.printMessage(
        WasabiLogger.LOG_LEVEL_WARN, 
        String.format("[Pointcut] [Non-Test-Method] Test ---%s--- | Injection site ---%s--- | Injection location ---%s--- | Retry caller ---%s---\n",
          this.testMethodName, 
          injectionSite, 
          injectionSourceLocation, 
          retryCallerFunction)
      );

      return;
    }

    LOG.printMessage(
      WasabiLogger.LOG_LEVEL_WARN, 
      String.format("[Pointcut] Test ---%s--- | Injection site ---%s--- | Injection location ---%s--- | Retry caller ---%s---\n",
        this.testMethodName, 
        injectionSite, 
        injectionSourceLocation, 
        retryCallerFunction)
    );

    InjectionPoint ipt = this.wasabiCtx.getInjectionPoint(this.testMethodName,
                               injectionSite, 
                               injectionSourceLocation,
                               retryException,
                               retryCallerFunction, 
                               stackSnapshot);
    if (ipt != null && this.wasabiCtx.shouldInject(ipt)) {
      this.activeInjectionLocations.add(retryCallerFunction);
    
      long threadId = Thread.currentThread().getId();
      throw new IOException(
        String.format("[wasabi] [thread=%d] [Injection] Test ---%s--- | ---%s--- thrown after calling ---%s--- | Retry location ---%s--- | Retry attempt ---%d---",
          threadId,
          this.testMethodName,
          ipt.retryException,
          ipt.injectionSite,
          ipt.retrySourceLocation,
          ipt.injectionCount)
      );
    }
  }

  /* Inject MarshalException */

  pointcut injectMarshalException():
    ((withincode(* org.apache.cassandra.db.compaction.Scrubber.scrub(..)) && 
    call(* org.apache.cassandra.db.marshal.AbstractType.*.validate(..) throws *Exception*))) &&
    !within(edu.uchicago.cs.systems.wasabi.*);

  after() throws MarshalException : injectMarshalException() {
    StackSnapshot stackSnapshot = new StackSnapshot();
    String retryCallerFunction = stackSnapshot.getSize() > 0 ? stackSnapshot.getFrame(0) : "???";
    String injectionSite = thisJoinPoint.toString();
    String retryException = "MarshalException";
    String injectionSourceLocation = String.format("%s:%d",
                  thisJoinPoint.getSourceLocation().getFileName(),
                  thisJoinPoint.getSourceLocation().getLine());

    if (this.wasabiCtx == null) {
      LOG.printMessage(
        WasabiLogger.LOG_LEVEL_WARN, 
        String.format("[Pointcut] [Non-Test-Method] Test ---%s--- | Injection site ---%s--- | Injection location ---%s--- | Retry caller ---%s---\n",
          this.testMethodName, 
          injectionSite, 
          injectionSourceLocation, 
          retryCallerFunction)
      );

      return;
    }

    LOG.printMessage(
      WasabiLogger.LOG_LEVEL_WARN, 
      String.format("[Pointcut] Test ---%s--- | Injection site ---%s--- | Injection location ---%s--- | Retry caller ---%s---\n",
        this.testMethodName, 
        injectionSite, 
        injectionSourceLocation, 
        retryCallerFunction)
    );

    InjectionPoint ipt = this.wasabiCtx.getInjectionPoint(this.testMethodName,
                               injectionSite, 
                               injectionSourceLocation,
                               retryException,
                               retryCallerFunction, 
                               stackSnapshot);
    if (ipt != null && this.wasabiCtx.shouldInject(ipt)) {
      this.activeInjectionLocations.add(retryCallerFunction);
    
      long threadId = Thread.currentThread().getId();
      throw new MarshalException(
        String.format("[wasabi] [thread=%d] [Injection] Test ---%s--- | ---%s--- thrown after calling ---%s--- | Retry location ---%s--- | Retry attempt ---%d---",
          threadId,
          this.testMethodName,
          ipt.retryException,
          ipt.injectionSite,
          ipt.retrySourceLocation,
          ipt.injectionCount)
      );
    }
  }

  /* Inject AssertionError */

  pointcut injectAssertionError():
    ((withincode(* org.apache.cassandra.service.StorageService.repairPaxosForTopologyChange(..)) && call(* org.apache.cassandra.service.StorageService.tryRepairPaxosForTopologyChange(..) throws *Exception*))) &&
    !within(edu.uchicago.cs.systems.wasabi.*);

  after() throws AssertionError : injectAssertionError() {
    StackSnapshot stackSnapshot = new StackSnapshot();
    String retryCallerFunction = stackSnapshot.getSize() > 0 ? stackSnapshot.getFrame(0) : "???";
    String injectionSite = thisJoinPoint.toString();
    String retryException = "AssertionError";
    String injectionSourceLocation = String.format("%s:%d",
                  thisJoinPoint.getSourceLocation().getFileName(),
                  thisJoinPoint.getSourceLocation().getLine());

    if (this.wasabiCtx == null) {
      LOG.printMessage(
        WasabiLogger.LOG_LEVEL_WARN, 
        String.format("[Pointcut] [Non-Test-Method] Test ---%s--- | Injection site ---%s--- | Injection location ---%s--- | Retry caller ---%s---\n",
          this.testMethodName, 
          injectionSite, 
          injectionSourceLocation, 
          retryCallerFunction)
      );

      return;
    }

    LOG.printMessage(
      WasabiLogger.LOG_LEVEL_WARN, 
      String.format("[Pointcut] Test ---%s--- | Injection site ---%s--- | Injection location ---%s--- | Retry caller ---%s---\n",
        this.testMethodName, 
        injectionSite, 
        injectionSourceLocation, 
        retryCallerFunction)
    );

    InjectionPoint ipt = this.wasabiCtx.getInjectionPoint(this.testMethodName,
                               injectionSite, 
                               injectionSourceLocation,
                               retryException,
                               retryCallerFunction, 
                               stackSnapshot);
    if (ipt != null && this.wasabiCtx.shouldInject(ipt)) {
      this.activeInjectionLocations.add(retryCallerFunction);
    
      long threadId = Thread.currentThread().getId();
      throw new AssertionError(
        String.format("[wasabi] [thread=%d] [Injection] Test ---%s--- | ---%s--- thrown after calling ---%s--- | Retry location ---%s--- | Retry attempt ---%d---",
          threadId,
          this.testMethodName,
          ipt.retryException,
          ipt.injectionSite,
          ipt.retrySourceLocation,
          ipt.injectionCount)
      );
    }
  }

  /* Inject InvalidRequestException */

  pointcut injectInvalidRequestException():
    ((withincode(* org.apache.cassandra.service.paxos.Paxos.cas(..)) && call(* org.apache.cassandra.service.CASRequest.makeUpdates(..) throws *Exception*)) ||
        (withincode(* org.apache.cassandra.service.paxos.Paxos.cas(..)) && call(* org.apache.cassandra.service.CASRequest.appliesTo(..) throws *Exception*)) ||
        (withincode(* org.apache.cassandra.service.paxos.Paxos.cas(..)) && call(* org.apache.cassandra.triggers.TriggerExecutor.execute(..) throws *Exception*))) &&
    !within(edu.uchicago.cs.systems.wasabi.*);

  after() throws InvalidRequestException : injectInvalidRequestException() {
    StackSnapshot stackSnapshot = new StackSnapshot();
    String retryCallerFunction = stackSnapshot.getSize() > 0 ? stackSnapshot.getFrame(0) : "???";
    String injectionSite = thisJoinPoint.toString();
    String retryException = "InvalidRequestException";
    String injectionSourceLocation = String.format("%s:%d",
                  thisJoinPoint.getSourceLocation().getFileName(),
                  thisJoinPoint.getSourceLocation().getLine());

    if (this.wasabiCtx == null) {
      LOG.printMessage(
        WasabiLogger.LOG_LEVEL_WARN, 
        String.format("[Pointcut] [Non-Test-Method] Test ---%s--- | Injection site ---%s--- | Injection location ---%s--- | Retry caller ---%s---\n",
          this.testMethodName, 
          injectionSite, 
          injectionSourceLocation, 
          retryCallerFunction)
      );

      return;
    }

    LOG.printMessage(
      WasabiLogger.LOG_LEVEL_WARN, 
      String.format("[Pointcut] Test ---%s--- | Injection site ---%s--- | Injection location ---%s--- | Retry caller ---%s---\n",
        this.testMethodName, 
        injectionSite, 
        injectionSourceLocation, 
        retryCallerFunction)
    );

    InjectionPoint ipt = this.wasabiCtx.getInjectionPoint(this.testMethodName,
                               injectionSite, 
                               injectionSourceLocation,
                               retryException,
                               retryCallerFunction, 
                               stackSnapshot);
    if (ipt != null && this.wasabiCtx.shouldInject(ipt)) {
      this.activeInjectionLocations.add(retryCallerFunction);
    
      long threadId = Thread.currentThread().getId();
      throw new InvalidRequestException(
        String.format("[wasabi] [thread=%d] [Injection] Test ---%s--- | ---%s--- thrown after calling ---%s--- | Retry location ---%s--- | Retry attempt ---%d---",
          threadId,
          this.testMethodName,
          ipt.retryException,
          ipt.injectionSite,
          ipt.retrySourceLocation,
          ipt.injectionCount)
      );
    }
  }

  /* Inject RequestFailureException */

  pointcut injectRequestFailureException():
    ((withincode(* org.apache.cassandra.service.paxos.Paxos.cas(..)) && call(* org.apache.cassandra.service.paxos.Paxos.*MaybeFailure.markAndThrowAsTimeoutOrFailure(..) throws *Exception*)) ||
        (withincode(* org.apache.cassandra.service.paxos.Paxos.begin(..)) && call(* org.apache.cassandra.service.paxos.Paxos.*MaybeFailure.markAndThrowAsTimeoutOrFailure(..) throws *Exception*))) &&
    !within(edu.uchicago.cs.systems.wasabi.*);

  after() throws RequestFailureException : injectRequestFailureException() {
    StackSnapshot stackSnapshot = new StackSnapshot();
    String retryCallerFunction = stackSnapshot.getSize() > 0 ? stackSnapshot.getFrame(0) : "???";
    String injectionSite = thisJoinPoint.toString();
    String retryException = "RequestFailureException";
    String injectionSourceLocation = String.format("%s:%d",
                  thisJoinPoint.getSourceLocation().getFileName(),
                  thisJoinPoint.getSourceLocation().getLine());

    if (this.wasabiCtx == null) {
      LOG.printMessage(
        WasabiLogger.LOG_LEVEL_WARN, 
        String.format("[Pointcut] [Non-Test-Method] Test ---%s--- | Injection site ---%s--- | Injection location ---%s--- | Retry caller ---%s---\n",
          this.testMethodName, 
          injectionSite, 
          injectionSourceLocation, 
          retryCallerFunction)
      );

      return;
    }

    LOG.printMessage(
      WasabiLogger.LOG_LEVEL_WARN, 
      String.format("[Pointcut] Test ---%s--- | Injection site ---%s--- | Injection location ---%s--- | Retry caller ---%s---\n",
        this.testMethodName, 
        injectionSite, 
        injectionSourceLocation, 
        retryCallerFunction)
    );

    InjectionPoint ipt = this.wasabiCtx.getInjectionPoint(this.testMethodName,
                               injectionSite, 
                               injectionSourceLocation,
                               retryException,
                               retryCallerFunction, 
                               stackSnapshot);
    if (ipt != null && this.wasabiCtx.shouldInject(ipt)) {
      this.activeInjectionLocations.add(retryCallerFunction);
    
      long threadId = Thread.currentThread().getId();
      throw new RequestFailureException(
        String.format("[wasabi] [thread=%d] [Injection] Test ---%s--- | ---%s--- thrown after calling ---%s--- | Retry location ---%s--- | Retry attempt ---%d---",
          threadId,
          this.testMethodName,
          ipt.retryException,
          ipt.injectionSite,
          ipt.retrySourceLocation,
          ipt.injectionCount)
      );
    }
  }

  /* Inject RequestTimeoutException */

  pointcut injectRequestTimeoutException():
    ((withincode(* org.apache.cassandra.service.paxos.Paxos.cas(..)) && call(* org.apache.cassandra.service.paxos.Paxos.*MaybeFailure.markAndThrowAsTimeoutOrFailure(..) throws *Exception*)) ||
        (withincode(* org.apache.cassandra.service.paxos.Paxos.begin(..)) && call(* org.apache.cassandra.service.paxos.Paxos.*MaybeFailure.markAndThrowAsTimeoutOrFailure(..) throws *Exception*))) &&
    !within(edu.uchicago.cs.systems.wasabi.*);

  after() throws RequestTimeoutException : injectRequestTimeoutException() {
    StackSnapshot stackSnapshot = new StackSnapshot();
    String retryCallerFunction = stackSnapshot.getSize() > 0 ? stackSnapshot.getFrame(0) : "???";
    String injectionSite = thisJoinPoint.toString();
    String retryException = "RequestTimeoutException";
    String injectionSourceLocation = String.format("%s:%d",
                  thisJoinPoint.getSourceLocation().getFileName(),
                  thisJoinPoint.getSourceLocation().getLine());

    if (this.wasabiCtx == null) {
      LOG.printMessage(
        WasabiLogger.LOG_LEVEL_WARN, 
        String.format("[Pointcut] [Non-Test-Method] Test ---%s--- | Injection site ---%s--- | Injection location ---%s--- | Retry caller ---%s---\n",
          this.testMethodName, 
          injectionSite, 
          injectionSourceLocation, 
          retryCallerFunction)
      );

      return;
    }

    LOG.printMessage(
      WasabiLogger.LOG_LEVEL_WARN, 
      String.format("[Pointcut] Test ---%s--- | Injection site ---%s--- | Injection location ---%s--- | Retry caller ---%s---\n",
        this.testMethodName, 
        injectionSite, 
        injectionSourceLocation, 
        retryCallerFunction)
    );

    InjectionPoint ipt = this.wasabiCtx.getInjectionPoint(this.testMethodName,
                               injectionSite, 
                               injectionSourceLocation,
                               retryException,
                               retryCallerFunction, 
                               stackSnapshot);
    if (ipt != null && this.wasabiCtx.shouldInject(ipt)) {
      this.activeInjectionLocations.add(retryCallerFunction);
    
      long threadId = Thread.currentThread().getId();
      throw new RequestTimeoutException(
        String.format("[wasabi] [thread=%d] [Injection] Test ---%s--- | ---%s--- thrown after calling ---%s--- | Retry location ---%s--- | Retry attempt ---%d---",
          threadId,
          this.testMethodName,
          ipt.retryException,
          ipt.injectionSite,
          ipt.retrySourceLocation,
          ipt.injectionCount)
      );
    }
  }

  /* Inject UnavailableException */

  pointcut injectUnavailableException():
    ((withincode(* org.apache.cassandra.service.paxos.Paxos.begin(..)) && call(* org.apache.cassandra.service.paxos.Paxos.*Participants.assureSufficientLiveNodes(..) throws *Exception*)) ||
        (withincode(* org.apache.cassandra.service.paxos.Paxos.begin(..)) && call(* org.apache.cassandra.service.paxos.PaxosPrepare.prepare(..) throws *Exception*))) &&
    !within(edu.uchicago.cs.systems.wasabi.*);

  after() throws UnavailableException : injectUnavailableException() {
    StackSnapshot stackSnapshot = new StackSnapshot();
    String retryCallerFunction = stackSnapshot.getSize() > 0 ? stackSnapshot.getFrame(0) : "???";
    String injectionSite = thisJoinPoint.toString();
    String retryException = "UnavailableException";
    String injectionSourceLocation = String.format("%s:%d",
                  thisJoinPoint.getSourceLocation().getFileName(),
                  thisJoinPoint.getSourceLocation().getLine());

    if (this.wasabiCtx == null) {
      LOG.printMessage(
        WasabiLogger.LOG_LEVEL_WARN, 
        String.format("[Pointcut] [Non-Test-Method] Test ---%s--- | Injection site ---%s--- | Injection location ---%s--- | Retry caller ---%s---\n",
          this.testMethodName, 
          injectionSite, 
          injectionSourceLocation, 
          retryCallerFunction)
      );

      return;
    }

    LOG.printMessage(
      WasabiLogger.LOG_LEVEL_WARN, 
      String.format("[Pointcut] Test ---%s--- | Injection site ---%s--- | Injection location ---%s--- | Retry caller ---%s---\n",
        this.testMethodName, 
        injectionSite, 
        injectionSourceLocation, 
        retryCallerFunction)
    );

    InjectionPoint ipt = this.wasabiCtx.getInjectionPoint(this.testMethodName,
                               injectionSite, 
                               injectionSourceLocation,
                               retryException,
                               retryCallerFunction, 
                               stackSnapshot);
    if (ipt != null && this.wasabiCtx.shouldInject(ipt)) {
      this.activeInjectionLocations.add(retryCallerFunction);
    
      long threadId = Thread.currentThread().getId();
      throw new UnavailableException(
        String.format("[wasabi] [thread=%d] [Injection] Test ---%s--- | ---%s--- thrown after calling ---%s--- | Retry location ---%s--- | Retry attempt ---%d---",
          threadId,
          this.testMethodName,
          ipt.retryException,
          ipt.injectionSite,
          ipt.retrySourceLocation,
          ipt.injectionCount)
      );
    }
  }

  /* Inject IllegalArgumentException */

  pointcut injectIllegalArgumentException():
    ((withincode(* org.apache.cassandra.service.paxos.Paxos.begin(..)) && 
    call(* org.apache.cassandra.service.reads.ResponseResolver.preprocess(..) throws *Exception*))) &&
    !within(edu.uchicago.cs.systems.wasabi.*);

  after() throws IllegalArgumentException : injectIllegalArgumentException() {
    StackSnapshot stackSnapshot = new StackSnapshot();
    String retryCallerFunction = stackSnapshot.getSize() > 0 ? stackSnapshot.getFrame(0) : "???";
    String injectionSite = thisJoinPoint.toString();
    String retryException = "IllegalArgumentException";
    String injectionSourceLocation = String.format("%s:%d",
                  thisJoinPoint.getSourceLocation().getFileName(),
                  thisJoinPoint.getSourceLocation().getLine());

    if (this.wasabiCtx == null) {
      LOG.printMessage(
        WasabiLogger.LOG_LEVEL_WARN, 
        String.format("[Pointcut] [Non-Test-Method] Test ---%s--- | Injection site ---%s--- | Injection location ---%s--- | Retry caller ---%s---\n",
          this.testMethodName, 
          injectionSite, 
          injectionSourceLocation, 
          retryCallerFunction)
      );

      return;
    }

    LOG.printMessage(
      WasabiLogger.LOG_LEVEL_WARN, 
      String.format("[Pointcut] Test ---%s--- | Injection site ---%s--- | Injection location ---%s--- | Retry caller ---%s---\n",
        this.testMethodName, 
        injectionSite, 
        injectionSourceLocation, 
        retryCallerFunction)
    );

    InjectionPoint ipt = this.wasabiCtx.getInjectionPoint(this.testMethodName,
                               injectionSite, 
                               injectionSourceLocation,
                               retryException,
                               retryCallerFunction, 
                               stackSnapshot);
    if (ipt != null && this.wasabiCtx.shouldInject(ipt)) {
      this.activeInjectionLocations.add(retryCallerFunction);
    
      long threadId = Thread.currentThread().getId();
      throw new IllegalArgumentException(
        String.format("[wasabi] [thread=%d] [Injection] Test ---%s--- | ---%s--- thrown after calling ---%s--- | Retry location ---%s--- | Retry attempt ---%d---",
          threadId,
          this.testMethodName,
          ipt.retryException,
          ipt.injectionSite,
          ipt.retrySourceLocation,
          ipt.injectionCount)
      );
    }
  }

  /* Inject IllegalStateException */

  pointcut injectIllegalStateException():
    ((withincode(* org.apache.cassandra.service.paxos.Paxos.begin(..)) && 
    call(* org.apache.cassandra.service.reads.ResponseResolver.preprocess(..) throws *Exception*))) &&
    !within(edu.uchicago.cs.systems.wasabi.*);

  after() throws IllegalStateException : injectIllegalStateException() {
    StackSnapshot stackSnapshot = new StackSnapshot();
    String retryCallerFunction = stackSnapshot.getSize() > 0 ? stackSnapshot.getFrame(0) : "???";
    String injectionSite = thisJoinPoint.toString();
    String retryException = "IllegalStateException";
    String injectionSourceLocation = String.format("%s:%d",
                  thisJoinPoint.getSourceLocation().getFileName(),
                  thisJoinPoint.getSourceLocation().getLine());

    if (this.wasabiCtx == null) {
      LOG.printMessage(
        WasabiLogger.LOG_LEVEL_WARN, 
        String.format("[Pointcut] [Non-Test-Method] Test ---%s--- | Injection site ---%s--- | Injection location ---%s--- | Retry caller ---%s---\n",
          this.testMethodName, 
          injectionSite, 
          injectionSourceLocation, 
          retryCallerFunction)
      );

      return;
    }

    LOG.printMessage(
      WasabiLogger.LOG_LEVEL_WARN, 
      String.format("[Pointcut] Test ---%s--- | Injection site ---%s--- | Injection location ---%s--- | Retry caller ---%s---\n",
        this.testMethodName, 
        injectionSite, 
        injectionSourceLocation, 
        retryCallerFunction)
    );

    InjectionPoint ipt = this.wasabiCtx.getInjectionPoint(this.testMethodName,
                               injectionSite, 
                               injectionSourceLocation,
                               retryException,
                               retryCallerFunction, 
                               stackSnapshot);
    if (ipt != null && this.wasabiCtx.shouldInject(ipt)) {
      this.activeInjectionLocations.add(retryCallerFunction);
    
      long threadId = Thread.currentThread().getId();
      throw new IllegalStateException(
        String.format("[wasabi] [thread=%d] [Injection] Test ---%s--- | ---%s--- thrown after calling ---%s--- | Retry location ---%s--- | Retry attempt ---%d---",
          threadId,
          this.testMethodName,
          ipt.retryException,
          ipt.injectionSite,
          ipt.retrySourceLocation,
          ipt.injectionCount)
      );
    }
  }

  /* Inject SSTableAcquisitionException */

  pointcut injectSSTableAcquisitionException():
    ((withincode(* PendingAntiCompaction.AcquisitionCallable.call(..)) && 
    call(* PendingAntiCompaction.AcquisitionCallable.acquireSSTables(..) throws *Exception*))) &&
    !within(edu.uchicago.cs.systems.wasabi.*);

  after() throws SSTableAcquisitionException : injectSSTableAcquisitionException() {
    StackSnapshot stackSnapshot = new StackSnapshot();
    String retryCallerFunction = stackSnapshot.getSize() > 0 ? stackSnapshot.getFrame(0) : "???";
    String injectionSite = thisJoinPoint.toString();
    String retryException = "SSTableAcquisitionException";
    String injectionSourceLocation = String.format("%s:%d",
                  thisJoinPoint.getSourceLocation().getFileName(),
                  thisJoinPoint.getSourceLocation().getLine());

    if (this.wasabiCtx == null) {
      LOG.printMessage(
        WasabiLogger.LOG_LEVEL_WARN, 
        String.format("[Pointcut] [Non-Test-Method] Test ---%s--- | Injection site ---%s--- | Injection location ---%s--- | Retry caller ---%s---\n",
          this.testMethodName, 
          injectionSite, 
          injectionSourceLocation, 
          retryCallerFunction)
      );

      return;
    }

    LOG.printMessage(
      WasabiLogger.LOG_LEVEL_WARN, 
      String.format("[Pointcut] Test ---%s--- | Injection site ---%s--- | Injection location ---%s--- | Retry caller ---%s---\n",
        this.testMethodName, 
        injectionSite, 
        injectionSourceLocation, 
        retryCallerFunction)
    );

    InjectionPoint ipt = this.wasabiCtx.getInjectionPoint(this.testMethodName,
                               injectionSite, 
                               injectionSourceLocation,
                               retryException,
                               retryCallerFunction, 
                               stackSnapshot);
    if (ipt != null && this.wasabiCtx.shouldInject(ipt)) {
      this.activeInjectionLocations.add(retryCallerFunction);
    
      long threadId = Thread.currentThread().getId();
      throw new SSTableAcquisitionException(
        String.format("[wasabi] [thread=%d] [Injection] Test ---%s--- | ---%s--- thrown after calling ---%s--- | Retry location ---%s--- | Retry attempt ---%d---",
          threadId,
          this.testMethodName,
          ipt.retryException,
          ipt.injectionSite,
          ipt.retrySourceLocation,
          ipt.injectionCount)
      );
    }
  }

}