package edu.uchicago.cs.systems.wasabi;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.net.SocketException;

import java.util.concurrent.ConcurrentHashMap;
import java.util.Set;

import edu.uchicago.cs.systems.wasabi.ConfigParser;
import edu.uchicago.cs.systems.wasabi.WasabiLogger;
import edu.uchicago.cs.systems.wasabi.WasabiContext;
import edu.uchicago.cs.systems.wasabi.InjectionPolicy;
import edu.uchicago.cs.systems.wasabi.StackSnapshot;
import edu.uchicago.cs.systems.wasabi.InjectionPoint;
import edu.uchicago.cs.systems.wasabi.ExecutionTrace;

public aspect InterceptElasticSearch {
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
    ((withincode(* org.elasticsearch.indices.IndicesService.processPendingDeletes(..)) && call(* org.elasticsearch.env.NodeEnvironment.deleteIndexDirectoryUnderLock(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.indices.IndicesService.processPendingDeletes(..)) && call(* org.elasticsearch.indices.IndicesService.deleteShardStore(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.xpack.watcher.notification.email.attachment.ReportingAttachmentParser.toAttachment(..)) && call(* org.elasticsearch.xpack.watcher.common.http.HttpClient.execute(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.index.IndexService.onShardClose(..)) && call(* beforeIndexShardDeleted(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.gateway.PersistedClusterStateService.completeCommit(..)) && call(* org.elasticsearch.gateway.PersistedClusterStateService.commit(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.indices.IndicesService.processPendingDeletes(..)) && call(* org.elasticsearch.env.NodeEnvironment.deleteIndexDirectoryUnderLock(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.indices.IndicesService.processPendingDeletes(..)) && call(* org.elasticsearch.indices.IndicesService.deleteShardStore(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.common.blobstore.fs.FsBlobContainer.moveBlobAtomic(..)) && call(* java.nio.file.Files.move(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.common.file.AbstractFileWatchingService.enableDirectoryWatcher(..)) && call(* org.elasticsearch.monitor.fs.FsInfo.Path.register(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.repositories.gcs.GoogleCloudStorageBlobStore.writeBlobResumable(..)) && call(* org.elasticsearch.core.internal.io.Streams.copy(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.repositories.gcs.GoogleCloudStorageBlobStore.writeBlobResumable(..)) && call(* org.elasticsearch.repositories.gcs.SocketAccess.doPrivilegedIOException(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.action.bulk.BulkRequestParser.parse(..)) && call(* org.elasticsearch.action.update.UpdateRequest.fromXContent(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.action.bulk.BulkRequestParser.parse(..)) && call(* org.elasticsearch.common.xcontent.XContentParser.booleanValue(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.action.bulk.BulkRequestParser.parse(..)) && call(* org.elasticsearch.common.xcontent.XContentParser.longValue(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.action.bulk.BulkRequestParser.parse(..)) && call(* org.elasticsearch.common.xcontent.XContentParser.intValue(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.action.bulk.BulkRequestParser.parse(..)) && call(* org.elasticsearch.common.xcontent.XContentParser.text(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.action.bulk.BulkRequestParser.parse(..)) && call(* org.elasticsearch.common.xcontent.XContentParser.currentName(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.action.bulk.BulkRequestParser.parse(..)) && call(* org.elasticsearch.common.xcontent.XContentParser.nextToken(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.action.bulk.BulkRequestParser.parse(..)) && call(* org.elasticsearch.search.fetch.subphase.FetchSourceContext.fromXContent(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.action.bulk.BulkRequestParser.parse(..)) && call(* org.elasticsearch.action.bulk.BulkRequestParser.createParser(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.action.bulk.BulkRequestParser.parse(..)) && call(* org.elasticsearch.common.xcontent.XContentParser.booleanValue(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.action.bulk.BulkRequestParser.parse(..)) && call(* org.elasticsearch.common.xcontent.XContentParser.longValue(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.action.bulk.BulkRequestParser.parse(..)) && call(* org.elasticsearch.common.xcontent.XContentParser.intValue(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.action.bulk.BulkRequestParser.parse(..)) && call(* org.elasticsearch.common.xcontent.XContentParser.text(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.action.bulk.BulkRequestParser.parse(..)) && call(* org.elasticsearch.common.xcontent.XContentParser.currentName(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.action.bulk.BulkRequestParser.parse(..)) && call(* org.elasticsearch.common.xcontent.XContentParser.nextToken(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.action.bulk.BulkRequestParser.parse(..)) && call(* org.elasticsearch.search.fetch.subphase.FetchSourceContext.fromXContent(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.index.reindex.BulkByScrollTask.*Status.innerFromXContent(..)) && call(* org.elasticsearch.common.xcontent.XContentParser.floatValue(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.index.reindex.BulkByScrollTask.*Status.innerFromXContent(..)) && call(* org.elasticsearch.common.xcontent.XContentParser.longValue(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.index.reindex.BulkByScrollTask.*Status.innerFromXContent(..)) && call(* org.elasticsearch.common.xcontent.XContentParser.intValue(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.index.reindex.BulkByScrollTask.*Status.innerFromXContent(..)) && call(* org.elasticsearch.common.xcontent.XContentParser.text(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.index.reindex.BulkByScrollTask.*Status.innerFromXContent(..)) && call(* org.elasticsearch.common.xcontent.XContentParser.currentName(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.index.reindex.BulkByScrollTask.*Status.innerFromXContent(..)) && call(* org.elasticsearch.common.xcontent.XContentParser.skipChildren(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.index.reindex.BulkByScrollTask.*Status.innerFromXContent(..)) && call(* org.elasticsearch.common.xcontent.XContentParser.nextToken(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.index.reindex.BulkByScrollTask.*Status.innerFromXContent(..)) && call(* org.elasticsearch.index.reindex.BulkByScrollTask.*StatusOrException.fromXContent(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.index.reindex.BulkByScrollTask.*Status.innerFromXContent(..)) && call(* org.elasticsearch.common.xcontent.ConstructingObjectParser.*.parse(..) throws *Exception*))) &&
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

  /* Inject SocketException */

  pointcut injectSocketException():
    ((withincode(* org.elasticsearch.cluster.coordination.ClusterBootstrapService.doBootstrap(..)) && call(* java.util.function.Consumer.accept(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.xpack.core.security.CommandLineHttpClient.checkClusterHealthWithRetriesWaitingForCluster(..)) && call(* org.elasticsearch.xpack.core.security.CommandLineHttpClient.execute(..) throws *Exception*))) &&
    !within(edu.uchicago.cs.systems.wasabi.*);

  after() throws Exception : injectSocketException() {
    StackSnapshot stackSnapshot = new StackSnapshot();
    String retryCallerFunction = stackSnapshot.getSize() > 0 ? stackSnapshot.getFrame(0) : "???";
    String injectionSite = thisJoinPoint.toString();
    String retryException = "SocketExceptionException";
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
      throw new SocketException(
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
    ((withincode(* org.elasticsearch.action.bulk.BulkRequestParser.parse(..)) && call(* org.elasticsearch.action.delete.DeleteRequest.setIfPrimaryTerm(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.action.bulk.BulkRequestParser.parse(..)) && call(* org.elasticsearch.action.delete.DeleteRequest.setIfSeqNo(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.action.bulk.BulkRequestParser.parse(..)) && call(* org.elasticsearch.action.index.IndexRequest.setIfPrimaryTerm(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.action.bulk.BulkRequestParser.parse(..)) && call(* org.elasticsearch.action.index.IndexRequest.setIfSeqNo(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.action.bulk.BulkRequestParser.parse(..)) && call(* org.elasticsearch.action.update.UpdateRequest.setIfPrimaryTerm(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.action.bulk.BulkRequestParser.parse(..)) && call(* org.elasticsearch.action.update.UpdateRequest.setIfSeqNo(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.action.bulk.BulkRequestParser.parse(..)) && call(* org.elasticsearch.index.VersionType.fromString(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.action.bulk.BulkRequestParser.parse(..)) && call(* org.elasticsearch.action.bulk.BulkRequestParser.findNextMarker(..) throws *Exception*)) ||
        (withincode(* org.elasticsearch.action.bulk.BulkRequestParser.parse(..)) && call(* org.elasticsearch.index.VersionType.fromString(..) throws *Exception*))) &&
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

}