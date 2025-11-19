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

import edu.uchicago.cs.systems.wasabi.ConfigParser;
import edu.uchicago.cs.systems.wasabi.WasabiLogger;
import edu.uchicago.cs.systems.wasabi.WasabiContext;
import edu.uchicago.cs.systems.wasabi.InjectionPolicy;
import edu.uchicago.cs.systems.wasabi.StackSnapshot;
import edu.uchicago.cs.systems.wasabi.InjectionPoint;
import edu.uchicago.cs.systems.wasabi.ExecutionTrace;

public aspect InterceptHive {
  private WasabiContext wasabiCtx = null;

  private static final String UNKNOWN = "UNKNOWN";

  private static final WasabiLogger LOG = new WasabiLogger();
  private static final String configFile = (System.getProperty("configFile") != null) ? System.getProperty("configFile") : "default.conf";
  private static final ConfigParser configParser = new ConfigParser(LOG, configFile);

  private Set<String> activeInjectionLocations = ConcurrentHashMap.newKeySet(); 
  private String testMethodName = UNKNOWN;

  pointcut testMethod():
    @annotation(org.junit.Test) && 
     // @annotation(org.junit.Before) ||
     // @annotation(org.junit.After) || 
     // @annotation(org.junit.BeforeClass) ||
     // @annotation(org.junit.AfterClass) || 
     // @annotation(org.junit.jupiter.api.BeforeEach) ||
     // @annotation(org.junit.jupiter.api.AfterEach) || 
     // @annotation(org.junit.jupiter.api.BeforeAll) ||
     // @annotation(org.junit.jupiter.api.AfterAll) || 
     // @annotation(org.junit.jupiter.api.Test)) &&
     !within(org.apache.hadoop.*.TestDFSClientFailover.*) &&
     !within(org.apache.hadoop.hdfs.*.TestOfflineImageViewer.*) &&
     !within(org.apache.hadoop.example.ITUseHadoopCodec.*) &&
     !within(org.apache.hive.hcatalog.mapreduce.TestHCatMultiOutputFormat.test.*);


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
    ((withincode(* org.apache.hadoop.hive.ql.parse.repl.CopyUtils.doCopyRetry(..)) &&
    call(* org.apache.hadoop.hive.ql.parse.repl.CopyUtils.getFilesToRetry(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hive.ql.parse.repl.CopyUtils.doCopyRetry(..)) &&
    call(* org.apache.hadoop.hive.ql.parse.repl.CopyUtils.doCopyOnce(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hive.druid.DruidStorageHandlerUtils.publishSegmentWithShardSpec(..)) &&
    call(* org.apache.hadoop.fs.FileSystem.mkdirs(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hive.druid.DruidStorageHandlerUtils.publishSegmentWithShardSpec(..)) &&
    call(* org.apache.hadoop.fs.FileSystem.rename(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hive.metastore.HiveMetaStoreClient.open(..)) &&
    call(* org.apache.hadoop.hive.metastore.utils.SecurityUtils.getUGI(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hive.ql.hooks.HiveProtoLoggingHook.*EventLogger.writeEvent(..)) &&
    call(* org.apache.hadoop.hive.ql.hooks.HiveProtoLoggingHook.*EventLogger.maybeRolloverWriterForDay(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hive.ql.hooks.HiveProtoLoggingHook.*EventLogger.writeEvent(..)) &&
    call(* org.apache.tez.dag.history.logging.proto.ProtoMessageWriter.*.writeProto(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hive.ql.hooks.HiveProtoLoggingHook.*EventLogger.writeEvent(..)) &&
    call(* org.apache.tez.dag.history.logging.proto.ProtoMessageWriter.*.hflush(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hive.metastore.ObjectStore.*RetryingExecutor.run(..)) &&
    call(* org.apache.hadoop.hive.metastore.ObjectStore.*RetryingExecutor.*Command.process(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hive.ql.exec.util.Retryable.executeCallable(..)) &&
    call(* org.apache.hadoop.security.UserGroupInformation.doAs(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hive.ql.exec.util.Retryable.executeCallable(..)) &&
    call(* org.apache.hadoop.security.UserGroupInformation.getLoginUser(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hive.ql.exec.repl.atlas.RetryingClientTimeBased.invokeWithRetry(..)) &&
    call(* java.util.concurrent.Callable.*.call(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hive.registry.impl.ZkRegistryBase.ensureInstancesCache(..)) &&
    call(* org.apache.curator.framework.recipes.cache.PathChildrenCache.start(..) throws *Exception*)) ||
    (withincode(* org.apache.hive.common.util.RetryUtilities.*ExponentiallyDecayingBatchWork.run(..)) &&
    call(* org.apache.hive.common.util.RetryUtilities.*ExponentialBackOffRetry.*.execute(..) throws *Exception*)) ||
    (withincode(* org.apache.hive.common.util.Retry.*RetryingStatement.evaluate(..)) &&
    call(* org.junit.runners.model.Statement.evaluate(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hive.druid.DruidStorageHandlerUtils.publishSegmentWithShardSpec(..)) &&
    call(* org.apache.hadoop.fs.FileSystem.exists(..) throws *Exception*)) ||
    (withincode(* org.apache.hive.hcatalog.templeton.LauncherDelegator.killTempletonJobWithRetry(..)) &&
    call(* org.apache.hive.hcatalog.templeton.LauncherDelegator.killJob(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hive.kafka.RetryUtils.retry(..)) &&
    call(* org.apache.hadoop.hive.kafka.RetryUtils.*Task.*.perform(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hive.llap.AsyncPbRpcProxy.*AsyncCallableRequest.call(..)) &&
    call(* org.apache.hadoop.hive.llap.AsyncPbRpcProxy.*AsyncCallableRequest.callInternal(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hive.ql.exec.tez.monitoring.TezJobMonitor.monitorExecution(..)) &&
    call(* org.apache.tez.dag.api.client.DAGClient.getDAGStatus(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hive.ql.hooks.HiveProtoLoggingHook.*EventLogger.writeEvent(..)) &&
    call(* org.apache.tez.dag.history.logging.proto.DatePartitionedLogger.*.getWriter(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hive.metastore.RetryingMetaStoreClient.invoke(..)) &&
    call(* org.apache.hadoop.security.UserGroupInformation.doAs(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hive.metastore.grpc.HiveMetastore.*CompactionInfoStruct.CompactionInfoStruct(..)) &&
    call(* com.google.protobuf.CodedInputStream.readBool(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hive.metastore.grpc.HiveMetastore.*CompactionInfoStruct.CompactionInfoStruct(..)) &&
    call(* com.google.protobuf.CodedInputStream.readEnum(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hive.metastore.grpc.HiveMetastore.*CompactionInfoStruct.CompactionInfoStruct(..)) &&
    call(* com.google.protobuf.CodedInputStream.readInt64(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hive.metastore.grpc.HiveMetastore.*CompactionInfoStruct.CompactionInfoStruct(..)) &&
    call(* com.google.protobuf.CodedInputStream.readStringRequireUtf8(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hive.metastore.grpc.HiveMetastore.*CompactionInfoStruct.CompactionInfoStruct(..)) &&
    call(* com.google.protobuf.CodedInputStream.readTag(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hive.metastore.grpc.HiveMetastore.*CompactionInfoStruct.CompactionInfoStruct(..)) &&
    call(* com.google.protobuf.GeneratedMessageV3.parseUnknownField(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hive.metastore.utils.MetaStoreServerUtils.loopUntilHMSReady(..)) &&
    call(* java.net.Socket.close(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hive.metastore.utils.MetaStoreServerUtils.loopUntilHMSReady(..)) &&
    call(* java.net.Socket.connect(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hive.metastore.utils.RetryUtilities.run(..)) &&
    call(* org.*.execute(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hive.metastore.HiveMetaStoreClientPreCatalog.open(..)) &&
    call(* org.apache.hadoop.hive.metastore.conf.MetastoreConf.getPassword(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hive.metastore.HiveMetaStoreClientPreCatalog.open(..)) &&
    call(* org.apache.hadoop.hive.metastore.security.HadoopThriftAuthBridge.*Client.createClientTransport(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hive.metastore.HiveMetaStoreClientPreCatalog.open(..)) &&
    call(* org.apache.hadoop.hive.metastore.utils.SecurityUtils.getTokenStrForm(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hive.metastore.HiveMetaStoreClientPreCatalog.open(..)) &&
    call(* org.apache.hadoop.hive.metastore.utils.SecurityUtils.getUGI(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hive.ql.exec.tez.YarnQueueHelper.checkQueueAccessInternal(..)) &&
    call(* checkQueueAccessFromSingleRm(..) throws *Exception*)) ||
    (withincode(* *checkJobTracker(..)) &&
    call(* *openStream(..) throws *Exception*)) ||
    (withincode(* *close*(..)) &&
    call(* *read(..) throws *Exception*)) ||
    (withincode(* *checkJobTracker(..)) &&
    call(* *read(..) throws *Exception*))) && 
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


  /* Inject SQLException */

  pointcut injectSQLException():
    ((withincode(* org.apache.hive.jdbc.HiveConnection.HiveConnection(..)) &&
    call(* org.apache.hive.jdbc.HiveConnection.executeInitSql(..) throws *Exception*)) ||
    (withincode(* org.apache.hive.jdbc.HiveConnection.HiveConnection(..)) &&
    call(* org.apache.hive.jdbc.HiveConnection.openSession(..) throws *Exception*)) ||
    (withincode(* org.apache.hive.jdbc.HiveConnection.HiveConnection(..)) &&
    call(* org.apache.hive.jdbc.HiveConnection.openTransport(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hive.ql.exec.Utilities.executeWithRetry(..)) &&
    call(* org.apache.hadoop.hive.ql.exec.Utilities.*SQLCommand.*.run(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hive.ql.exec.Utilities.connectWithRetry(..)) &&
    call(* java.sql.DriverManager.getConnection(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hive.ql.exec.Utilities.prepareWithRetry(..)) &&
    call(* java.sql.Connection.prepareStatement(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hive.metastore.txn.CompactionTxnHandler.findReadyToClean(..)) &&
    call(* java.sql.ResultSet.getInt(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hive.metastore.txn.CompactionTxnHandler.findReadyToClean(..)) &&
    call(* java.sql.ResultSet.getLong(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hive.metastore.txn.CompactionTxnHandler.findReadyToClean(..)) &&
    call(* java.sql.ResultSet.getString(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hive.metastore.txn.CompactionTxnHandler.findReadyToClean(..)) &&
    call(* java.sql.ResultSet.next(..) throws *Exception*))) &&
    !within(edu.uchicago.cs.systems.wasabi.*);

  after() throws SQLException : injectSQLException() {
    StackSnapshot stackSnapshot = new StackSnapshot();
    String retryCallerFunction = stackSnapshot.getSize() > 0 ? stackSnapshot.getFrame(0) : "???";
    String injectionSite = thisJoinPoint.toString();
    String retryException = "SQLException";
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
      throw new SQLException(
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