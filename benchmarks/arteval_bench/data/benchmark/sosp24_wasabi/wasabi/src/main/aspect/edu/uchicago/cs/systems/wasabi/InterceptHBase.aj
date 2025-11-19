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

import org.apache.zookeeper.KeeperException;
import org.apache.hadoop.hbase.replication.ReplicationException;

import edu.uchicago.cs.systems.wasabi.ConfigParser;
import edu.uchicago.cs.systems.wasabi.WasabiLogger;
import edu.uchicago.cs.systems.wasabi.WasabiContext;
import edu.uchicago.cs.systems.wasabi.InjectionPolicy;
import edu.uchicago.cs.systems.wasabi.StackSnapshot;
import edu.uchicago.cs.systems.wasabi.InjectionPoint;
import edu.uchicago.cs.systems.wasabi.ExecutionTrace;

public aspect InterceptHBase {
  private WasabiContext wasabiCtx = null;

  private static final String UNKNOWN = "UNKNOWN";

  private static final WasabiLogger LOG = new WasabiLogger();
  private static final String configFile = (System.getProperty("configFile") != null) ? System.getProperty("configFile") : "default.conf";
  private static final ConfigParser configParser = new ConfigParser(LOG, configFile);

  private Set<String> activeInjectionLocations = ConcurrentHashMap.newKeySet(); 
  private String testMethodName = UNKNOWN;

  pointcut testMethod():
    (@annotation(org.junit.Test) || 
     // @annotation(org.junit.Before) ||
     // @annotation(org.junit.After) || 
     // @annotation(org.junit.BeforeClass) ||
     // @annotation(org.junit.AfterClass) || 
     // @annotation(org.junit.jupiter.api.BeforeEach) ||
     // @annotation(org.junit.jupiter.api.AfterEach) || 
     // @annotation(org.junit.jupiter.api.BeforeAll) ||
     // @annotation(org.junit.jupiter.api.AfterAll) || 
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
    ((withincode(* org.apache.hadoop.hbase.regionserver.wal.AbstractFSWAL.archive(..)) &&
    call(* org.apache.hadoop.hbase.regionserver.wal.AbstractFSWAL.archiveLogFile(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.wal.AbstractWALRoller.run(..)) &&
    call(* org.apache.hadoop.hbase.wal.AbstractWALRoller.*RollController.rollWal(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.wal.AbstractWALRoller.run(..)) &&
    call(* org.apache.hadoop.hbase.wal.AbstractWALRoller.*RollController.rollWal(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.wal.AbstractWALRoller.run(..)) &&
    call(* org.apache.hadoop.hbase.wal.AbstractWALRoller.*RollController.rollWal(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.ipc.BlockingRpcConnection.setupIOstreams(..)) &&
    call(* org.apache.hadoop.net.NetUtils.getInputStream(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.ipc.BlockingRpcConnection.setupIOstreams(..)) &&
    call(* org.apache.hadoop.net.NetUtils.getOutputStream(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.ipc.BlockingRpcConnection.setupIOstreams(..)) &&
    call(* org.apache.hadoop.security.UserGroupInformation.doAs(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.ipc.BlockingRpcConnection.setupIOstreams(..)) &&
    call(* org.apache.hadoop.hbase.security.HBaseSaslRpcClient.getInputStream(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.ipc.BlockingRpcConnection.setupIOstreams(..)) &&
    call(* org.apache.hadoop.hbase.security.HBaseSaslRpcClient.getOutputStream(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.regionserver.BootstrapNodeManager.getFromMaster(..)) &&
    call(* org.apache.hadoop.hbase.util.FutureUtils.get(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.tool.BulkLoadHFilesTool.performBulkLoad(..)) &&
    call(* org.apache.hadoop.hbase.util.FutureUtils.get(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.tool.BulkLoadHFilesTool.performBulkLoad(..)) &&
    call(* org.apache.hadoop.hbase.tool.BulkLoadHFilesTool.groupOrSplitPhase(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.tool.BulkLoadHFilesTool.performBulkLoad(..)) &&
    call(* org.apache.hadoop.hbase.tool.BulkLoadHFilesTool.bulkLoadPhase(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.regionserver.wal.DualAsyncFSWAL.createWriterInstance(..)) &&
    call(* org.apache.hadoop.hbase.regionserver.wal.AsyncFSWAL.createAsyncWriter(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.io.asyncfs.FanOutOneBlockAsyncDFSOutputHelper.createOutput(..)) &&
    call(* org.apache.hadoop.hdfs.protocol.ClientProtocol.addBlock(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.io.asyncfs.FanOutOneBlockAsyncDFSOutputHelper.completeFile(..)) &&
    call(* org.apache.hadoop.hdfs.protocol.ClientProtocol.complete(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.regionserver.snapshot.FlushSnapshotSubprocedure.*RegionSnapshotTask.call(..)) &&
    call(* org.apache.hadoop.hbase.regionserver.HRegion.flush(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.util.FSTableDescriptors.writeTableDescriptor(..)) &&
    call(* org.apache.hadoop.fs.FileSystem.create(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.util.FSTableDescriptors.writeTableDescriptor(..)) &&
    call(* java.io.FilterOutputStream.write(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.util.FSTableDescriptors.writeTableDescriptor(..)) &&
    call(* org.apache.hadoop.hbase.util.FSTableDescriptors.deleteTableDescriptorFiles(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.util.FSUtils.setVersion(..)) &&
    call(* org.apache.hadoop.fs.FileSystem.create(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.util.FSUtils.setVersion(..)) &&
    call(* java.io.FilterOutputStream.write(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.util.FSUtils.setVersion(..)) &&
    call(* org.apache.hadoop.fs.FSDataOutputStream.close(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.util.FSUtils.setVersion(..)) &&
    call(* org.apache.hadoop.fs.FileSystem.rename(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.util.FSUtils.checkClusterIdExists(..)) &&
    call(* org.apache.hadoop.fs.FileSystem.exists(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.util.FSUtils.setClusterId(..)) &&
    call(* org.apache.hadoop.fs.FileSystem.create(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.util.FSUtils.setClusterId(..)) &&
    call(* java.io.FilterOutputStream.write(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.util.FSUtils.setClusterId(..)) &&
    call(* org.apache.hadoop.fs.FileSystem.rename(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.util.HBaseFsck.*FileLockCallable.createFileWithRetries(..)) &&
    call(* org.apache.hadoop.hbase.util.CommonFSUtils.create(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.util.HBaseFsck.unlockHbck(..)) &&
    call(* org.apache.hadoop.hbase.util.CommonFSUtils.delete(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.util.HBaseFsck.unlockHbck(..)) &&
    call(* org.apache.hadoop.hbase.util.CommonFSUtils.getCurrentFileSystem(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.replication.regionserver.HBaseInterClusterReplicationEndpoint.replicate(..)) &&
    call(* org.apache.hadoop.hbase.replication.regionserver.HBaseInterClusterReplicationEndpoint.parallelReplicate(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.backup.HFileArchiver.resolveAndArchiveFile(..)) &&
    call(* org.apache.hadoop.fs.FileSystem.exists(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.backup.HFileArchiver.resolveAndArchiveFile(..)) &&
    call(* org.apache.hadoop.hbase.backup.HFileArchiver.*File.moveAndClose(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.replication.regionserver.HFileReplicator.doBulkLoad(..)) &&
    call(* org.apache.hadoop.hbase.tool.BulkLoadHFilesTool.loadHFileQueue(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.regionserver.HRegionFileSystem.createDir(..)) &&
    call(* org.apache.hadoop.hbase.regionserver.HRegionFileSystem.mkdirs(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.regionserver.HRegionFileSystem.rename(..)) &&
    call(* org.apache.hadoop.fs.FileSystem.rename(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.regionserver.HRegionFileSystem.deleteDir(..)) &&
    call(* org.apache.hadoop.fs.FileSystem.delete(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.regionserver.HRegionFileSystem.createDirOnFileSystem(..)) &&
    call(* org.apache.hadoop.fs.FileSystem.mkdirs(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.regionserver.HRegionServer.createRegionServerStatusStub(..)) &&
    call(* org.apache.hadoop.hbase.security.UserProvider.getCurrent(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.regionserver.HStore.flushCache(..)) &&
    call(* org.apache.hadoop.hbase.regionserver.StoreFlusher.flushSnapshot(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.util.MoveWithAck.call(..)) &&
    call(* org.apache.hadoop.hbase.client.Admin.move(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.util.MoveWithAck.call(..)) &&
    call(* org.apache.hadoop.hbase.util.MoveWithAck.isSameServer(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.chaos.ChaosAgent.execWithRetries(..)) &&
    call(* org.apache.hadoop.hbase.chaos.ChaosAgent.exec(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.procedure2.store.wal.WALProcedureStore.recoverLease(..)) &&
    call(* org.apache.hadoop.hbase.procedure2.store.wal.ProcedureWALFile.removeFile(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.shaded.protobuf.generated.RPCProtos.*ExceptionResponse.*Builder.mergeFrom(..)) &&
    call(* org.apache.hbase.thirdparty.com.google.protobuf.GeneratedMessageV3.*Builder.*.parseUnknownField(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.backup.HFileArchiver.resolveAndArchiveFile(..)) &&
    call(* org.apache.hadoop.fs.FileSystem.mkdirs(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.master.MasterWalManager.getFailedServersFromLogFolders(..)) &&
    call(* org.apache.hadoop.fs.FileSystem.exists(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.master.MasterWalManager.getFailedServersFromLogFolders(..)) &&
    call(* org.apache.hadoop.hbase.util.CommonFSUtils.listStatus(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.regionserver.RemoteProcedureResultReporter.run(..)) &&
    call(* org.apache.hadoop.hbase.shaded.protobuf.generated.RegionServerStatusProtos.*ReportProcedureDoneRequest.*Builder.addResult(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.replication.regionserver.RecoveredReplicationSourceShipper.getStartPosition(..)) &&
    call(* org.apache.hadoop.hbase.replication.regionserver.RecoveredReplicationSource.locateRecoveredPaths(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.replication.regionserver.ReplicationSource.uncaughtException(..)) &&
    call(* org.apache.hadoop.hbase.replication.regionserver.ReplicationSourceManager.refreshSources(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.replication.regionserver.ReplicationSourceWALReader.run(..)) &&
    call(* org.apache.hadoop.hbase.replication.regionserver.ReplicationSourceWALReader.readWALEntries(..) throws *IOException*)) ||
    (withincode(* org.apache.hadoop.hbase.replication.regionserver.ReplicationSourceWALReader.run(..)) &&
    call(* org.apache.hadoop.hbase.replication.regionserver.WALEntryStream.reset(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.replication.regionserver.ReplicationSourceWALReader.run(..)) &&
    call(* org.apache.hadoop.hbase.replication.regionserver.ReplicationSourceWALReader.tryAdvanceStreamAndCreateWALBatch(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.util.HBaseFsck.unlockHbck(..)) &&
    call(* org.apache.hbase.thirdparty.com.google.common.io.Closeables.close(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.util.HBaseFsckRepair.waitUntilAssigned(..)) &&
    call(* org.apache.hadoop.hbase.client.Admin.getClusterMetrics(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.wal.AbstractFSWALProvider.openReader(..)) &&
    call(* org.apache.hadoop.fs.Path.getFileSystem(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.wal.AbstractFSWALProvider.openReader(..)) &&
    call(* org.apache.hadoop.hbase.wal.WALFactory.createStreamReader(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.wal.WALFactory.createStreamReader(..)) &&
    call(* org.apache.hadoop.hbase.wal.AbstractFSWALProvider.*Reader.init(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.master.procedure.SwitchRpcThrottleProcedure.executeFromState(..)) &&
    call(* org.apache.hadoop.hbase.master.procedure.SwitchRpcThrottleProcedure.switchThrottleState(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.util.HBaseFsckRepair.waitUntilAssigned(..)) &&
    call(* org.apache.hadoop.hbase.client.Admin.getClusterMetrics(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.master.procedure.RSProcedureDispatcher.run(..)) &&
    call(* org.apache.hadoop.hbase.master.procedure.RSProcedureDispatcher.sendRequest(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.regionserver.handler.RegionReplicaFlushHandler.triggerFlushInPrimaryRegion(..)) &&
    call(* org.apache.hadoop.hbase.util.FutureUtils.get(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.regionserver.RemoteProcedureResultReporter.run(..)) &&
    call(* org.apache.hadoop.hbase.regionserver.HRegionServer.reportProcedureDone(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.replication.regionserver.ReplicationSource.initialize(..)) &&
    call(* org.apache.hadoop.hbase.replication.regionserver.ReplicationSource.createReplicationEndpoint(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.replication.regionserver.ReplicationSource.initialize(..)) &&
    call(* org.apache.hadoop.hbase.replication.regionserver.ReplicationSource.initAndStartReplicationEndpoint(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.replication.regionserver.ReplicationSourceManager.cleanOldLogs(..)) &&
    call(* org.apache.hadoop.hbase.replication.regionserver.ReplicationSourceManager.removeRemoteWALs(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.replication.regionserver.ReplicationSourceShipper.shipEdits(..)) &&
    call(* org.apache.hadoop.hbase.replication.regionserver.ReplicationSourceShipper.cleanUpHFileRefs(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.shaded.protobuf.generated.RPCProtos.*ExceptionResponse.*Builder.mergeFrom(..)) &&
    call(* org.apache.hbase.thirdparty.com.google.protobuf.CodedInputStream.readTag(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.shaded.protobuf.generated.RPCProtos.*ExceptionResponse.*Builder.mergeFrom(..)) &&
    call(* org.apache.hbase.thirdparty.com.google.protobuf.CodedInputStream.readBytes(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.shaded.protobuf.generated.RPCProtos.*ExceptionResponse.*Builder.mergeFrom(..)) &&
    call(* org.apache.hbase.thirdparty.com.google.protobuf.CodedInputStream.readBytes(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.shaded.protobuf.generated.RPCProtos.*ExceptionResponse.*Builder.mergeFrom(..)) &&
    call(* org.apache.hbase.thirdparty.com.google.protobuf.CodedInputStream.readBytes(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.shaded.protobuf.generated.RPCProtos.*ExceptionResponse.*Builder.mergeFrom(..)) &&
    call(* org.apache.hbase.thirdparty.com.google.protobuf.CodedInputStream.readInt32(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.shaded.protobuf.generated.RPCProtos.*ExceptionResponse.*Builder.mergeFrom(..)) &&
    call(* org.apache.hbase.thirdparty.com.google.protobuf.CodedInputStream.readBool(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.shaded.protobuf.generated.RPCProtos.*ExceptionResponse.*Builder.mergeFrom(..)) &&
    call(* org.apache.hbase.thirdparty.com.google.protobuf.CodedInputStream.readBool(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.rsgroup.RSGroupInfoManagerImpl.moveRegionsBetweenGroups(..)) &&
    call(* org.apache.hadoop.hbase.master.LoadBalancer.randomAssignment(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.master.procedure.ServerCrashProcedure.executeFromState(..)) &&
    call(* org.apache.hadoop.hbase.master.MasterServices.getProcedures(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.regionserver.SnapshotRegionCallable.doCall(..)) &&
    call(* org.apache.hadoop.hbase.regionserver.HRegion.flush(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.master.procedure.SplitWALProcedure.executeFromState(..)) &&
    call(* org.apache.hadoop.hbase.master.SplitWALManager.isSplitWALFinished(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.master.replication.SyncReplicationReplayWALProcedure.executeFromState(..)) &&
    call(* org.apache.hadoop.hbase.master.replication.SyncReplicationReplayWALManager.isReplayWALFinished(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.master.replication.SyncReplicationReplayWALRemoteProcedure.truncateWALs(..)) &&
    call(* org.apache.hadoop.hbase.master.replication.SyncReplicationReplayWALManager.finishReplayWAL(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.namequeues.WALEventTrackerTableAccessor.doPut(..)) &&
    call(* org.apache.hadoop.hbase.client.Connection.getTable(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.namequeues.WALEventTrackerTableAccessor.doPut(..)) &&
    call(* org.apache.hadoop.hbase.client.Table.put(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.procedure2.store.wal.WALProcedureStore.recoverLease(..)) &&
    call(* org.apache.hadoop.hbase.procedure2.store.wal.WALProcedureStore.getLogFiles(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.procedure2.store.wal.WALProcedureStore.recoverLease(..)) &&
    call(* org.apache.hadoop.hbase.procedure2.store.wal.WALProcedureStore.initOldLogs(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.procedure2.store.wal.WALProcedureStore.recoverLease(..)) &&
    call(* org.apache.hadoop.hbase.procedure2.store.wal.WALProcedureStore.rollWriter(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.procedure2.store.wal.WALProcedureStore.syncSlots(..)) &&
    call(* org.apache.hadoop.hbase.procedure2.store.wal.WALProcedureStore.syncSlots(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.procedure2.store.wal.WALProcedureStore.rollWriterWithRetries(..)) &&
    call(* org.apache.hadoop.hbase.procedure2.store.wal.WALProcedureStore.rollWriter(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.backup.impl.FullTableBackupClient.snapshotTable(..)) &&
    call(* snapshot(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.master.zksyncer.ClientZKSyncer.setDataForClientZkUntilSuccess(..)) &&
    call(* org.apache.hadoop.hbase.zookeeper.ZKUtil.setData(..) throws *IOException*)) ||
    (withincode(* org.apache.hadoop.hbase.master.replication.TransitPeerSyncReplicationStateProcedure.executeFromState(..)) &&
    call(* org.apache.hadoop.hbase.master.replication.TransitPeerSyncReplicationStateProcedure.createDirForRemoteWAL(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.master.MasterWalManager.getFailedServersFromLogFolders(..)) &&
    call(* listStatus(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.master.replication.TransitPeerSyncReplicationStateProcedure.executeFromState(..)) &&
    call(* org.apache.hadoop.hbase.master.replication.TransitPeerSyncReplicationStateProcedure.createDirForRemoteWAL(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.master.assignment.TransitRegionStateProcedure.executeFromState(..)) &&
    call(* openRegion(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.master.assignment.TransitRegionStateProcedure.executeFromState(..)) &&
    call(* confirmOpened(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.master.assignment.TransitRegionStateProcedure.executeFromState(..)) &&
    call(* closeRegion(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.master.assignment.TransitRegionStateProcedure.executeFromState(..)) &&
    call(* confirmClosed(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.master.replication.ModifyPeerProcedure.executeFromState(..)) &&
    call(* prePeerModification(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.master.replication.ModifyPeerProcedure.executeFromState(..)) &&
    call(* reopenRegions(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.master.replication.ModifyPeerProcedure.executeFromState(..)) &&
    call(* updateLastPushedSequenceIdForSerialPeer(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.master.replication.ModifyPeerProcedure.executeFromState(..)) &&
    call(* postPeerModification(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.master.replication.RecoverStandbyProcedure.executeFromState(..)) &&
    call(* renameToPeerReplayWALDir(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.master.replication.RecoverStandbyProcedure.executeFromState(..)) &&
    call(* renameToPeerSnapshotWALDir(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.mob.MobFileCleanerChore.cleanupObsoleteMobFiles(..)) &&
    call(* initReader(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.mob.MobFileCleanerChore.cleanupObsoleteMobFiles(..)) &&
    call(* closeStoreFile(..) throws *Exception*))) &&
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
    ((withincode(* org.apache.hadoop.hbase.ipc.BlockingRpcConnection.setupConnection(..)) &&
    call(* javax.net.SocketFactory.createSocket(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.ipc.BlockingRpcConnection.setupConnection(..)) &&
    call(* java.net.Socket.setTcpNoDelay(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.ipc.BlockingRpcConnection.setupConnection(..)) &&
    call(* java.net.Socket.setKeepAlive(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.ipc.BlockingRpcConnection.setupConnection(..)) &&
    call(* org.apache.hadoop.net.NetUtils.connect(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.ipc.BlockingRpcConnection.setupConnection(..)) &&
    call(* java.net.Socket.setSoTimeout(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.ipc.BlockingRpcConnection.setupIOstreams(..)) &&
    call(* org.apache.hadoop.hbase.ipc.BlockingRpcConnection.setupConnection(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.ipc.BlockingRpcConnection.setupIOstreams(..)) &&
    call(* org.apache.hadoop.hbase.ipc.BlockingRpcConnection.writeConnectionHeaderPreamble(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.ipc.BlockingRpcConnection.setupIOstreams(..)) &&
    call(* org.apache.hadoop.hbase.ipc.BlockingRpcConnection.writeConnectionHeader(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.ipc.BlockingRpcConnection.setupIOstreams(..)) &&
    call(* org.apache.hadoop.hbase.ipc.BlockingRpcConnection.processResponseForConnectionHeader(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.ipc.BlockingRpcConnection.setupConnection(..)) &&
    call(* java.net.Socket.bind(..) throws *Exception*))) &&
    !within(edu.uchicago.cs.systems.wasabi.*);

  after() throws SocketException : injectSocketException() {
    StackSnapshot stackSnapshot = new StackSnapshot();
    String retryCallerFunction = stackSnapshot.getSize() > 0 ? stackSnapshot.getFrame(0) : "???";
    String injectionSite = thisJoinPoint.toString();
    String retryException = "SocketException";
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

  /* Inject UnknownHostException */

  pointcut injectUnknownHostException():
    ((withincode(* org.apache.hadoop.hbase.ipc.BlockingRpcConnection.setupConnection(..)) &&
    call(* org.apache.hadoop.hbase.ipc.RpcConnection.getRemoteInetAddress(..) throws *Exception*))) &&
    !within(edu.uchicago.cs.systems.wasabi.*);

  after() throws UnknownHostException : injectUnknownHostException() {
    StackSnapshot stackSnapshot = new StackSnapshot();
    String retryCallerFunction = stackSnapshot.getSize() > 0 ? stackSnapshot.getFrame(0) : "???";
    String injectionSite = thisJoinPoint.toString();
    String retryException = "UnknownHostException";
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
      throw new UnknownHostException(
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

  /* Inject FileNotFoundException */

  pointcut injectFileNotFoundException():
    ((withincode(* org.apache.hadoop.hbase.io.FileLink.read(..)) &&
    call(* org.apache.hadoop.fs.FSDataInputStream.read(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.io.FileLink.readFully(..)) &&
    call(* readFully(..) throws *Exception*))) &&
    !within(edu.uchicago.cs.systems.wasabi.*);

  after() throws FileNotFoundException : injectFileNotFoundException() {
    StackSnapshot stackSnapshot = new StackSnapshot();
    String retryCallerFunction = stackSnapshot.getSize() > 0 ? stackSnapshot.getFrame(0) : "???";
    String injectionSite = thisJoinPoint.toString();
    String retryException = "FileNotFoundException";
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
      throw new FileNotFoundException(
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

  /* Inject InterruptedException */

  pointcut injectInterruptedException():
    ((withincode(* org.apache.hadoop.hbase.master.procedure.SnapshotVerifyProcedure.execute(..)) &&
    call(* org.apache.hadoop.hbase.master.procedure.ServerRemoteProcedure.execute(..) throws *Exception*))) &&
    !within(edu.uchicago.cs.systems.wasabi.*);

  after() throws InterruptedException : injectInterruptedException() {
    StackSnapshot stackSnapshot = new StackSnapshot();
    String retryCallerFunction = stackSnapshot.getSize() > 0 ? stackSnapshot.getFrame(0) : "???";
    String injectionSite = thisJoinPoint.toString();
    String retryException = "InterruptedException";
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
      throw new InterruptedException(
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

    /* Inject KeeperException.OperationTimeoutException */

    pointcut injectKeeperExceptionOperationTimeoutException():
    ((withincode(* org.apache.hadoop.hbase.util.HBaseFsck.setMasterInMaintenanceMode(..)) &&
    call(* org..*.createEphemeralNodeAndWatch(..))) ||
    (withincode(* org.apache.hadoop.hbase.MetaRegionLocationCache.updateMetaLocation(..)) &&
    call(* org..*.watchAndCheckExists(..))) ||
    (withincode(* org.apache.hadoop.hbase.MetaRegionLocationCache.updateMetaLocation(..)) &&
    call(* org..*.getMetaRegionLocation(..))) ||
    (withincode(* org.apache.hadoop.hbase.zookeeper.RecoverableZooKeeper.delete(..)) &&
    call(* org..*.checkZk(..))) ||
    (withincode(* org.apache.hadoop.hbase.zookeeper.RecoverableZooKeeper.exists(..)) &&
    call(* org..*.checkZk(..))) ||
    (withincode(* org.apache.hadoop.hbase.zookeeper.RecoverableZooKeeper.getChildren(..)) &&
    call(* org..*.checkZk(..))) ||
    (withincode(* org.apache.hadoop.hbase.zookeeper.RecoverableZooKeeper.getData(..)) &&
    call(* org..*.checkZk(..))) ||
    (withincode(* org.apache.hadoop.hbase.zookeeper.RecoverableZooKeeper.setData(..)) &&
    call(* org..*.checkZk(..))) ||
    (withincode(* org.apache.hadoop.hbase.zookeeper.RecoverableZooKeeper.createNonSequential(..)) &&
    call(* org..*.checkZk(..))) ||
    (withincode(* org.apache.hadoop.hbase.zookeeper.RecoverableZooKeeper.createSequential(..)) &&
    call(* org..*.checkZk(..))) ||
    (withincode(* org.apache.hadoop.hbase.zookeeper.RecoverableZooKeeper.getAcl(..)) &&
    call(* org..*.checkZk(..))) ||
    (withincode(* org.apache.hadoop.hbase.zookeeper.RecoverableZooKeeper.setAcl(..)) &&
    call(* org..*.checkZk(..)))) &&
    !within(edu.uchicago.cs.systems.wasabi.*);

  after() throws KeeperException : injectKeeperExceptionOperationTimeoutException() {
    if (this.wasabiCtx == null) { // This happens for non-test methods (e.g. config) inside test code
      return; // Ignore retry in "before" and "after" annotated methods
    }
    
    StackSnapshot stackSnapshot = new StackSnapshot();
    String retryCallerFunction = stackSnapshot.getSize() > 0 ? stackSnapshot.getFrame(0) : "???";
    String injectionSite = thisJoinPoint.toString();
    String retryException = "KeeperException.OperationTimeoutException";
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
      LOG.printMessage(
        WasabiLogger.LOG_LEVEL_ERROR, 
        String.format("[wasabi] [thread=%d] [Injection] Test ---%s--- | ---%s--- thrown after calling ---%s--- | Retry location ---%s--- | Retry attempt ---%d---",
          threadId,
          this.testMethodName,
          ipt.retryException,
          ipt.injectionSite,
          ipt.retrySourceLocation,
          ipt.injectionCount)
      );
      throw new KeeperException.OperationTimeoutException();
    }
  }

  /* Inject KeeperException.SessionExpiredException */

  pointcut injectKeeperExceptionSessionExpiredException():
    ((withincode(* org.apache.hadoop.hbase.zookeeper.RecoverableZooKeeper.multi(..)) &&
    call(* org..*.checkZk(..))) ||
    (withincode(* org.apache.hadoop.hbase.zookeeper.ZKNodeTracker.blockUntilAvailable(..)) &&
    call(* org..*.getDataAndWatch(..))) ||
    (withincode(* org.apache.hadoop.hbase.zookeeper.ZKNodeTracker.blockUntilAvailable(..)) &&
    call(* org..*.ZKUtil.checkExists(..))) ||
    (withincode(* org.apache.hadoop.hbase.zookeeper.ZKUtil.waitForBaseZNode(..)) &&
    call(* org..*.exists(..))) ||
    (withincode(* org.apache.hadoop.hbase.master.zksyncer.ClientZKSyncer.deleteDataForClientZkUntilSuccess(..)) &&
    call(* org..*.deleteNode(..))) ||
    (withincode(* org.apache.hadoop.hbase.MetaRegionLocationCache.loadMetaLocationsFromZk(..)) &&
    call(* org..*.getMetaReplicaNodesAndWatchChildren(..))) ||
    (withincode(* ZkSplitLogWorkerCoordination.getTaskList(..)) &&
    call(* org..*listChildrenAndWatchForNewChildren(..))) ||
    (withincode(* org.apache.hadoop.hbase.master.zksyncer.ClientZKSyncer.deleteDataForClientZkUntilSuccess(..)) &&
    call(* org..*.deleteNode(..))) ||
    (withincode(* org.apache.hadoop.hbase.master.zksyncer.ClientZKSyncer.reconnectAfterExpiration(..)) &&
    call(* org..*.reconnectAfterExpiration(..))) ||
    (withincode(* org.apache.hadoop.hbase.master.zksyncer.ClientZKSyncer.setDataForClientZkUntilSuccess(..)) &&
    call(* org..*.createNodeIfNotExistsNoWatch(..)))) &&
    !within(edu.uchicago.cs.systems.wasabi.*);

  after() throws KeeperException : injectKeeperExceptionSessionExpiredException() {
    if (this.wasabiCtx == null) { // This happens for non-test methods (e.g. config) inside test code
      return; // Ignore retry in "before" and "after" annotated methods
    }

    StackSnapshot stackSnapshot = new StackSnapshot();
    String retryCallerFunction = stackSnapshot.getSize() > 0 ? stackSnapshot.getFrame(0) : "???";
    String injectionSite = thisJoinPoint.toString();
    String retryException = "KeeperException.SessionExpiredException";
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
      LOG.printMessage(
        WasabiLogger.LOG_LEVEL_ERROR, 
        String.format("[wasabi] [thread=%d] [Injection] Test ---%s--- | ---%s--- thrown after calling ---%s--- | Retry location ---%s--- | Retry attempt ---%d---",
          threadId,
          this.testMethodName,
          ipt.retryException,
          ipt.injectionSite,
          ipt.retrySourceLocation,
          ipt.injectionCount)
      );
      throw new KeeperException.SessionExpiredException();
    }
  }

  /* Inject KeeperException.NoNodeException */

  pointcut injectKeeperExceptionNoNodeException():
    withincode(* org.apache.hadoop.hbase.master.zksyncer.ClientZKSyncer.setDataForClientZkUntilSuccess(..)) &&
    call(* org..*ZKUtil.setData(..) throws *KeeperException*) &&
    !within(edu.uchicago.cs.systems.wasabi.*);

  after() throws KeeperException : injectKeeperExceptionNoNodeException() {
    if (this.wasabiCtx == null) { // This happens for non-test methods (e.g. config) inside test code
      return; // Ignore retry in "before" and "after" annotated methods
    }

    StackSnapshot stackSnapshot = new StackSnapshot();
    String retryCallerFunction = stackSnapshot.getSize() > 0 ? stackSnapshot.getFrame(0) : "???";
    String injectionSite = thisJoinPoint.toString();
    String retryException = "KeeperException.NoNodeException";
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
      LOG.printMessage(
        WasabiLogger.LOG_LEVEL_ERROR, 
        String.format("[wasabi] [thread=%d] [Injection] Test ---%s--- | ---%s--- thrown after calling ---%s--- | Retry location ---%s--- | Retry attempt ---%d---",
          threadId,
          this.testMethodName,
          ipt.retryException,
          ipt.injectionSite,
          ipt.retrySourceLocation,
          ipt.injectionCount)
      );
      throw new KeeperException.NoNodeException();
    }
  }

  /* Inject BindException */

  pointcut injectBindException():
    ((withincode(* org.apache.hadoop.hbase.HBaseServerBase.putUpWebUI(..)) &&
    call(* org.apache.hadoop.hbase.http.InfoServer.start(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.replication.ZKReplicationQueueStorage.setWALPosition(..)) &&
    call(* org.apache.hadoop.hbase.zookeeper.ZKUtil.multiOrSequential(..) throws *Exception*))) &&
    !within(edu.uchicago.cs.systems.wasabi.*);

  after() throws BindException : injectBindException() {
    StackSnapshot stackSnapshot = new StackSnapshot();
    String retryCallerFunction = stackSnapshot.getSize() > 0 ? stackSnapshot.getFrame(0) : "???";
    String injectionSite = thisJoinPoint.toString();
    String retryException = "BindException";
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
      throw new BindException(
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

  /* Inject ReplicationException */

  pointcut injectReplicationException():
    ((withincode(* org.apache.hadoop.hbase.master.replication.ClaimReplicationQueuesProcedure.execute(..)) &&
    call(* removeQueue(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.master.replication.TransitPeerSyncReplicationStateProcedure.executeFromState(..)) &&
    call(* org.apache.hadoop.hbase.master.replication.TransitPeerSyncReplicationStateProcedure.postTransit(..) throws *ReplicationException*)) ||
    (withincode(* org.apache.hadoop.hbase.master.replication.TransitPeerSyncReplicationStateProcedure.executeFromState(..)) &&
    call(* org.apache.hadoop.hbase.master.replication.TransitPeerSyncReplicationStateProcedure.setPeerNewSyncReplicationState(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.master.replication.TransitPeerSyncReplicationStateProcedure.executeFromState(..)) &&
    call(* org.apache.hadoop.hbase.master.replication.TransitPeerSyncReplicationStateProcedure.removeAllReplicationQueues (..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.master.replication.TransitPeerSyncReplicationStateProcedure.executeFromState(..)) &&
    call(* org.apache.hadoop.hbase.master.replication.TransitPeerSyncReplicationStateProcedure.setLastPushedSequenceId(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.master.replication.TransitPeerSyncReplicationStateProcedure.executeFromState(..)) &&
    call(* org.apache.hadoop.hbase.master.replication.TransitPeerSyncReplicationStateProcedure.transitPeerSyncReplicationState(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.master.replication.TransitPeerSyncReplicationStateProcedure.executeFromState(..)) &&
    call(* org.apache.hadoop.hbase.master.replication.TransitPeerSyncReplicationStateProcedure.enablePear(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.master.replication.ModifyPeerProcedure.executeFromState(..)) &&
    call(* updatePeerStorage(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hbase.master.replication.ModifyPeerProcedure.executeFromState(..)) &&
    call(* enablePeer(..) throws *Exception*))) &&
    !within(edu.uchicago.cs.systems.wasabi.*);

  after() throws ReplicationException : injectReplicationException() {
    StackSnapshot stackSnapshot = new StackSnapshot();
    String retryCallerFunction = stackSnapshot.getSize() > 0 ? stackSnapshot.getFrame(0) : "???";
    String injectionSite = thisJoinPoint.toString();
    String retryException = "ReplicationException";
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
      throw new ReplicationException(
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