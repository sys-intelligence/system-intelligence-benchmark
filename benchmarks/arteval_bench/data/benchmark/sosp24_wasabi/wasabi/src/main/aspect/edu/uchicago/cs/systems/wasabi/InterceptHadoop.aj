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

import org.apache.hadoop.ipc.RetriableException;

import java.util.concurrent.ConcurrentHashMap;
import java.util.Set;

import edu.uchicago.cs.systems.wasabi.ConfigParser;
import edu.uchicago.cs.systems.wasabi.WasabiLogger;
import edu.uchicago.cs.systems.wasabi.WasabiContext;
import edu.uchicago.cs.systems.wasabi.InjectionPolicy;
import edu.uchicago.cs.systems.wasabi.StackSnapshot;
import edu.uchicago.cs.systems.wasabi.InjectionPoint;
import edu.uchicago.cs.systems.wasabi.ExecutionTrace;

public aspect InterceptHadoop {
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
    ((withincode(* org.apache.hadoop.ha.ActiveStandbyElector.reEstablishSession(..)) &&
    call(* org.apache.hadoop.ha.ActiveStandbyElector.createConnection(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.server.balancer.Balancer.run(..)) &&
    call(* org.apache.hadoop.hdfs.server.balancer.Balancer.doBalance(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.server.namenode.sps.BlockStorageMovementNeeded.*SPSPathIdProcessor.run(..)) &&
    call(* org.apache.hadoop.hdfs.server.namenode.sps.Context.scanAndCollectFiles(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.server.namenode.sps.BlockStorageMovementNeeded.*SPSPathIdProcessor.run(..)) &&
    call(* org.apache.hadoop.hdfs.server.namenode.sps.Context.scanAndCollectFiles(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.server.namenode.sps.BlockStorageMovementNeeded.*SPSPathIdProcessor.run(..)) &&
    call(* org.apache.hadoop.hdfs.server.namenode.sps.Context.removeSPSHint(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.fs.impl.prefetch.CachingBlockManager.get(..)) &&
    call(* org.apache.hadoop.fs.impl.prefetch.CachingBlockManager.getInternal(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.mapreduce.tools.CLI.getJob(..)) &&
    call(* org.apache.hadoop.mapreduce.Cluster.getJob(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.mapreduce.tools.CLI.getJob(..)) &&
    call(* org.apache.hadoop.mapreduce.Cluster.getJob(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.ipc.Client.*Connection.setupIOstreams(..)) &&
    call(* org.apache.hadoop.security.UserGroupInformation.doAs(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.mapred.ClientServiceDelegate.invoke(..)) &&
    call(* org.apache.hadoop.mapred.ClientServiceDelegate.getProxy(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.fs.azurebfs.oauth2.CustomTokenProviderAdapter.refreshToken(..)) &&
    call(* org.apache.hadoop.fs.azurebfs.extensions.CustomTokenProviderAdaptee.getAccessToken(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.DataStreamer.transfer(..)) &&
    call(* org.apache.hadoop.hdfs.DataStreamer.*StreamerStreams.sendTransferBlock(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.DataStreamer.createBlockOutputStream(..)) &&
    call(* org.apache.hadoop.net.NetUtils.getOutputStream(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.DataStreamer.createBlockOutputStream(..)) &&
    call(* org.apache.hadoop.net.NetUtils.getInputStream(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.DataStreamer.createBlockOutputStream(..)) &&
    call(* org.apache.hadoop.hdfs.protocol.datatransfer.Sender.writeBlock(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.DataStreamer.createBlockOutputStream(..)) &&
    call(* org.apache.hadoop.hdfs.protocol.proto.DataTransferProtos.*BlockOpResponseProto.parseFrom(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.DataStreamer.createBlockOutputStream(..)) &&
    call(* org.apache.hadoop.hdfs.protocolPB.PBHelperClient.vintPrefixed(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.DataStreamer.createBlockOutputStream(..)) &&
    call(* org.apache.hadoop.hdfs.protocol.datatransfer.DataTransferProtoUtil.checkBlockOpStatus(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.server.datanode.DataXceiverServer.run(..)) &&
    call(* org.apache.hadoop.hdfs.server.datanode.DataXceiver.create(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.tools.DebugAdmin.*RecoverLeaseCommand.run(..)) &&
    call(* org.apache.hadoop.hdfs.DistributedFileSystem.recoverLease(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.DFSInputStream.actualGetFromOneDataNode(..)) &&
    call(* org.apache.hadoop.hdfs.DFSInputStream.getBlockReader(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.DFSInputStream.actualGetFromOneDataNode(..)) &&
    call(* org.apache.hadoop.fs.ByteBufferReadable.read(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.DFSInputStream.openInfo(..)) &&
    call(* org.apache.hadoop.hdfs.DFSInputStream.getLastBlockLength(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.DFSInputStream.readBlockLength(..)) &&
    call(* org.apache.hadoop.hdfs.DFSUtilClient.createClientDatanodeProtocolProxy(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.DFSInputStream.readBlockLength(..)) &&
    call(* org.apache.hadoop.hdfs.protocol.ClientDatanodeProtocol.getReplicaVisibleLength(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.DFSInputStream.blockSeekTo(..)) &&
    call(* org.apache.hadoop.hdfs.DFSInputStream.getBlockAt(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.DFSInputStream.blockSeekTo(..)) &&
    call(* org.apache.hadoop.hdfs.DFSInputStream.chooseDataNode(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.DFSInputStream.blockSeekTo(..)) &&
    call(* org.apache.hadoop.hdfs.DFSInputStream.getBlockReader(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.DFSInputStream.readBuffer(..)) &&
    call(* org.apache.hadoop.hdfs.ReaderStrategy.readFromBlock(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.DFSInputStream.readBuffer(..)) &&
    call(* org.apache.hadoop.hdfs.DFSInputStream.seekToBlockSource(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.DFSInputStream.readBuffer(..)) &&
    call(* org.apache.hadoop.hdfs.DFSInputStream.seekToNewSource(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.DFSInputStream.readWithStrategy(..)) &&
    call(* org.apache.hadoop.hdfs.DFSInputStream.blockSeekTo(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.DFSInputStream.readWithStrategy(..)) &&
    call(* org.apache.hadoop.hdfs.DFSInputStream.readBuffer(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.DFSOutputStream.addBlock(..)) &&
    call(* org.apache.hadoop.hdfs.protocol.ClientProtocol.addBlock(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.DFSOutputStream.newStreamForCreate(..)) &&
    call(* org.apache.hadoop.hdfs.protocol.ClientProtocol.create(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.DFSOutputStream.completeFile(..)) &&
    call(* org.apache.hadoop.hdfs.protocol.ClientProtocol.complete(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.DFSStripedInputStream.createBlockReader(..)) &&
    call(* org.apache.hadoop.hdfs.DFSStripedInputStream.refreshLocatedBlock(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.DFSStripedInputStream.createBlockReader(..)) &&
    call(* org.apache.hadoop.hdfs.DFSInputStream.getBlockReader(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.mapreduce.task.reduce.EventFetcher.run(..)) &&
    call(* org.apache.hadoop.mapreduce.task.reduce.EventFetcher.getMapCompletionEvents(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.server.sps.ExternalSPSBlockMoveTaskHandler.*BlockMovingTask.moveBlock(..)) &&
    call(* org.apache.hadoop.hdfs.server.balancer.KeyManager.getAccessToken(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.server.sps.ExternalSPSBlockMoveTaskHandler.*BlockMovingTask.moveBlock(..)) &&
    call(* org.apache.hadoop.hdfs.server.common.sps.BlockDispatcher.moveBlock(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.yarn.server.federation.retry.FederationActionRetry.runWithRetries(..)) &&
    call(* org.apache.hadoop.yarn.server.federation.retry.FederationActionRetry.run(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.mapreduce.task.reduce.Fetcher.copyFromHost(..)) &&
    call(* org.apache.hadoop.mapreduce.task.reduce.Fetcher.copyMapOutput(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.FileChecksumHelper.*ReplicatedFileChecksumComputer.checksumBlock(..)) &&
    call(* org.apache.hadoop.hdfs.FileChecksumHelper.*ReplicatedFileChecksumComputer.tryDatanode(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.FileChecksumHelper.*StripedFileNonStripedChecksumComputer.checksumBlockGroup(..)) &&
    call(* org.apache.hadoop.hdfs.FileChecksumHelper.*StripedFileNonStripedChecksumComputer.tryDatanode(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.mapreduce.lib.output.FileOutputCommitter.commitJob(..)) &&
    call(* org.apache.hadoop.mapreduce.lib.output.FileOutputCommitter.commitJobInternal(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.yarn.server.timelineservice.storage.FileSystemTimelineWriterImpl.*FSAction.runWithRetries(..)) &&
    call(* org.apache.hadoop.yarn.server.timelineservice.storage.FileSystemTimelineWriterImpl.*FSAction.run(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.fs.FSInputChecker.readChecksumChunk(..)) &&
    call(* org.apache.hadoop.fs.FSInputChecker.readChunk(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.server.namenode.FSNamesystem.*LazyPersistFileScrubber.run(..)) &&
    call(* org.apache.hadoop.hdfs.server.namenode.FSNamesystem.*LazyPersistFileScrubber.clearCorruptLazyPersistFiles(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.mapred.JobClient.getJob(..)) &&
    call(* org.apache.hadoop.mapred.JobClient.getJobInner(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.mapred.JobEndNotifier.localRunnerNotification(..)) &&
    call(* org.apache.hadoop.mapred.JobEndNotifier.httpNotification(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.client.impl.LeaseRenewer.run(..)) &&
    call(* org.apache.hadoop.hdfs.client.impl.LeaseRenewer.renew(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.crypto.key.kms.LoadBalancingKMSClientProvider.doOp(..)) &&
    call(* org.apache.hadoop.crypto.key.kms.LoadBalancingKMSClientProvider.*ProviderCallable.*.call(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.yarn.logaggregation.filecontroller.ifile.LogAggregationIndexedFileController.*FSAction.runWithRetries(..)) &&
    call(* org.apache.hadoop.yarn.logaggregation.filecontroller.ifile.LogAggregationIndexedFileController.*FSAction.run(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.fs.cosn.CosNativeFileSystemStore.callCOSClientWithRetry(..)) &&
    call(* org.apache.hadoop.fs.azure.StorageInterface.*CloudBlockBlobWrapper.commitBlockList(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.fs.cosn.CosNFileReadTask.run(..)) &&
    call(* java.io.InputStream.close(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.fs.cosn.CosNFileReadTask.run(..)) &&
    call(* org.apache.hadoop.fs.cosn.NativeFileSystemStore.retrieveBlock(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.fs.cosn.CosNFileReadTask.run(..)) &&
    call(* org.apache.hadoop.io.IOUtils.readFully(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.fs.obs.OBSFileSystem.getFileStatus(..)) &&
    call(* org.apache.hadoop.fs.obs.OBSFileSystem.innerGetFileStatus(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.fs.obs.OBSInputStream.lazySeek(..)) &&
    call(* org.apache.hadoop.fs.obs.OBSInputStream.reopen(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.fs.obs.OBSInputStream.lazySeek(..)) &&
    call(* org.apache.hadoop.fs.obs.OBSInputStream.seekInStream(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.fs.obs.OBSInputStream.read(..)) &&
    call(* java.io.InputStream.read(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.fs.obs.OBSInputStream.onReadFailure(..)) &&
    call(* org.apache.hadoop.fs.obs.OBSInputStream.reopen(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.fs.obs.OBSInputStream.read(..)) &&
    call(* org.apache.hadoop.fs.obs.OBSInputStream.tryToReadFromInputStream(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.fs.obs.OBSInputStream.read(..)) &&
    call(* org.apache.hadoop.fs.obs.OBSInputStream.tryToReadFromInputStream(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.fs.obs.OBSInputStream.randomReadWithNewInputStream(..)) &&
    call(* org.apache.hadoop.fs.obs.OBSInputStream.tryToReadFromInputStream(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.fs.obs.OBSObjectBucketUtils.createEmptyObject(..)) &&
    call(* org.apache.hadoop.fs.obs.OBSObjectBucketUtils.innerCreateEmptyObject(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.fs.obs.OBSObjectBucketUtils.copyFile(..)) &&
    call(* org.apache.hadoop.fs.obs.OBSObjectBucketUtils.innerCopyFile(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.fs.obs.OBSPosixBucketUtils.innerFsRenameWithRetry(..)) &&
    call(* org.apache.hadoop.fs.obs.OBSPosixBucketUtils.innerFsRenameFile(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.fs.impl.prefetch.CachingBlockManager.get(..)) &&
    call(* org.apache.hadoop.fs.impl.prefetch.BufferPool.acquire(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.ha.ActiveStandbyElector.zkDoWithRetries(..)) &&
    call(* org.apache.hadoop.ha.ActiveStandbyElector.*ZKAction.*.run(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.security.UserGroupInformation.*AutoRenewalForUserCredsRunnable.run(..)) &&
    call(* org.apache.hadoop.security.UserGroupInformation.*AutoRenewalForUserCredsRunnable.relogin(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.ipc.protobuf.RpcHeaderProtos.*RpcRequestHeaderProto.RpcRequestHeaderProto(..)) &&
    call(* org.apache.hadoop.thirdparty.protobuf.CodedInputStream.readBytes(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.ipc.protobuf.RpcHeaderProtos.*RpcRequestHeaderProto.RpcRequestHeaderProto(..)) &&
    call(* org.apache.hadoop.thirdparty.protobuf.CodedInputStream.readEnum(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.ipc.protobuf.RpcHeaderProtos.*RpcRequestHeaderProto.RpcRequestHeaderProto(..)) &&
    call(* org.apache.hadoop.thirdparty.protobuf.CodedInputStream.readInt64(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.ipc.protobuf.RpcHeaderProtos.*RpcRequestHeaderProto.RpcRequestHeaderProto(..)) &&
    call(* org.apache.hadoop.thirdparty.protobuf.CodedInputStream.readMessage(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.ipc.protobuf.RpcHeaderProtos.*RpcRequestHeaderProto.RpcRequestHeaderProto(..)) &&
    call(* org.apache.hadoop.thirdparty.protobuf.CodedInputStream.readSInt32(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.ipc.protobuf.RpcHeaderProtos.*RpcRequestHeaderProto.RpcRequestHeaderProto(..)) &&
    call(* org.apache.hadoop.thirdparty.protobuf.CodedInputStream.readTag(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.ipc.protobuf.RpcHeaderProtos.*RpcRequestHeaderProto.RpcRequestHeaderProto(..)) &&
    call(* org.apache.hadoop.thirdparty.protobuf.GeneratedMessageV3.parseUnknownField(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.ipc.protobuf.RpcHeaderProtos.*RpcResponseHeaderProto.RpcResponseHeaderProto(..)) &&
    call(* org.apache.hadoop.thirdparty.protobuf.CodedInputStream.readBytes(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.ipc.protobuf.RpcHeaderProtos.*RpcResponseHeaderProto.RpcResponseHeaderProto(..)) &&
    call(* org.apache.hadoop.thirdparty.protobuf.CodedInputStream.readEnum(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.ipc.protobuf.RpcHeaderProtos.*RpcResponseHeaderProto.RpcResponseHeaderProto(..)) &&
    call(* org.apache.hadoop.thirdparty.protobuf.CodedInputStream.readInt64(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.ipc.protobuf.RpcHeaderProtos.*RpcResponseHeaderProto.RpcResponseHeaderProto(..)) &&
    call(* org.apache.hadoop.thirdparty.protobuf.CodedInputStream.readSInt32(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.ipc.protobuf.RpcHeaderProtos.*RpcResponseHeaderProto.RpcResponseHeaderProto(..)) &&
    call(* org.apache.hadoop.thirdparty.protobuf.CodedInputStream.readTag(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.ipc.protobuf.RpcHeaderProtos.*RpcResponseHeaderProto.RpcResponseHeaderProto(..)) &&
    call(* org.apache.hadoop.thirdparty.protobuf.CodedInputStream.readUInt32(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.ipc.protobuf.RpcHeaderProtos.*RpcResponseHeaderProto.RpcResponseHeaderProto(..)) &&
    call(* org.apache.hadoop.thirdparty.protobuf.GeneratedMessageV3.parseUnknownField(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.DataStreamer.createBlockOutputStream(..)) &&
    call(* org.apache.hadoop.hdfs.protocol.datatransfer.BlockConstructionStage.getRecoveryStage(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.DFSInputStream.openInfo(..)) &&
    call(* org.apache.hadoop.hdfs.DFSInputStream.fetchAndCheckLocatedBlocks(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.DFSInputStream.openInfo(..)) &&
    call(* org.apache.hadoop.hdfs.DFSInputStream.waitFor(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.DFSInputStream.readBlockLength(..)) &&
    call(* org.apache.hadoop.util.StopWatch.start(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.server.namenode.ha.ObserverReadProxyProvider.*ObserverReadInvocationHandler.invoke(..)) &&
    call(* java.lang.reflect.Method.invoke(..) throws *IOException*)) ||
    (withincode(* org.apache.hadoop.hdfs.shortcircuit.ShortCircuitCache.*SlotReleaser.run(..)) &&
    call(* org.apache.hadoop.hdfs.protocolPB.PBHelperClient.vintPrefixed(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.server.datanode.fsdataset.impl.ProvidedVolumeImpl.*ProvidedBlockPoolSlice.fetchVolumeMap(..)) &&
    call(* org.apache.hadoop.hdfs.server.common.blockaliasmap.BlockAliasMap.*.getReader(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.server.namenode.ha.EditLogTailer.*MultipleNameNodeProxy.getActiveNodeProxy(..)) &&
    call(* org.apache.hadoop.ipc.RPC.getProtocolVersion(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.server.namenode.ReencryptionHandler.run(..)) &&
    call(* org.apache.hadoop.hdfs.server.namenode.ReencryptionHandler.*ReencryptionPendingInodeIdCollector.checkPauseForTesting(..) throws *IOException*)) ||
    (withincode(* org.apache.hadoop.hdfs.server.namenode.ReencryptionUpdater.takeAndProcessTasks(..)) &&
    call(* org.apache.hadoop.util.StopWatch.start(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.server.namenode.SecondaryNameNode.doWork(..)) &&
    call(* org.apache.hadoop.security.UserGroupInformation.checkTGTAndReloginFromKeytab(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.server.namenode.SecondaryNameNode.doWork(..)) &&
    call(* org.apache.hadoop.security.UserGroupInformation.getCurrentUser(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.mapred.YarnChild.main(..)) &&
    call(* org.apache.hadoop.mapred.TaskUmbilicalProtocol.getTask(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.mapred.ClientServiceDelegate.invoke(..)) &&
    call(* java.lang.reflect.Method.invoke(..) throws *IOException*)) ||
    (withincode(* org.apache.hadoop.fs.aliyun.oss.AliyunOSSFileReaderTask.run(..)) &&
    call(* org.apache.hadoop.io.IOUtils.readFully(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.fs.s3a.Invoker.retryUntranslated(..)) &&
    call(* org.apache.hadoop.util.functional.CallableRaisingIOE.*.apply(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.fs.azure.BlockBlobAppendStream.writeBlockRequestInternal(..)) &&
    call(* org.apache.hadoop.fs.azure.StorageInterface.*CloudBlockBlobWrapper.uploadBlock(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.fs.azure.BlockBlobAppendStream.writeBlockRequestInternal(..)) &&
    call(* org.apache.hadoop.fs.azure.StorageInterface.*CloudBlockBlobWrapper.uploadBlock(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.fs.azure.BlockBlobAppendStream.writeBlockListRequestInternal(..)) &&
    call(* org.apache.hadoop.fs.azure.StorageInterface.*CloudBlockBlobWrapper.commitBlockList(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.fs.azure.WasbRemoteCallHelper.retryableRequest(..)) &&
    call(* java.io.BufferedReader.readLine(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.fs.azurebfs.oauth2.AzureADAuthenticator.getTokenCall(..)) &&
    call(* org.apache.hadoop.fs.azurebfs.oauth2.AzureADAuthenticator.getTokenSingleCall(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.tools.SimpleCopyListing.*TraverseDirectory.traverseDirectoryMultiThreaded(..)) &&
    call(* org.apache.hadoop.tools.util.ProducerConsumer.*.take(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.tools.dynamometer.DynoInfraUtils.waitForAndGetNameNodeProperties(..)) &&
    call(* java.util.Properties.load(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.tools.dynamometer.DynoInfraUtils.waitForAndGetNameNodeProperties(..)) &&
    call(* org.apache.hadoop.fs.FileSystem.open(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.tools.dynamometer.DynoInfraUtils.waitForAndGetNameNodeProperties(..)) &&
    call(* org.apache.hadoop.fs.Path.getFileSystem(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.tools.dynamometer.DynoInfraUtils.waitForNameNodeJMXValue(..)) &&
    call(* org.apache.hadoop.tools.dynamometer.DynoInfraUtils.fetchNameNodeJMXValue(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.yarn.proto.YarnProtos.*ContainerLaunchContextProto.ContainerLaunchContextProto(..)) &&
    call(* org.apache.hadoop.thirdparty.protobuf.CodedInputStream.readBytes(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.yarn.proto.YarnProtos.*ContainerLaunchContextProto.ContainerLaunchContextProto(..)) &&
    call(* org.apache.hadoop.thirdparty.protobuf.CodedInputStream.readMessage(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.yarn.proto.YarnProtos.*ContainerLaunchContextProto.ContainerLaunchContextProto(..)) &&
    call(* org.apache.hadoop.thirdparty.protobuf.CodedInputStream.readTag(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.yarn.proto.YarnProtos.*ContainerLaunchContextProto.ContainerLaunchContextProto(..)) &&
    call(* org.apache.hadoop.thirdparty.protobuf.GeneratedMessageV3.parseUnknownField(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.yarn.proto.YarnProtos.*ContainerRetryContextProto.ContainerRetryContextProto(..)) &&
    call(* org.apache.hadoop.thirdparty.protobuf.CodedInputStream.readEnum(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.yarn.proto.YarnProtos.*ContainerRetryContextProto.ContainerRetryContextProto(..)) &&
    call(* org.apache.hadoop.thirdparty.protobuf.CodedInputStream.readInt32(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.yarn.proto.YarnProtos.*ContainerRetryContextProto.ContainerRetryContextProto(..)) &&
    call(* org.apache.hadoop.thirdparty.protobuf.CodedInputStream.readInt64(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.yarn.proto.YarnProtos.*ContainerRetryContextProto.ContainerRetryContextProto(..)) &&
    call(* org.apache.hadoop.thirdparty.protobuf.CodedInputStream.readRawVarint32(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.yarn.proto.YarnProtos.*ContainerRetryContextProto.ContainerRetryContextProto(..)) &&
    call(* org.apache.hadoop.thirdparty.protobuf.CodedInputStream.readTag(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.yarn.proto.YarnProtos.*ContainerRetryContextProto.ContainerRetryContextProto(..)) &&
    call(* org.apache.hadoop.thirdparty.protobuf.GeneratedMessageV3.parseUnknownField(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.yarn.logaggregation.filecontroller.ifile.LogAggregationIndexedFileController.loadUUIDFromLogFile(..)) &&
    call(* java.io.DataInputStream.readFully(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.yarn.logaggregation.filecontroller.ifile.LogAggregationIndexedFileController.loadUUIDFromLogFile(..)) &&
    call(* org.apache.hadoop.fs.FileContext.open(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.yarn.logaggregation.filecontroller.ifile.LogAggregationIndexedFileController.loadUUIDFromLogFile(..)) &&
    call(* org.apache.hadoop.fs.RemoteIterator.*.hasNext(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.yarn.logaggregation.filecontroller.ifile.LogAggregationIndexedFileController.loadUUIDFromLogFile(..)) &&
    call(* org.apache.hadoop.fs.RemoteIterator.*.next(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.yarn.logaggregation.filecontroller.ifile.LogAggregationIndexedFileController.loadUUIDFromLogFile(..)) &&
    call(* org.apache.hadoop.yarn.logaggregation.filecontroller.ifile.LogAggregationIndexedFileController.deleteFileWithRetries(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.yarn.server.resourcemanager.recovery.FileSystemRMStateStore.*FSAction.runWithRetries(..)) &&
    call(* org.apache.hadoop.yarn.server.resourcemanager.recovery.FileSystemRMStateStore.*FSAction.run(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.yarn.server.router.clientrm.FederationClientInterceptor.submitReservation(..)) &&
    call(* org.apache.hadoop.yarn.api.ApplicationClientProtocol.submitReservation(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.yarn.server.router.clientrm.FederationClientInterceptor.getNewReservation(..)) &&
    call(* org.apache.hadoop.yarn.api.ApplicationClientProtocol.getNewReservation(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.yarn.server.nodemanager.recovery.NMLeveldbStateStoreService.loadContainerState(..)) &&
    call(* org.apache.hadoop.yarn.server.utils.BuilderUtils.newContainerTokenIdentifier(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.yarn.server.nodemanager.recovery.NMLeveldbStateStoreService.loadContainerState(..)) &&
    call(* org.apache.hadoop.yarn.server.nodemanager.containermanager.container.ResourceMappings.*AssignedResources.fromBytes(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.ipc.RPC.waitForProtocolProxy(..)) &&
    call(* org.apache.hadoop.security.UserGroupInformation.getCurrentUser(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.server.namenode.SecondaryNameNode.doWork(..)) &&
    call(* org.apache.hadoop.hdfs.server.namenode.SecondaryNameNode.shouldCheckpointBasedOnCount(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.server.namenode.SecondaryNameNode.doWork(..)) &&
    call(* org.apache.hadoop.hdfs.server.namenode.SecondaryNameNode.doCheckpoint(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.tools.SimpleCopyListing.*TraverseDirectory.traverseDirectoryMultiThreaded(..)) &&
    call(* org.apache.hadoop.tools.util.DistCpUtils.toCopyListingFileStatus(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.tools.SimpleCopyListing.*TraverseDirectory.traverseDirectoryMultiThreaded(..)) &&
    call(* org.apache.hadoop.tools.SimpleCopyListing.addToFileListing(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.tools.SimpleCopyListing.*TraverseDirectory.traverseDirectoryMultiThreaded(..)) &&
    call(* org.apache.hadoop.tools.SimpleCopyListing.writeToFileListing(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.server.namenode.sps.StoragePolicySatisfier.run(..)) &&
    call(* org.apache.hadoop.hdfs.server.namenode.sps.Context.getFileInfo(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.server.namenode.sps.StoragePolicySatisfier.run(..)) &&
    call(* org.apache.hadoop.hdfs.server.namenode.sps.StoragePolicySatisfier.analyseBlocksStorageMovementsAndAssignToDN(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.server.namenode.sps.StoragePolicySatisfier.run(..)) &&
    call(* org.apache.hadoop.hdfs.server.namenode.sps.BlockStorageMovementNeeded.removeItemTrackInfo(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.mapred.Task.done(..)) &&
    call(* org.apache.hadoop.mapred.TaskUmbilicalProtocol.commitPending(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.mapred.Task.statusUpdate(..)) &&
    call(* org.apache.hadoop.mapred.TaskUmbilicalProtocol.statusUpdate(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.mapred.Task.sendDone(..)) &&
    call(* org.apache.hadoop.mapred.TaskUmbilicalProtocol.done(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.mapred.Task.commit(..)) &&
    call(* org.apache.hadoop.mapred.TaskUmbilicalProtocol.canCommit(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.mapred.Task.*TaskReporter.run(..)) &&
    call(* org.apache.hadoop.mapred.TaskUmbilicalProtocol.statusUpdate(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.mapred.Task.*TaskReporter.run(..)) &&
    call(* org.apache.hadoop.mapred.TaskUmbilicalProtocol.statusUpdate(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.yarn.client.api.impl.TimelineV2ClientImpl.putObjects(..)) &&
    call(* org.apache.hadoop.yarn.client.api.impl.TimelineV2ClientImpl.putObjects(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.yarn.server.uam.UnmanagedApplicationManager.monitorCurrentAppAttempt(..)) &&
    call(* org.apache.hadoop.yarn.server.uam.UnmanagedApplicationManager.getApplicationReport(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.yarn.server.uam.UnmanagedApplicationManager.monitorCurrentAppAttempt(..)) &&
    call(* org.apache.hadoop.yarn.server.uam.UnmanagedApplicationManager.getApplicationReport(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.yarn.server.uam.UnmanagedApplicationManager.monitorCurrentAppAttempt(..)) &&
    call(* org.apache.hadoop.yarn.api.ApplicationBaseProtocol.getApplicationAttemptReport(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.ha.HealthMonitor.tryConnect(..)) &&
    call(* org.apache.hadoop.ha.HealthMonitor.createProxy(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.fs.TrashPolicyDefault.moveToTrash(..)) &&
    call(* mkdirs(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.fs.TrashPolicyDefault.run(..)) &&
    call(* createCheckpoint(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.fs.TrashPolicyDefault.run(..)) &&
    call(* deleteCheckpoint(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.DFSClient.renewLease(..)) &&
    call(* renewLease(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.util.DiskChecker.doDiskIo(..)) &&
    call(* diskIoCheckWithoutNativeIo(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.server.sps.ExternalStoragePolicySatisfier.getNameNodeConnector(..)) &&
    call(* newNameNodeConnectors(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.protocol.CacheDirectiveIterator.makeRequest(..)) &&
    call(* listCacheDirectives(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.mapreduce.v2.app.local.LocalContainerAllocator.heartbeat(..)) &&
    call(* allocate(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.yarn.server.resourcemanager.security.DelegationTokenRenewer.run(..)) &&
    call(* doAs(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.yarn.server.AMRMClientRelayer.allocate(..)) &&
    call(* reRegisterApplicationMaster(..) throws *Exception*)) ||
    (withincode(* CreateOutputDirectoriesStage.maybeCreateOneDirectory(..)) &&
    call(* mkdirs(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.io.retry.RetryInvocationHandler.invokeOnce(..)) &&
    call(* invoke(..) throws *Exception*))) &&
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
    ((withincode(* org.apache.hadoop.hdfs.server.datanode.BPServiceActor.run(..)) &&
    call(* org.apache.hadoop.hdfs.server.datanode.BPServiceActor.connectToNNAndHandshake(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.ipc.Client.*Connection.setupConnection(..)) &&
    call(* javax.net.SocketFactory.createSocket(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.ipc.Client.*Connection.setupConnection(..)) &&
    call(* java.net.Socket.setTcpNoDelay(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.ipc.Client.*Connection.setupConnection(..)) &&
    call(* java.net.Socket.setKeepAlive(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.ipc.Client.*Connection.setupConnection(..)) &&
    call(* org.apache.hadoop.net.NetUtils.getLocalInetAddress(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.ipc.Client.*Connection.setupConnection(..)) &&
    call(* java.net.Socket.setReuseAddress(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.ipc.Client.*Connection.setupConnection(..)) &&
    call(* java.net.Socket.bind(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.ipc.Client.*Connection.setupConnection(..)) &&
    call(* java.net.Socket.setSoTimeout(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.ipc.Client.*Connection.setupIOstreams(..)) &&
    call(* org.apache.hadoop.ipc.Client.*Connection.setupConnection(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.ipc.Client.*Connection.setupIOstreams(..)) &&
    call(* org.apache.hadoop.ipc.Client.*Connection.writeConnectionHeader(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.ipc.Client.*Connection.setupIOstreams(..)) &&
    call(* org.apache.hadoop.ipc.Client.*IpcStreams.setSaslClient(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.ipc.Client.*Connection.setupIOstreams(..)) &&
    call(* org.apache.hadoop.ipc.Client.*Connection.writeConnectionContext(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.DataStreamer.createBlockOutputStream(..)) &&
    call(* org.apache.hadoop.hdfs.DataStreamer.createSocketForPipeline(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.DataStreamer.createBlockOutputStream(..)) &&
    call(* org.apache.hadoop.hdfs.protocol.datatransfer.sasl.SaslDataTransferClient.socketSend(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.server.namenode.ha.EditLogTailer.*MultipleNameNodeProxy.getActiveNodeProxy(..)) &&
    call(* org.apache.hadoop.ipc.RPC.waitForProxy(..) throws *Exception*)) ||
    (withincode(* java.io.IOException(..)) &&
    call(* org.apache.hadoop.mapreduce.task.reduce.Fetcher.openConnection(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.mapreduce.task.reduce.Fetcher.connect(..)) &&
    call(* java.net.URLConnection.connect(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.server.namenode.FSDirEncryptionZoneOp.*EDEKCacheLoader.run(..)) &&
    call(* org.apache.hadoop.crypto.key.KeyProviderCryptoExtension.warmUpEncryptedKeys(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.yarn.client.cli.LogsCLI.*ClientConnectionRetry.retryOn(..)) &&
    call(* org.apache.hadoop.yarn.client.cli.LogsCLI.*ClientRetryOp.run(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.ipc.Client.*Connection.setupConnection(..)) &&
    call(* java.net.Socket.setTrafficClass(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.shortcircuit.ShortCircuitCache.*SlotReleaser.run(..)) &&
    call(* org.apache.hadoop.hdfs.protocol.datatransfer.Sender.releaseShortCircuitFds(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.shortcircuit.ShortCircuitCache.*SlotReleaser.run(..)) &&
    call(* org.apache.hadoop.hdfs.protocol.proto.DataTransferProtos.*ReleaseShortCircuitAccessResponseProto.parseFrom(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.fs.azure.WasbRemoteCallHelper.retryableRequest(..)) &&
    call(* org.apache.hadoop.fs.azure.WasbRemoteCallHelper.getHttpRequest(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.fs.azure.WasbRemoteCallHelper.retryableRequest(..)) &&
    call(* org.apache.hadoop.fs.azure.WasbRemoteCallHelper.getHttpRequest(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.fs.azure.WasbRemoteCallHelper.retryableRequest(..)) &&
    call(* org.apache.http.client.HttpClient.execute(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.fs.azure.WasbRemoteCallHelper.retryableRequest(..)) &&
    call(* org.apache.http.HttpEntity.getContent(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.tools.util.RetriableCommand.execute(..)) &&
    call(* org.apache.hadoop.tools.util.RetriableCommand.doExecute(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.yarn.client.api.impl.TimelineConnector.*TimelineClientConnectionRetry.retryOn(..)) &&
    call(* org.apache.hadoop.yarn.client.api.impl.TimelineConnector.*TimelineClientRetryOp.run(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.shortcircuit.ShortCircuitCache.*SlotReleaser.run(..)) &&
    call(* org.apache.hadoop.net.unix.DomainSocket.connect(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.web.WebHdfsFileSystem.*AbstractRunner.runWithRetry(..)) &&
    call(* org.apache.hadoop.hdfs.web.WebHdfsFileSystem.*AbstractRunner.getUrl(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.web.WebHdfsFileSystem.*AbstractRunner.runWithRetry(..)) &&
    call(* org.apache.hadoop.hdfs.web.WebHdfsFileSystem.*AbstractRunner.connect(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.web.WebHdfsFileSystem.*AbstractRunner.runWithRetry(..)) &&
    call(* org.apache.hadoop.hdfs.web.WebHdfsFileSystem.*AbstractRunner.getResponse(..) throws *Exception*))) &&
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

  /* Inject ConnectException */

  pointcut injectConnectException():
    ((withincode(* org.apache.hadoop.ipc.Client.*Connection.setupConnection(..)) &&
    call(* org.apache.hadoop.net.NetUtils.connect(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.ipc.RPC.waitForProtocolProxy(..)) &&
    call(* org.apache.hadoop.ipc.RPC.getProtocolProxy(..) throws *Exception*))) &&
    !within(edu.uchicago.cs.systems.wasabi.*);

  after() throws ConnectException : injectConnectException() {
    StackSnapshot stackSnapshot = new StackSnapshot();
    String retryCallerFunction = stackSnapshot.getSize() > 0 ? stackSnapshot.getFrame(0) : "???";
    String injectionSite = thisJoinPoint.toString();
    String retryException = "ConnectException";
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
      throw new ConnectException(
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

  /* Inject SocketTimeoutException */

  pointcut injectSocketTimeoutException():
    ((withincode(* org.apache.hadoop.hdfs.server.datanode.DataXceiverServer.run(..)) &&
    call(* org.apache.hadoop.hdfs.net.PeerServer.accept(..) throws *Exception*))) &&
    !within(edu.uchicago.cs.systems.wasabi.*);

  after() throws SocketTimeoutException : injectSocketTimeoutException() {
    StackSnapshot stackSnapshot = new StackSnapshot();
    String retryCallerFunction = stackSnapshot.getSize() > 0 ? stackSnapshot.getFrame(0) : "???";
    String injectionSite = thisJoinPoint.toString();
    String retryException = "SocketTimeoutException";
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
      throw new SocketTimeoutException(
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
    ((withincode(* org.apache.hadoop.fs.obs.OBSCommonUtils.isFolderEmpty(..)) &&
    call(* org.apache.hadoop.fs.obs.OBSCommonUtils.innerIsFolderEmpty(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.fs.obs.OBSPosixBucketUtils.innerFsRenameWithRetry(..)) &&
    call(* org.apache.hadoop.fs.obs.OBSPosixBucketUtils.innerFsRenameFile(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.yarn.logaggregation.filecontroller.ifile.LogAggregationIndexedFileController.loadUUIDFromLogFile(..)) &&
    call(* org.apache.hadoop.fs.FileContext.open(..) throws *Exception*))) &&
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

  /* Inject EOFException */

  pointcut injectEOFException():
    ((withincode(* org.apache.hadoop.hdfs.DataStreamer.createBlockOutputStream(..)) &&
    call(* org.apache.hadoop.hdfs.protocolPB.PBHelperClient.vintPrefixed(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.shortcircuit.ShortCircuitCache.*SlotReleaser.run(..)) &&
    call(* org.apache.hadoop.hdfs.protocolPB.PBHelperClient.vintPrefixed(..) throws *Exception*))) &&
    !within(edu.uchicago.cs.systems.wasabi.*);

  after() throws EOFException : injectEOFException() {
    StackSnapshot stackSnapshot = new StackSnapshot();
    String retryCallerFunction = stackSnapshot.getSize() > 0 ? stackSnapshot.getFrame(0) : "???";
    String injectionSite = thisJoinPoint.toString();
    String retryException = "EOFException";
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
      throw new EOFException(
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

  /* Inject RetriableException */

  pointcut injectRetriableException():
    ((withincode(* org.apache.hadoop.hdfs.server.namenode.ReencryptionUpdater.takeAndProcessTasks(..)) &&
    call(* org.apache.hadoop.hdfs.server.namenode.ReencryptionUpdater.processTask(..) throws *Exception*)) ||
    (withincode(* org.apache.hadoop.hdfs.shortcircuit.ShortCircuitCache.*SlotReleaser.run(..)) &&
    call(* org.apache.hadoop.hdfs.protocolPB.PBHelperClient.vintPrefixed(..) throws *Exception*))) &&
    !within(edu.uchicago.cs.systems.wasabi.*);

  after() throws RetriableException : injectRetriableException() {
    StackSnapshot stackSnapshot = new StackSnapshot();
    String retryCallerFunction = stackSnapshot.getSize() > 0 ? stackSnapshot.getFrame(0) : "???";
    String injectionSite = thisJoinPoint.toString();
    String retryException = "RetriableException";
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
      throw new RetriableException(
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
