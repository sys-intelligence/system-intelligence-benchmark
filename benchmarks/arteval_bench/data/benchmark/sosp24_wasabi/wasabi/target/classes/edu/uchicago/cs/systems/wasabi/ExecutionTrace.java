package edu.uchicago.cs.systems.wasabi;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;
import java.util.Deque;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Objects;

class OpEntry {

  public static final Integer RETRY_CALLER_OP = 0;
  public static final Integer THREAD_SLEEP_OP = 1;

  private String opName = "";
  private Integer opType = this.RETRY_CALLER_OP;
  private StackSnapshot stackSnapshot = null;
  private Long timestamp = 0L;
  private String exception = null;

  public OpEntry(String opName,
                 Integer opType,
                 Long timestamp, 
                 StackSnapshot stackSnapshot) {
    this.opName = opName;
    this.opType = opType;
    this.timestamp = timestamp;
    this.stackSnapshot = stackSnapshot;
    this.exception = null;
  }

  public OpEntry(String opName,
                 Integer opType,
                 Long timestamp, 
                 StackSnapshot stackSnapshot,
                 String exception) {
    this.opName = opName;
    this.opType = opType;
    this.timestamp = timestamp;
    this.stackSnapshot = stackSnapshot;
    this.exception = exception;
  }

  public OpEntry(String opName,
                 Integer opType,
                 StackSnapshot stackSnapshot,
                 String exception) {
    this.opName = opName;
    this.opType = opType;
    this.timestamp = 0L;
    this.stackSnapshot = stackSnapshot;
    this.exception = exception;
  }

  public Boolean isOfType(Integer opType) {
    return Objects.equals(this.opType, opType);
  }

  public Boolean hasFrame(String target) {
    return this.stackSnapshot.hasFrame(target);
  }

  public Boolean isSameOp(OpEntry target) {      
    return ( 
        this.opType == target.opType && 
        (this.exception == null || this.exception.equals(target.exception)) &&
        this.stackSnapshot.isEqual(target.stackSnapshot)
      );
  }

  public void printOpEntry(WasabiLogger log) {
    log.printMessage(WasabiLogger.LOG_LEVEL_WARN, 
      String.format("\n Op type: %s\n Op name: %s\n Timestamp: %d\n Callstack (top):\n%s\n Exception: %s\n", 
        this.opType == this.RETRY_CALLER_OP ? "retry" : "sleep",
        this.opName,
        this.timestamp,
        this.stackSnapshot.serializeTopFrames(5),
        this.exception
      )
    );
  }
}

class ExecutionTrace {

  private final Lock mutex = new ReentrantLock();
  private final int INFINITE_CACHE = -1; 

  private ArrayDeque<OpEntry> opCache;
  private int maxOpCacheSize;

  public ExecutionTrace() {
    this.opCache = new ArrayDeque<OpEntry>();
    this.maxOpCacheSize = this.INFINITE_CACHE;
  }

  public ExecutionTrace(int maxOpCacheSize) {
    this.opCache = new ArrayDeque<OpEntry>();
    this.maxOpCacheSize = maxOpCacheSize;
  }

  public Boolean isNullOrEmpty() {
    mutex.lock();
    try {
      return this.opCache == null || this.opCache.isEmpty();
    } finally {
      mutex.unlock();
    }
  }

  public int getMaxOpCacheSize() {
    mutex.lock();
    try {
      return this.maxOpCacheSize;
    } finally {
      mutex.unlock();
    }
  }

  public int getSize() {
    mutex.lock();
    try {
      return this.opCache.size();
    } finally {
      mutex.unlock();
    }
  }

  public void addLast(OpEntry opEntry) {
    mutex.lock();
    try {
      if (this.maxOpCacheSize != this.INFINITE_CACHE && this.opCache.size() >= this.maxOpCacheSize) {
        this.opCache.removeFirst();
      }
      this.opCache.addLast(opEntry);
    } finally {
      mutex.unlock();
    }
  }

  public Boolean checkIfOpsAreEqual(int leftIndex, int rightIndex) {
    mutex.lock();
    try {
      if (this.opCache.size() < Math.max(leftIndex, rightIndex)) {
        return false;
      }

      OpEntry leftOp = null;
      OpEntry rightOp = null;

      int index = this.opCache.size() - 1; 
      Iterator<OpEntry> itr = this.opCache.descendingIterator();
      while (itr.hasNext() && index >= Math.min(leftIndex, rightIndex)) {
        OpEntry current = itr.next();

        if (index == leftIndex) {
          leftOp = current;
        } else if (index == rightIndex) {
          rightOp = current;
        }

        --index;
      }
  
      return leftOp != null && rightOp != null && leftOp.isSameOp(rightOp);

    } finally {
      mutex.unlock();
    }
  }

  public Boolean checkIfOpIsOfType(int targetIndex, int targetOpType) {
    mutex.lock();
    try {
      if (this.opCache.size() < targetIndex) {
        return false;
      }

      OpEntry targetOp = null;

      int index = this.opCache.size() - 1; 
      Iterator<OpEntry> itr = this.opCache.descendingIterator();
      while (itr.hasNext() && index >= targetIndex) {
        OpEntry current = itr.next();

        if (index == targetIndex) {
          targetOp = current;
        }

        --index;
      }

      return targetOp != null && targetOp.isOfType(targetOpType);

    } finally {
      mutex.unlock();
    }
  }
  
  public Boolean checkIfOpHasFrame(int targetIndex, String targetFrame) {
    mutex.lock();
    try {
      if (this.opCache.size() < targetIndex) {
        return false;
      }

      OpEntry targetOp = null;

      int index = this.opCache.size() - 1; 
      Iterator<OpEntry> itr = this.opCache.descendingIterator();
      while (itr.hasNext() && index >= targetIndex) {
        OpEntry current = itr.next();

        if (index == targetIndex) {
          targetOp = current;
        }

        --index;
      }

      return targetOp != null && targetOp.hasFrame(targetFrame);

    } finally {
      mutex.unlock();
    }
  }

  public void printExecutionTrace(WasabiLogger log, String msg) {
    mutex.lock();
    try {
      log.printMessage(WasabiLogger.LOG_LEVEL_WARN, String.format("================================ %s", msg));
      for (OpEntry op : this.opCache) {
        op.printOpEntry(log);
      }
      log.printMessage(WasabiLogger.LOG_LEVEL_WARN, String.format("================================================================\n\n"));

    } finally {
      mutex.unlock();
    }
  }
}
