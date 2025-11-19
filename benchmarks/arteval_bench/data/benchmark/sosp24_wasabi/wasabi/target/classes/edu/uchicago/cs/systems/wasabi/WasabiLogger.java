package edu.uchicago.cs.systems.wasabi;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

class WasabiLogger {
  private final Logger LOG = LoggerFactory.getLogger(WasabiLogger.class);

  public static final int LOG_LEVEL_INFO = 1;
  public static final int LOG_LEVEL_WARN = 2;
  public static final int LOG_LEVEL_DEBUG = 3;
  public static final int LOG_LEVEL_ERROR = 4;

  public synchronized void printMessage(int logLevel, String msg) {
    long timestamp = System.nanoTime();
    long threadId = Thread.currentThread().getId();

    switch(logLevel) {
      case LOG_LEVEL_INFO:
        LOG.info("[wasabi] [" + timestamp + "] [thread=" + threadId + "] " + msg);
        break;
      case LOG_LEVEL_WARN:
        LOG.warn("[wasabi] [" + timestamp + "] [thread=" + threadId + "] " + msg);
        break;
      case LOG_LEVEL_DEBUG:
        LOG.debug("[wasabi] [" + timestamp + "] [thread=" + threadId + "] " + msg);
        break;
      case LOG_LEVEL_ERROR:
        LOG.error("[wasabi] [" + timestamp + "] [thread=" + threadId + "] " + msg);
        break;
    }
  }
}
