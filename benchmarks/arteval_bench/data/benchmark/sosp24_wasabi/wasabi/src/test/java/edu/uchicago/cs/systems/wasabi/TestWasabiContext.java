package edu.uchicago.cs.systems.wasabi;

import edu.uchicago.cs.systems.wasabi.InjectionPoint;
import edu.uchicago.cs.systems.wasabi.WasabiContext;
import edu.uchicago.cs.systems.wasabi.WasabiLogger;

import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import static org.junit.Assert.*;

public class TestWasabiContext {
  
  private final WasabiLogger LOG = new WasabiLogger();
  
  private final String testConfigFile = "./_test.conf";
  private final String testRetryDataFile = "./_test_retry_locations.data";
  private final String testRetryPolicy = "max-count";
  private final int testMaxCount = 42;

  private ConfigParser configParser;
  
  private void generateConfigFile() {
    try (FileWriter writer = new FileWriter(this.testConfigFile)) {
      writer.append("retry_data_file: " + this.testRetryDataFile + "\n");
      writer.append("injection_policy: " + this.testRetryPolicy + "\n");
      writer.append("max_injection_count: " + String.valueOf(this.testMaxCount) + "\n");
    } catch (IOException e) {
      this.LOG.printMessage(
          LOG.LOG_LEVEL_ERROR, 
          String.format("[wasabi] Error occurred while generating the retry data file: %s", e.getMessage())
        );
      e.printStackTrace();
    }
  }

  private void generateDataRetryFile() {
    StackSnapshot stackSnapshot = new StackSnapshot();
    String[][] records = {
        {
          "test_retry_location:TestWasabiContext.javaL#0", // retry location 
          StackSnapshot.getQualifiedName(stackSnapshot.getFrame(1)), // enclosing method
          StackSnapshot.getQualifiedName(stackSnapshot.getFrame(0)), // retried method 
          "SocketException", // exception
          "1.0", // injection probability
          "0" // test coverage metrics
        }
      };

    try (FileWriter writer = new FileWriter(this.testRetryDataFile)) {
      writer.append("Retry location!!!Enclosing method!!!Retried method!!!Exception!!!Injection probability!!!Test coverage\n");

      for (String[] record : records) {
        writer.append(
            String.format("%s!!!%s!!!%s!!!%s!!!%s!!!%s\n", record[0], record[1], record[2], record[3], record[4], record[5])
          );
      }
    } catch (IOException e) {
      this.LOG.printMessage(
          LOG.LOG_LEVEL_ERROR, 
          String.format("[wasabi] Error occurred while generating the retry data file: %s", e.getMessage())
        );
      e.printStackTrace();
    }
  }

  @Before
  public void startUp() {
    generateConfigFile();
    generateDataRetryFile();
    this.configParser = new ConfigParser(LOG, testConfigFile);
  }

  /*
  @Test
  public void testShouldInject() {
    WasabiContext wasabiCtx = new WasabiContext(this.LOG, this.configParser);
    InjectionPoint validInjectionPoint = wasabiCtx.getInjectionPoint();
    
    assertTrue(validInjectionPoint != null);
    assertTrue(wasabiCtx.shouldInject(validInjectionPoint));
    
    StackSnapshot stackSnapshot = new StackSnapshot();
    InjectionPoint invalidInjectionPoint = new InjectionPoint(
        stackSnapshot,
        "FakeRetryLocation",
        "FakeRetryCaller",
        "FakeRetriedCallee",
        "FakeException",
        100  // injection count
      );

    assertFalse(wasabiCtx.shouldInject(invalidInjectionPoint));
  }
  */

  /*
  @Test
  public void testUpdateInjectionCount() {
    WasabiContext wasabiCtx = new WasabiContext(this.LOG, this.configParser);
    InjectionPoint ipt = wasabiCtx.getInjectionPoint(); // new injection point
    int initialCount = ipt.injectionCount;

    ipt = wasabiCtx.getInjectionPoint(); // new injeciton point, same retry context
    assertTrue(wasabiCtx.shouldInject(ipt));
    assertEquals(initialCount + 1, ipt.injectionCount.intValue());

    StackSnapshot stackSnapshot = new StackSnapshot();
    int uniqueId = HashingPrimitives.getHashValue(stackSnapshot.normalizeStackBelowFrame(stackSnapshot.getFrame(1)));
    wasabiCtx.addToExecTrace(uniqueId, OpEntry.THREAD_SLEEP_OP, stackSnapshot); // some sleep operations in between
    wasabiCtx.addToExecTrace(uniqueId, OpEntry.THREAD_SLEEP_OP, stackSnapshot);
    wasabiCtx.addToExecTrace(uniqueId, OpEntry.THREAD_SLEEP_OP, stackSnapshot);

    ipt = wasabiCtx.getInjectionPoint(); // new injeciton point, same retry context
    assertTrue(wasabiCtx.shouldInject(ipt));
    assertEquals(initialCount + 2, ipt.injectionCount.intValue());
  }
  */

  @After
  public void tearDown() {
    try {
      Path path = Paths.get(this.testRetryDataFile);
      Files.deleteIfExists(path);

      path = Paths.get(this.testConfigFile);
      Files.deleteIfExists(path);

    } catch (IOException e) {
      this.LOG.printMessage(
          LOG.LOG_LEVEL_ERROR, 
          String.format("[wasabi] Error occurred while deleting test configuration files: %s", e.getMessage())
        );
      e.printStackTrace();
    }
  }
}