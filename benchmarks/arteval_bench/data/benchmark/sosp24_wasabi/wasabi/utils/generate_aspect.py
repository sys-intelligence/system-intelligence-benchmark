import argparse

def read_spec_file_to_dict(csv_file_path):
  with open(csv_file_path, 'r') as f:
    lines = f.readlines()
    lines = lines[1:]
    
    exception_map = {}
    for line in lines:
      tokens = line.strip().split("!!!")
      enclosing_method = tokens[1]
      retried_method = tokens[2]
      exception = tokens[4].strip().split(".")[-1]
      
      if exception not in exception_map:
        exception_map[exception] = []
      exception_map[exception].append((enclosing_method, retried_method))
  
  return exception_map

def generate_aspectj_code(exception_map):
  pointcut_code = ""
  for exception, method_pairs in exception_map.items():
    patterns = []
    
    patterns = [
      f"(withincode(* {enclosing}(..)) && call(* {retried}(..) throws *Exception*))"
      for enclosing, retried in method_pairs
    ]
    pointcut_body = " ||\n        ".join(patterns)

    pointcut_template = f"""
  /* Inject {exception} */

  pointcut inject{exception}():
    ({pointcut_body}) &&
    !within(edu.uchicago.cs.systems.wasabi.*);

  after() throws {exception} : inject{exception}() {{
    StackSnapshot stackSnapshot = new StackSnapshot();
    String retryCallerFunction = stackSnapshot.getSize() > 0 ? stackSnapshot.getFrame(0) : "???";
    String injectionSite = thisJoinPoint.toString();
    String retryException = "{exception}";
    String injectionSourceLocation = String.format("%s:%d",
                  thisJoinPoint.getSourceLocation().getFileName(),
                  thisJoinPoint.getSourceLocation().getLine());

    if (this.wasabiCtx == null) {{
      LOG.printMessage(
        WasabiLogger.LOG_LEVEL_WARN, 
        String.format("[Pointcut] [Non-Test-Method] Test ---%s--- | Injection site ---%s--- | Injection location ---%s--- | Retry caller ---%s---\\n",
          this.testMethodName, 
          injectionSite, 
          injectionSourceLocation, 
          retryCallerFunction)
      );

      return;
    }}

    LOG.printMessage(
      WasabiLogger.LOG_LEVEL_WARN, 
      String.format("[Pointcut] Test ---%s--- | Injection site ---%s--- | Injection location ---%s--- | Retry caller ---%s---\\n",
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
    if (ipt != null && this.wasabiCtx.shouldInject(ipt)) {{
      this.activeInjectionLocations.add(retryCallerFunction);
    
      long threadId = Thread.currentThread().getId();
      throw new {exception}(
        String.format("[wasabi] [thread=%d] [Injection] Test ---%s--- | ---%s--- thrown after calling ---%s--- | Retry location ---%s--- | Retry attempt ---%d---",
          threadId,
          this.testMethodName,
          ipt.retryException,
          ipt.injectionSite,
          ipt.retrySourceLocation,
          ipt.injectionCount)
      );
    }}
  }}
"""
    pointcut_code += pointcut_template
  
  pointcut_code = pointcut_code.replace("(    (within", "((within")
  pointcut_code = pointcut_code.replace(") ||\n) &&", ")) &&")

  code_template = f"""package edu.uchicago.cs.systems.wasabi;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/* Add imports specific to the exceptions thrown by the Aspect program */

import java.util.concurrent.ConcurrentHashMap;
import java.util.Set;

import edu.uchicago.cs.systems.wasabi.ConfigParser;
import edu.uchicago.cs.systems.wasabi.WasabiLogger;
import edu.uchicago.cs.systems.wasabi.WasabiContext;
import edu.uchicago.cs.systems.wasabi.InjectionPolicy;
import edu.uchicago.cs.systems.wasabi.StackSnapshot;
import edu.uchicago.cs.systems.wasabi.InjectionPoint;
import edu.uchicago.cs.systems.wasabi.ExecutionTrace;

public aspect Interceptor {{
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


  before() : testMethod() {{
    this.wasabiCtx = new WasabiContext(LOG, configParser);
    this.LOG.printMessage(
      WasabiLogger.LOG_LEVEL_WARN, 
      String.format("[TEST-BEFORE]: Test ---%s--- started", thisJoinPoint.toString())
    );

    if (this.testMethodName != this.UNKNOWN) {{
      this.LOG.printMessage(
        WasabiLogger.LOG_LEVEL_WARN, 
        String.format("[TEST-BEFORE]: [ALERT]: Test method ---%s--- executes concurrentlly with test method ---%s---", 
          this.testMethodName, thisJoinPoint.toString())
      ); 
    }}

    this.testMethodName = thisJoinPoint.toString();
  }}

  after() returning: testMethod() {{
    if (this.wasabiCtx == null) {{ // This happens for non-test methods (e.g. config) inside test code
      return; // Ignore retry in "before" and "after" annotated methods
    }}
    
    this.LOG.printMessage(
      WasabiLogger.LOG_LEVEL_WARN, 
      String.format("[TEST-AFTER]: [SUCCESS]: Test ---%s--- done", thisJoinPoint.toString())
    );

    this.wasabiCtx.printExecTrace(this.LOG, String.format(" Test: %s", this.testMethodName));

    this.testMethodName = this.UNKNOWN;
    this.wasabiCtx = null;
    this.activeInjectionLocations.clear();
  }}

  after() throwing (Throwable t): testMethod() {{
    if (this.wasabiCtx == null) {{ // This happens for non-test methods (e.g. config) inside test code
      return; // Ignore retry in "before" and "after" annotated methods
    }}
    
    this.wasabiCtx.printExecTrace(this.LOG, String.format(" Test: %s", this.testMethodName));

    StringBuilder exception = new StringBuilder();
    for (Throwable e = t; e != null; e = e.getCause()) {{
      exception.append(e);
      exception.append(" :-: ");
    }}

    StackSnapshot stackSnapshot = new StackSnapshot();
    this.LOG.printMessage(
      WasabiLogger.LOG_LEVEL_WARN, 
      String.format("[TEST-AFTER] [FAILURE] Test ---%s--- | Failure message :-: %s| Stack trace:\\n%s\\n:-:-:\\n\\n", 
          thisJoinPoint.toString(), exception.toString(), stackSnapshot.toString())
    );
     
    this.testMethodName = this.UNKNOWN;
    this.activeInjectionLocations.clear();
  }}

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

  before() : recordThreadSleep() {{
    try {{
      if (this.wasabiCtx == null) {{ // This happens for non-test methods (e.g. config) inside test code
        return; // Ignore retry in "before" and "after" annotated methods
      }}
    
      StackSnapshot stackSnapshot = new StackSnapshot();  
      for (String retryCallerFunction : this.activeInjectionLocations) {{
        if (stackSnapshot.hasFrame(retryCallerFunction.split("\\\\(", 2)[0])) {{
          String sleepLocation = String.format("%s(%s:%d)",
                      retryCallerFunction.split("\\\\(", 2)[0],
                      thisJoinPoint.getSourceLocation().getFileName(),
                      thisJoinPoint.getSourceLocation().getLine());

          this.wasabiCtx.addToExecTrace(sleepLocation, OpEntry.THREAD_SLEEP_OP, stackSnapshot);
          LOG.printMessage(
            WasabiLogger.LOG_LEVEL_WARN, 
            String.format("[THREAD-SLEEP] Test ---%s--- | Sleep location ---%s--- | Retry location ---%s---\\n",
              this.testMethodName, 
              sleepLocation, 
              retryCallerFunction.split("\\\\(", 2)[0])
          );
        }}
      }}
    }} catch (Exception e) {{
      this.LOG.printMessage(
        WasabiLogger.LOG_LEVEL_ERROR, 
        String.format("Exception occurred in recordThreadSleep(): %s", e.getMessage())
      );
      e.printStackTrace();
    }}
  }}

  {pointcut_code}
}}"""

  return code_template

def main():
  parser = argparse.ArgumentParser(description="Generate AspectJ code following a particular specification.")
  parser.add_argument("--spec-file", help="Path to the input specification file")
  parser.add_argument("--aspect-file", help="Path to the output AspectJ file")
  
  args = parser.parse_args()
  
  exception_map = read_spec_file_to_dict(args.spec_file)
  code = generate_aspectj_code(exception_map)

  with open(args.aspect_file, "w") as f:
    f.write(code)

if __name__ == "__main__":
  main()
