import argparse
from collections import defaultdict
import os
import re

class LogMessage:
  def __init__(self) -> None:
    self.type = None
    self.timestamp = None
    self.test_name = None
    self.injection_site = None
    self.injection_location = None
    self.retry_caller = None
    self.exception_injected = None
    self.retry_attempt = None
    self.sleep_location = None
    self.failure_string = None
    self.failure_exceptions = None
    self.stack_trace = None

  def parse_log_message(self, log_message: str, is_test_report: True) -> None:
    """Parses a single log message string and populates the LogMessage object's attributes.

    Args:
      log_message (str): A string containing a log message.
    """

    if is_test_report:
      if "[wasabi]" in log_message:
        tokens = log_message.split(" | ")
        self.test_name = self.get_test_name(tokens[0], True)
        if "[Pointcut]" in tokens[0]:
          self.parse_pointcut_message(tokens)
        elif "[Injection]" in tokens[0]:
          self.parse_injection_message(tokens)
        elif "[THREAD-SLEEP]" in tokens[0]:
          self.parse_sleep_message(tokens)
        elif "[FAILURE]" in tokens[0]:
          self.parse_failure_message(log_message)
    else:
      if "[ERROR]" in log_message:
        self.type = "error"
        self.test_name = self.get_test_name(log_message, False)
        self.stack_trace = self.get_error_details(log_message)

  def get_test_name(self, log_message: str, is_test_report) -> str:
    """Extracts the test name from an error log message.

    Args:
      log_message (str): A string containing an error log message.
    """
    test_name = "UNKNOWN"
    if is_test_report:
      token = self.get_value_between_separators(log_message, "---", "---")
      if token: 
        match = re.search(r'\w+\(.*\s+(.*\(.*?\))\)', token)
        test_name = match.group(1).split("(")[0] if match else test_name
        test_name = re.sub(r'[^\w.]+.*$', '', test_name)
        tokens = test_name.split('.')
        if len(tokens) >= 2:
            test_name = '.'.join(tokens[-2:])
    else:
      for token in log_message.split(" "):
        if "test" in token:
          test_name = re.sub(r'[^\w.]+.*$', '', token)
          break
    return test_name

  def get_error_details(self, log_message: str) -> str:
    """Extracts the failure string and stack trace from an error log message.

    Args:
      log_message (str): A string containing an error log message.
    """
    self.failure_string = ""
    stack_found = False
    stack = []
    for line in log_message.split("\n"):
      if line.strip().startswith("at "):
        stack.append(line.strip().split("at ")[1])
        stack_found = True
      elif not stack_found:
        self.failure_string += line + "\n"
      else:
        break # Stop if stack trace processing is complete
    norm_stack = self.normalize_stack_trace(stack)
    return norm_stack

  def normalize_stack_trace(self, stack_trace: [str]) -> str:
    """Normalizes the stack trace for a given test failure by removing
    top frames that correspond to Java standard libraries.

    Args:
      stack_trace (str): The stack trace for a particular test failure.

    Returns:
      str: The normalized stack trace, if it exists.
    """
    javalib_frames_prefixes = ["java.", "jdk.", "org.junit.", "sun.", "oracle.", 
                               "app//org.mockito.", "app//org.slf4j.", 
                               "org.apache.maven.surefire."]
    norm_stack_trace = []
    for frame in stack_trace:
      if not any(frame.startswith(prefix) for prefix in javalib_frames_prefixes):
        norm_stack_trace.append(frame.strip())
    return "\n".join(norm_stack_trace)

  def parse_pointcut_message(self, tokens: list) -> None:
    """Parses a pointcut log message and populates the LogMessage object's attributes.

    Args:
      tokens (list): A list of string tokens derived from the log message.
    """
    self.type = "pointcut"
    self.injection_site = self.get_injection_site(tokens[1])
    self.injection_location = self.get_value_between_separators(tokens[2], "---", "---")
    self.retry_caller = self.get_value_between_separators(tokens[3], "---", "---")

  def parse_injection_message(self, tokens: list) -> None:
    """Parses an injection log message and populates the LogMessage object's attributes.

    Args:
      tokens (list): A list of string tokens derived from the log message.
    """
    self.type = "injection"
    self.exception_injected = self.get_value_between_separators(tokens[1].split("thrown after calling")[0], "---", "---")
    self.injection_site = self.get_injection_site(tokens[1].split("thrown after calling")[1])
    self.retry_caller = self.get_value_between_separators(tokens[2], "---", "---")
    self.retry_attempt = int(self.get_value_between_separators(tokens[3], "---", "---"))

  def parse_sleep_message(self, tokens: list) -> None:
    """Parses a sleep log message and populates the LogMessage object's attributes.

    Args:
      tokens (list): A list of string tokens derived from the log message.
    """
    self.type = "sleep"
    self.sleep_location = self.get_value_between_separators(tokens[1], "---", "---")
    self.retry_caller = self.get_value_between_separators(tokens[2], "---", "---")

  def parse_failure_message(self, log_message: str):
    """Parses a failure log message and populates the LogMessage object's attributes.

    Args:
      log_message (str): A string containing a log message.
      
    """
    if "Failure message" in log_message and "Stack trace:" in log_message:
      self.type = "failure"
      self.failure_string = re.search(r'Failure message :-: (.*?) :-: \| Stack trace:', log_message, re.S).group(1)
      self.failure_exceptions = self.extract_failure_exception(self.failure_string)

  def extract_failure_exception(self, log_message: str) -> set:
    """
    Extracts the failure exceptions from the failure log message.

    Args:
      log_message (str): A string containing a log message.

    Returns:
      list: A list of exceptions in the failure message.
    """
    exceptions = set()
    tokens = log_message.split(":-:")

    for token in tokens:
      # Estract fully qualified Java exceptions
      java_exceptions = re.findall(r'java\.[a-zA-Z]+\.[a-zA-Z]+Exception', token)
      exceptions.update(java_exceptions)
      
      # Extract fully qualified Apache exceptions
      org_exceptions = re.findall(r'org\.[a-zA-Z]+\.[a-zA-Z]+Exception', token)
      exceptions.update(org_exceptions)
      
      # Extract truncated or unqalified exception names
      norm_exceptions = re.findall(r'[a-zA-Z]+Exception', token)
      exceptions.update(norm_exceptions)
    
    norm_exceptions = {e.strip(' \t\n:.') for e in exceptions}
    return norm_exceptions

  def get_injection_site(self, token: str) -> str:
    """Extracts the injection site from the token.

    Args:
      token (str): A string token derived from the log message.

    Returns:
      str: The extracted injection site or 'UNKNOWN' if not found.
    """
    match = re.search(r'\w+\(.*\s+(.*\(.*?\))\)', self.get_value_between_separators(token, "---", "---"))
    if match:
      return match.group(1).split("(")[0]
    return "UNKNOWN"

  @staticmethod
  def get_value_between_separators(text: str, start_sep: str, end_sep: str) ->  list[str]:
    """Extracts a value between two separators from a given text.

    Args:
      text (str): The text containing the separators.
      start_sep (str): The starting separator.
      end_sep (str): The ending separator.

    Returns:
      str: The extracted value or None if not found.
    """
    try:
      return text.split(start_sep)[1].split(end_sep)[0].strip()
    except IndexError:
      return None


def parse_build_log(file_path: str) -> list:
  """Parses a single build log file, handles errors, and parses the relevant log messages.

  Args:
    file_path (str): Path to the build log file.

  Returns:
    list[LogMessage]: A list of LogMessage objects parsed from the log file.
  """
  timeout_messages = ["TimeoutException", 
                     "TimeoutIOException", 
                     "SocketTimeoutException", 
                     "TestTimedOut", 
                     "[ERROR] There was a timeout"]

  with open(file_path, "r") as file:
    lines = file.readlines()

  log_messages = []
  log_timeout_messeges = []

  index = 0
  while index < len(lines):
    if "[ERROR]" in lines[index] and "test" in lines[index]:
      offset = index
      log_message = ""
      while index < len(lines) and (lines[index].strip().startswith("at ") or ((index - offset + 1) <= 50)):
        log_message += lines[index].strip() + "\n"
        index += 1

      log_msg = LogMessage()
      log_msg.parse_log_message(log_message, False)
      log_msg.test_name = file_path.split('build-')[1].split('.')[0] + "." + log_msg.test_name.split(".")[-1]
      log_messages.append(log_msg)

      if index < len(lines) and any(exception in lines[index] for exception in timeout_messages):
        log_timeout_messeges.append(lines[index])
      if index < len(lines) and any(exception in log_msg.stack_trace for exception in timeout_messages):
        log_timeout_messeges.append(lines[index])
    else:
      index += 1

  return log_messages, log_timeout_messeges

def parse_test_log(file_path: str) -> list:
  """Parses a single test report log file to extract log messages.

  Args:
    file_path (str): Path to the test report log file.

  Returns:
    list[LogMessage]: A list of LogMessage objects parsed from the log file.
  """
  log_messages = []
  with open(file_path, 'r') as file:
    log_data = file.read()
    log_entries = log_data.strip().split("\n")
    for entry in log_entries:
      msg = LogMessage()
      msg.parse_log_message(entry, True)
      log_messages.append(msg)
 
  return log_messages

def error_in_test_code(op: LogMessage) -> bool:
  """Determines if a particular failure log message and call stack
  indicate a false positive or a true retry bug.

  Args:
    failure_exception (str): The failure exception thrown by the test.
    stack_trace (list[str]): The failing call stack.

  Returns:
    bool: 'True' if error is located in test code, 'False' otherwise.
  """
  test_frames_patterns = ["Test", ".test", "MiniYARNCluster", "MiniDFSCluster", "MiniRouterDFSCluster", ".doBenchmark("]
  if op.stack_trace and len(op.stack_trace) > 0:
    for pattern in test_frames_patterns:
      if pattern in op.stack_trace[0]:
        return True

  test_code_exceptions = [".TimeoutException", ".TimeoutIOException", ".AssertionError", ".AssertionFailedError", 
                          ".ComparisonError", ".ComparisonFailure", ".AssumptionViolatedException", ".InterruptedException",  
                          ".InterruptedIOException", ".AssumptionViolatedException", ".DoNotRetry", ".DoNotRetryTest",
                          "org.mockito.exceptions", "java.lang.RuntimeException"]
  for e in test_code_exceptions:
    if e in op.failure_string:
      return True

  return False

def check_how_bugs(test_failures: dict(), execution_trace: defaultdict(list)) -> set:
  """Searches for HOW bugs by parsing test reports for logged failures with a different exception
   than the one injected by WASAI.

  Args:
    log_messages (list[LogMessage]): A list of LogMessage objects parsed from a single log file.

  Returns:
    set: A set of tuples with HOW buggy retry locations and a 'how-bug' tag.
  """
  how_bugs = set()

  for test_name, operations in execution_trace.items():
    last_injection_op = None
    
    for op in operations:
      # Skip if error in test code
      if op.test_name in test_failures and error_in_test_code(test_failures[op.test_name]):
        continue
      if op.type == "injection":
        last_injection_op = op
      elif op.type == "failure":
        if last_injection_op is None or any(last_injection_op.exception_injected in exception for exception in op.failure_exceptions):
          continue
        elif error_in_test_code(op) or "| Retry attempt ---" in op.failure_string:
          continue
        else:
          how_bugs.add(("how-bug", last_injection_op))
        last_injection_op = None
 
  return how_bugs

def check_when_missing_backoff_bugs(execution_trace: defaultdict(list)) -> set:
  """Searches for WHEN missing bacckof retry bugs by parsing test repors and checking for consecutive retry
   attempts where WASABI did not record any Thread.sleep-like call.

  Args:
    log_messages (list[LogMessage]): A list of LogMessage objects parsed from a single log file.

  Returns:
    set: A set of tuples with WHEN missing backoff buggy retry locations ahd a 'when-missing-backoff' tag
  """
  when_missing_backoff_bugs = set()

  for test_name, operations in execution_trace.items():
    max_op = None
    has_sleep = False
    max_retry_attempts = 0
    for op in operations:
      if op.type == "sleep":
        has_sleep = True
      elif op.type == "injection" and max_retry_attempts < op.retry_attempt:
        max_retry_attempts = op.retry_attempt
        max_op = op

    if not has_sleep and max_retry_attempts >= 2:
      when_missing_backoff_bugs.add(("when-missing-backoff", max_op))

  return when_missing_backoff_bugs

def check_when_missing_cap_bugs(execution_trace: defaultdict(list)) -> set:
  """Searches for WHEN missing cap retry bugs by parsing test repors and checking if WASABI can 
   inject a large number of exceptions that indicate infinite retry attempts.

  Args:
    log_messages (list[LogMessage]): A list of LogMessage objects parsed from a single log file.

  Returns:
    set: A set of tuples with WHEN missing cap buggy retry locations ahd a 'when-missing-cap' tag
  """
  MISSING_CAP_BOUND = 90
  when_missing_cap = set()

  for test_name, operations in execution_trace.items():
    for op in operations:
      if op.type == "injection" and op.retry_attempt >= MISSING_CAP_BOUND:
        when_missing_cap.add(("when-missing-cap", op))

  return when_missing_cap

def check_when_missing_cap_timeouts(execution_trace: defaultdict(list), test_timeouts: dict()) -> set:
  """Searches for WHEN missing cap retry bugs by parsing test repors and checking if WASABI injects
  a large 

  Args:
    log_messages (list[LogMessage]): A list of LogMessage objects parsed from a single log file.

  Returns:
    set: A set of tuples with WHEN missing cap buggy retry locations ahd a 'when-missing-cap' tag
  """
  MISSING_CAP_BOUND = 5
  timeout_retry_locations = ["org.apache.hadoop.hbase.backup.HFileArchiver.resolveAndArchiveFile",
                             "org.apache.hadoop.hbase.io.asyncfs.FanOutOneBlockAsyncDFSOutputHelper.completeFile",
                             "org.apache.hadoop.hbase.master.replication.SyncReplicationReplayWALProcedure.executeFromState",
                             "org.apache.hadoop.hbase.regionserver.RemoteProcedureResultReporter.run",
                             "org.apache.hadoop.hbase.regionserver.wal.DualAsyncFSWAL.createWriterInstance",
                             "org.apache.hadoop.hbase.replication.regionserver.ReplicationSource.initialize",
                             "org.apache.hadoop.hbase.shaded.protobuf.generated.RPCProtos$ExceptionResponse$Builder.mergeFrom",
                             "org.apache.hadoop.hbase.util.FSUtils.setClusterId",
                             "org.apache.hadoop.hdfs.server.namenode.ReencryptionUpdater.takeAndProcessTasks"]
  
  when_missing_cap_timeout = set()

  for test_name, operations in execution_trace.items():
    for op in operations:
      if op.type == "injection" and op.retry_attempt >= MISSING_CAP_BOUND:
        test_class = test_name
        if len(test_name.split(".")) > 1:
          test_class = test_name.split(".")[0]
        if test_class in test_timeouts and op.retry_caller in timeout_retry_locations:
          when_missing_cap_timeout.add(("when-missing-cap", op))

  return when_missing_cap_timeout

def main():
  parser = argparse.ArgumentParser(description="Parse and process log files for retry bug analysis.")
  parser.add_argument("logs_root_dir", type=str, help="The root directory where build/test logs are saved")
  parser.add_argument("--benchmark", choices=["hadoop", "hbase", "hive", "cassandra", "elasticsearch", "all-maven"], required=True, help="The benchmark to run")
  args = parser.parse_args()
  root_path = args.logs_root_dir

  test_timeouts = dict()
  test_failures = dict()
  all_bugs = set()
  coverage = set()

  for root, _, files in os.walk(os.path.join(root_path, "build-reports/")):
    for fname in files:
      if "build-" in fname and fname.endswith('.log'):
        build_log_messages, build_log_timeout_messages = parse_build_log(os.path.join(root, fname))
        
        for msg in build_log_messages:
          test_failures[msg.test_name] = msg

        test_class = fname.split(".")[-2]
        test_timeouts[test_class] = build_log_timeout_messages

  for root, _, files in os.walk(os.path.join(root_path, "test-reports/")):
    for fname in files:
      if fname.endswith('-output.txt'):
        test_log = parse_test_log(os.path.join(root, fname))
        execution_trace = defaultdict(list)
        
        for msg in test_log:
          if msg.type in ["injection", "sleep", "failure"]:
            execution_trace[msg.test_name].append(msg)
          if msg.type == "pointcut":
            coverage.update([f"test-injected,{msg.test_name}"])
        
        all_bugs.update(check_when_missing_backoff_bugs(execution_trace))
        all_bugs.update(check_when_missing_cap_bugs(execution_trace))
        all_bugs.update(check_how_bugs(test_failures, execution_trace))
        all_bugs.update(check_when_missing_cap_timeouts(execution_trace, test_timeouts))

  print("// ----------------------------- //")
  print(f"   Retry bugs for {args.benchmark}")
  print("// ----------------------------- //")
  for bug_no, bug in enumerate(all_bugs, 1):
    bug_type, op = bug
    print(f"bug-{bug_no},{bug_type},{op.retry_caller},{op.test_name}")

  bug_file = os.path.join(root_path, f"{args.benchmark}-bugs-per-test.csv")
  with open(bug_file, "w") as f:
    for bug_no, bug in enumerate(all_bugs, 1):
      bug_type, op = bug
      f.write(f"bug-{bug_no},{bug_type},{op.retry_caller},{op.test_name}\n")

  cov_file = os.path.join(root_path, f"{args.benchmark}-cov.csv")
  with open(cov_file, "w") as f:
    for cov_msg in coverage:
      f.write(f"{cov_msg}\n")

if __name__ == "__main__":
  main()