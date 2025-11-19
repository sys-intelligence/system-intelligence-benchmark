import argparse
from collections import deque
import datetime
import glob
import os
import re
import shutil
import subprocess
import time
import sys


LOG_FILE_NAME = "wasabi-install.log"
TIMEOUT = 3600


def run_command_with_timeout(cmd: list[str], dir_path: str):
  """
  Run a command with a timeout of {TIMEOUT} seconds.

  Parameters:
    cmd (list): The command to run as a list of arguments.
    timeout (int): The timeout in seconds.

  Returns:
    subprocess.CompletedProcess: The result of the command execution.
  """
  try:
    result = subprocess.run(cmd, cwd=dir_path, shell=False, capture_output=True, timeout=TIMEOUT)
    return result
  except subprocess.TimeoutExpired:
    return None


def get_conf_files(config_dir: str):
  """
  Find all config files (extension ".conf").

  Parameters:
    config_dir (str): The path of the config directory.

  Returns:
    list: A list of strings containing the paths of the ".conf" files.
  """
  return glob.glob(os.path.join(config_dir, "*.conf"))


def get_test_file_name(config_file: str):
  """
  Extracts the test name from its corresponding config file.

  Parameters:
    config_file (str): The path of the config file.

  Returns:
    str: The path of the log file for the config file.
  """
  test_name = re.search(r"retry_locations-(.+?)\.conf", config_file).group(1)

  return test_name


def get_log_file_name(target_root_dir: str, test_path: str):
  """
  Constructs the log file name from the config file.

  Parameters:
    target_root_dir (str): The path of the config directory.
    config_file (str): The path of the config file.

  Returns:
    str: The path of the log file for the config file.
  """
  test_name = get_test_file_name(test_path)
  log_file_name = f"build-{test_name}.log"
  return os.path.join(target_root_dir, log_file_name)


def build_target(target: str, target_root_dir: str, wasabi_arg: str = None):
  """
  Build a target application.

  Parameters:
    target (str): The name of the target application.
    target_root_dir (str): The path of the target root directory.
    arg (str): The path of the log file.
  """
  if target == "wasabi": 
    cmd = ["mvn", "clean", "install", "-fn", "-B", "-U", "-DskipTests", f"-Dinstrumentation.target={wasabi_arg}"]
  elif target == "hive":
    cmd = ["mvn", "clean", "install", "-Pdist", "-fn", "-Drat.numUnapprovedLicenses=20000", "-B", "-U", "-DskipTests"]
  elif target == "cassandra":
    cmd = ["ant"]
  elif target == "elasticsearch":
    cmd = ["./gradlew", "clean", "publishToMavenLocal", "-x", "test"]
  else:
    cmd = ["mvn", "clean", "install", "-fn", "-B", "-U", "-DskipTests"]

  print("// -------------------------------------------------------------------------- //")
  print(f"Active directory: {target_root_dir}")
  print(f"Command: {' '.join(cmd)}", flush=True)

  result = subprocess.run(cmd, cwd=target_root_dir, shell=False, capture_output=True)
  
  print(f"Status: {result.returncode}", flush=True)
  print("// -------------------------------------------------------------------------- //\n")

  log_file_path = os.path.join(target_root_dir, LOG_FILE_NAME)
  with open(log_file_path, "a", encoding="utf-8") as outfile:
    outfile.write(result.stdout.decode('utf-8'))
    outfile.write((result.stderr.decode('utf-8')))


def run_test_suite(target: str, target_root_dir: str, args: str):
  """
  Run test suite for a target application.

  Parameters:
    target (str): The name of the target application.
    conf_files (list): A list of strings containing the paths of the ".conf" files.
    args (str): A set of arguments to be added to the command.

  Returns:
    list: A list of tuples containing the outcome and duration of each thread.
  """
  cmd_queue = deque()
  for config_file, test_name in args:
    cmd_queue.append((config_file, test_name))
  
  total_cmds = len(cmd_queue)
  counter = 0
  while cmd_queue:
    counter += 1

    config_file, test_name = cmd_queue.popleft()
    log_file = get_log_file_name(target_root_dir, config_file)
    
    if target == "hive":
      cmd = ["mvn", "surefire:test", "-B", "-Drat.numUnapprovedLicenses=20000", f"-DconfigFile={config_file}", f"-Dtest={test_name}", "-fn"]
    elif target == "cassandra":
      cmd = ["ant", f"-Dtest={test_name}", "test"]
    elif target == "elasticsearch":
      cmd = ["./gradlew", f"test --tests {test_name}", f"-DconfigFile={config_file}"]
    else:
      cmd = ["mvn", "surefire:test", "-B", f"-DconfigFile={config_file}", f"-Dtest={test_name}", "-fn"]

    print("// -------------------------------------------------------------------------- //")
    print(f"Job count: {counter} / {total_cmds}")
    print(f"Command: {' '.join(cmd)}")
    print(f"Active directory: {target_root_dir}")
    print(f"Config file: {config_file}")
    print(f"Log file: {log_file}", flush=True)

    result = run_command_with_timeout(cmd, target_root_dir)

    if result is not None:
      print(f"Status: {result.returncode}", flush=True)
      print("// -------------------------------------------------------------------------- //\n")

      with open(log_file, "a", encoding="utf-8") as outfile:
        outfile.write(result.stdout.decode('utf-8'))
        outfile.write(result.stderr.decode('utf-8'))
    
    else:
      print(f"Status: timeout -- TimeoutExpired exception", flush=True)
      print("// -------------------------------------------------------------------------- //\n")


def cleanup(build_system: str):
  """
  Clean up of local package directory.
  """
  
  if build_system == "maven" or build_system == "gradle":
   package_dir = os.path.expanduser("~/.m2")
  elif build_system == "ant":
   package_dir = os.path.expanduser("~/.ivy2") 
  
  cmd = ["rm", "-rf", package_dir]

  print("// -------------------------------------------------------------------------- //")
  print(f"Command: {' '.join(cmd)}", flush=True)

  result = run_command_with_timeout(cmd, dir_path=os.path.expanduser("~"))

  if result is None:
    print(f"Command timed out while trying to remove {package_dir}.", flush=True)
  else:
    print(f"Status: {result.returncode}", flush=True)
  print("// -------------------------------------------------------------------------- //\n")


def save_log_files(target_app: str, wasabi_root_dir: str):
  """
  Save test and build log files to a separate directory.

  Parameters:
    wasabi_root_dir (str): The path of the Wasabi root directory.
    target_app (str): The target application name for which logs will be saved.
  """
  wasabi_results_dir = os.path.join(wasabi_root_dir, "..", "results", target_app)
  target_root_dir = os.path.join(wasabi_root_dir, "..", "benchmarks", target_app)

  date = datetime.datetime.now().strftime("%Y%m%d%H%M")
  
  # Save test reports
  test_reports_dir = os.path.join(wasabi_results_dir, date, "test-reports")
  os.makedirs(test_reports_dir, exist_ok=True)
  for dirpath, _, files in os.walk(target_root_dir):
    for file in files:
      if file.endswith("-output.txt"):
        output_file = os.path.join(dirpath, file)
        shutil.copy(output_file, os.path.join(test_reports_dir, f"{date}.{file}"))

  # Save build reports
  build_reports_dir = os.path.join(wasabi_results_dir, date, "build-reports")
  os.makedirs(build_reports_dir, exist_ok=True)
  for file in os.listdir(target_root_dir):
    if file.startswith("build-") and file.endswith(".log"):
      output_file = os.path.join(target_root_dir, file)
      shutil.copy(output_file, os.path.join(build_reports_dir, f"{date}.{file}"))


def main():
  parser = argparse.ArgumentParser()
  parser.add_argument("--benchmark", choices=["hadoop", "hbase", "hive", "cassandra", "elasticsearch"], required=True, help="The benchmark to run")
  args = parser.parse_args()
  
  wasabi_root_dir = os.getenv("WASABI_ROOT_DIR")
  if not wasabi_root_dir:
    print("[WASABI-HELPER]: [ERROR]: The WASABI_ROOT_DIR environment variable is not set.")
    sys.exit(1)
  
  target_root_dir = os.path.join(wasabi_root_dir, "..", "benchmarks", args.benchmark)
  config_dir = os.path.join(wasabi_root_dir, "wasabi-testing", "config", args.benchmark, "test-plan")

  conf_files = get_conf_files(config_dir)
  test_names = [get_test_file_name(config_file) for config_file in conf_files]
  configs = [(conf_file, test_name) for conf_file, test_name in zip(conf_files, test_names)]

  # Cleanup old packages
  if args.benchmark == "cassandra":
    cleanup("ant")
  elif args.benchmark == "elasticsearch":
    cleanup("gradle")
  else:
    cleanup("maven")

  # Build and install WASABI
  build_target("wasabi", os.path.join(wasabi_root_dir, "wasabi-testing"), args.benchmark)

  # Build and install the target application
  build_target(args.benchmark, target_root_dir)

  start_time = time.perf_counter()

  # Run the test suite of the target application
  run_test_suite(args.benchmark, target_root_dir, configs)
  
  end_time = time.perf_counter()
  print(f"\n\n// -------------------------------------------------------------------------- //")
  print(f"End-to-end running time: {end_time - start_time} secs")

  # Save logs to a separate directory
  save_log_files(args.benchmark, wasabi_root_dir)

if __name__ == "__main__":
  main()
