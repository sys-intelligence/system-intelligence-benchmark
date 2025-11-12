import argparse
import datetime
import os
import shutil
import subprocess
import sys


""" Evaluation phases
"""
def clone_repositories(root_dir: str, benchmark: str):
  """
  Clone the necessary repositories and checkout specific versions for the specified benchmarks.

  Arguments:
    root_dir (str): The root directory of the repository.
    benchmark_list (list): A list of target applications to clone.
  """
  repos = {
    "hadoop": ("https://github.com/apache/hadoop.git", "60867de"),
    "hbase": ("https://github.com/apache/hbase.git", "89ca7f4"),
    "hive": ("https://github.com/apache/hive.git", "e08a600"),
    "cassandra": ("https://github.com/apache/cassandra.git", "f0ad7ea"),
    "elasticsearch": ("https://github.com/elastic/elasticsearch.git", "5ce03f2"),
  }
  benchmarks_dir = os.path.join(root_dir, "benchmarks")
  os.makedirs(benchmarks_dir, exist_ok=True)

  if benchmark in repos:
    url, version = repos[benchmark]
    repo_dir = os.path.join(benchmarks_dir, benchmark)

    if os.path.exists(repo_dir):
      result = run_command(["rm", "-rf", repo_dir], os.getcwd())
    print(f"[WASABI-HELPER]: [INFO]: Cloning {benchmark} repository from {url}...")
    result = run_command(["git", "clone", url, repo_dir], os.getcwd())
    if result is None or result.returncode != 0:
      print(f"[WASABI-HELPER]: [ERROR]: Error cloning {benchmark}:\n\t{result.stdout}\n\t{result.stderr}")
      sys.exit(1)
    print(f"[WASABI-HELPER]: [INFO]: Successfully cloned {benchmark}.")

    print(f"Checking out version {version} for {benchmark}...")
    result = run_command(["git", "checkout", version], repo_dir)
    if result is None or result.returncode != 0:
      print(f"[WASABI-HELPER]: [ERROR]: Error checking out version {version} for {benchmark}:\n\t{result.stdout}\n\t{result.stderr}")
      sys.exit(1)
    print(f"[WASABI-HELPER]: [INFO]: Successfully checked out version {version} for {benchmark}.")
  else:
    print(f"[WASABI-HELPER]: [WARNING]: Benchmark {benchmark} is not recognized and will be skipped.")

def replace_config_files(root_dir: str, benchmark: str):
  """
  Replaces the original build (Maven pom.xml) file with a customized version 
  for each application in the benchmark list.

  Arguments:
    root_dir (str): The root directory of the repository.
    benchmark (list): The target applications for which to replace the config/build files.
  """
  benchmark_dir = os.path.join(root_dir, "benchmarks", benchmark)
  original_pom_path = os.path.join(benchmark_dir, "pom.xml")
  backup_pom_path = os.path.join(benchmark_dir, "pom-original.xml")
  if "hive/standalone-metastore" in benchmark: 
    custom_pom_path = os.path.join(root_dir, "wasabi", "wasabi-testing", "config", "hive", "pom-hive-standalone-metastore.xml")
  else:
    custom_pom_path = os.path.join(root_dir, "wasabi", "wasabi-testing", "config", benchmark, f"pom-{benchmark}.xml")
  new_pom_path = os.path.join(benchmark_dir, "pom.xml")

  if os.path.exists(backup_pom_path):
    print(f"[WASABI-HELPER]: [INFO]: Backup pom-original.xml already exists for {benchmark}. Skipping renaming.")
  else:
    if os.path.exists(original_pom_path):
      shutil.move(original_pom_path, backup_pom_path)
      print(f"[WASABI-HELPER]: [INFO]: Renamed {original_pom_path} to {backup_pom_path}.")
    else:
      print(f"[WASABI-HELPER]: [INFO]: Original pom.xml not found for {benchmark}. Skipping renaming.")

  if os.path.exists(custom_pom_path):
    shutil.copy(custom_pom_path, new_pom_path)
    print(f"[WASABI-HELPER]: [INFO]: Copied {custom_pom_path} to {new_pom_path}.")
  else:
    print(f"[WASABI-HELPER]: [ERROR]: Customized {custom_pom_path} not found for {benchmark}. Skipping copy.")

def rewrite_source_code(root_dir: str, benchmark: str, mode: str):
  """
  Rewrites retry related bounds -- either retry thresholds or test timeouts.

  Arguments:
    root_dir (str): The root directory of the repository.
    benchmark (list): The target applications for which to replace the pom.xml.
    mode (str): The type of source rewriting -- retry bounds or timeout values.
  """
  benchmark_dir = os.path.join(root_dir, "benchmarks", benchmark)
  if mode == "bounds-rewriting": 
    config_file = os.path.join(root_dir, "wasabi", "wasabi-testing", "config", benchmark, f"{benchmark}_retry_bounds.data")
  elif mode == "timeout-rewriting":
    config_file = os.path.join(root_dir, "wasabi", "wasabi-testing", "config", benchmark, f"{benchmark}_timeout_bounds.data")
  else:
    print(f"[WASABI-HELPER]: [ERROR]: Bad arguments provided to source_rewriter.py.")
    return

  cmd = ["python3", "source_rewriter.py", "--mode", mode, config_file, benchmark_dir]
  result = run_command(cmd, os.getcwd())
  
  if result is None or result.returncode != 0:
    print(f"[WASABI-HELPER]: [ERROR]: Rewriting retry-related bounds failed:\n\t{result.stdout}\n\t{result.stderr}")
  else:
    print(f"[WASABI-HELPER]: [INFO]: Successfully overwritten retry-related bounds. Status: {result.returncode}")
    

def run_fault_injection(target: str):
  """
  Run the run_benchmark.py script for a specific application.

  Arguments:
    root_dir (str): The root directory of the repository.
    target (str): The name of the application.
  """

  cmd = ["python3", "run_benchmark.py", "--benchmark", target]
  result = run_command(cmd, os.getcwd())
  if result is None or result.returncode != 0:
    print(f"[WASABI-HELPER]: [ERROR]: Command to run run_benchmark.py on {target} failed with error message:\n\t{result.stdout}\n\t{result.stderr}")
  else:
    print(f"[WASABI-HELPER]: [INFO]: Finished running test suite for {target}. Status: {result.returncode}")


def run_bug_oracles(root_dir: str, target: str):
  """
  Runs bug oracels over a set of test and build reports.

  Parameters:
    root_dir (str): The root directory where the results for the target are located.
    target (str): The name of the application.
  """
  target_root_dir = os.path.join(root_dir, "results", target)
  csv_file = os.path.join(target_root_dir, f"{target}-bugs-per-test.csv")
  if os.path.exists(csv_file):
    cmd = ["rm", "-f", csv_file]
    result = run_command(cmd, os.getcwd())
    
    if result is None or result.returncode != 0:
      print(f"[WASABI-HELPER]: [ERROR]: Command to remove {csv_file} failed:\n\t{result.stdout}\n\t{result.stderr}")
    else:
      print(f"[WASABI-HELPER]: [INFO]: Removed {csv_file}. Status: {result.returncode}")
  
  for item in os.listdir(target_root_dir):
    item_path = os.path.join(target_root_dir, item)
    if os.path.isdir(item_path):
      cmd = ["python3", "bug_oracles.py", item_path, "--benchmark", target]
      result = run_command(cmd, os.getcwd())
      if result:
        print(result.stdout)
      
      if result is None or result.returncode != 0:
        print(f"[WASABI-HELPER]: [ERROR]: Command to run bug_oracles.py on {item_path} failed with error message:\n\t{result.stdout}\n\t{result.stderr}")
      else:
        print(f"[WASABI-HELPER]: [INFO]: Finished processing {item_path}. Status: {result.returncode}")


""" Helper functions
"""
def run_command(cmd: list[str], cwd: str):
  """
  Run a command in a subprocess and display the output in real-time.

  Arguments:
    cmd (list): The command to run.
    cwd (str): The working directory.

  Returns:
    CompletedProcess: The result of the command execution.
  """
  process = subprocess.Popen(cmd, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)

  stdout_lines = []
  stderr_lines = []

  try:
    for stdout_line in iter(process.stdout.readline, ""):
      stdout_lines.append(stdout_line)
      print(stdout_line, end="")

    process.stdout.close()
    process.wait()

    stderr_lines = process.stderr.readlines()
    process.stderr.close()

    return subprocess.CompletedProcess(cmd, process.returncode, ''.join(stdout_lines), ''.join(stderr_lines))
  except Exception as e:
    process.kill()
    raise e

def display_phase(phase: str, benchmark: str):
  """
  Prints a "stylized" message indicating the current phase.

  Arguments:
    phase (str): The name of the phase to display.
  """
  phase_text = f" {benchmark}: {phase} "
  border_line = "*" * (len(phase_text) + 4)
  inner_line = "*" + " " * (len(phase_text) + 2) + "*"
  print(f"\n{border_line}")
  print(f"{inner_line}")
  print(f"*{phase_text.center(len(border_line) - 2)}*")
  print(f"{inner_line}")
  print(f"{border_line}\n")


""" Main
"""
def main():
  parser = argparse.ArgumentParser()
  parser.add_argument("--phase", choices=["setup", "prep", "bug-triggering", "bug-oracles", "all"], required=True, help="The pipeline phase to run")
  parser.add_argument("--benchmark", choices=["hadoop", "hbase", "hive", "cassandra", "elasticsearch"], required=True, help="The benchmark to run")
  args = parser.parse_args()

  wasabi_root_dir = os.getenv("WASABI_ROOT_DIR")
  if not wasabi_root_dir:
    print("[WASABI-HELPER]: [ERROR]: The WASABI_ROOT_DIR environment variable is not set.")
    sys.exit(1)
  repo_root_dir = os.path.join(wasabi_root_dir, "..")

  if args.phase == "setup" or args.phase == "all":
    display_phase("setup", args.benchmark)
    clone_repositories(repo_root_dir, args.benchmark)

  if args.phase == "prep" or args.phase == "all":
    display_phase("code preparation", args.benchmark)
    replace_config_files(repo_root_dir, args.benchmark)
    if args.benchmark == "hive":
      replace_config_files(repo_root_dir, os.path.join(args.benchmark, "standalone-metastore"))
    rewrite_source_code(repo_root_dir, args.benchmark, "bounds-rewriting")
    rewrite_source_code(repo_root_dir, args.benchmark, "timeout-rewriting")

  if args.phase == "bug-triggering" or args.phase == "all":
    display_phase("bug triggering", args.benchmark)
    run_fault_injection(args.benchmark)

  if args.phase == "bug-oracles" or args.phase == "all":
    display_phase("Bug oracles", args.benchmark)
    run_bug_oracles(repo_root_dir, args.benchmark)

if __name__ == "__main__":
  main()