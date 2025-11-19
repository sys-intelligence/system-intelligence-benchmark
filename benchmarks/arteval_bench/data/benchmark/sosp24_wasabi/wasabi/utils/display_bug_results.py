from collections import defaultdict
import os
import sys

def get_benchmark_name(loc):
  """
  Classifies the location based on its prefix.

  Parameters:
    location (str): The bug location string to classify.
  
  Returns:
    str: The classification group (hdfs, yarn, mapreduce, hadoop, hbase, hive, cassandra, elasticsearch).
  """
  if loc.startswith("org.apache.hadoop.hdfs") and "SecondaryNameNode.doWork" not in loc:
    return "hdfs"
  elif loc.startswith("org.apache.hadoop.yarn"):
    return "yarn"
  elif loc.startswith("org.apache.hadoop.mapreduce") or loc.startswith("org.apache.hadoop.mapred"):
    return "mapreduce"
  elif loc.startswith("org.apache.hadoop.hbase"):
    return "hbase"
  elif loc.startswith("org.apache.hadoop.hive"):
    return "hive"
  elif loc.startswith("org.apache.cassandra"):
    return "cassandra"
  elif loc.startswith("org.apache.hadoop") or "SecondaryNameNode.doWork" in loc: # initialy found in hadoop-common, added here to match Table 3
    return "hadoop"
  elif loc.startswith("org.elasticsearch"):
    return "elasticsearch"
  else:
    return "unknown"

def aggregate_bugs(root_dir):
  """
  Searches for bug report files and aggregates bugs based on their type and 
  which application have been found in.

  Parameters:
   root_dir (str): The root directory to search for the bug report files.
  
  Returns:
   dict: A dictionary storing the benchmark, bug type, and retry location tuples.
  """
  bugs = defaultdict(lambda: defaultdict(set))
  unique = dict()

  for dirpath, _, files in os.walk(root_dir):
    for file in files:
      if file.endswith(".csv"):
        file_path = os.path.join(dirpath, file)
        
        with open(file_path, 'r') as f:
          for line in f:
            if "how-bug" in line or "when-missing-" in line:
              tokens = line.strip().split(",")
      
              bug_type = tokens[1]
              bug_loc = tokens[2]
              
              key = bug_type + bug_loc
              if key in unique:
                continue
              unique[key] = "x"

              benchmark = get_benchmark_name(bug_loc)       
              bugs[bug_type][benchmark].add(bug_loc)
 
  return bugs


def get_ground_truth_bugs(file_path: str):
  """
  Reads the ground truth bugs from a file and organizes them into a dictionary.

  Parameters:
   file_path (str): The path to the ground truth file.
  
  Returns:
   dict: A dictionary similar to the bugs dictionary with bug_type, benchmark, and retry_location.
  """
  ground_truth = defaultdict(lambda: defaultdict(set))
  
  with open(file_path, 'r') as f:
    for line in f:
      tokens = line.strip().split(",")
      benchmark = tokens[0]
      bug_type = tokens[1]
      retry_location = tokens[2]
      ground_truth[bug_type][benchmark].add(retry_location)
  
  return ground_truth


def print_bug_tables(bugs, ground_truth):
  """
  Prints a table of bug types and the benchmark where they were found.

  Parameters:
    bugs (dict): A dictionary that aggregates all bugs found by WASABI.
  """
  benchmarks = ["hadoop", "hdfs", "mapreduce", "yarn", "hbase", "hive", "cassandra", "elasticsearch"]
  ordered_bug_types = ["when-missing-cap", "when-missing-backoff", "how-bug"]
  row_names = {
    "how-bug": "HOW",
    "when-missing-backoff": "WHEN-no-delay",
    "when-missing-cap": "WHEN-no-cap"
  }
 
  display_table_name("Table 3 (inverted, bugs found)")
  header = ["Bug Type"] + benchmarks + ["TOTAL"]
  print(f"{header[0]:<20}", end="")
  for b in benchmarks:
    print(f"{b:<15}", end="")
  print(f"{'TOTAL':<15}")
  
  unmatched_ground_truth = {}
  for bug_type in ordered_bug_types:
    display_name = row_names.get(bug_type, bug_type)
    print(f"{display_name:<20}", end="")
    total_count = 0
    
    for benchmark in benchmarks:
      ground_truth_locations = ground_truth.get(bug_type, {}).get(benchmark, set())
      bug_locations = bugs.get(bug_type, {}).get(benchmark, set())
      unmatched_ground_truth.setdefault(bug_type, set())

      matching_locations = set()
      for bug in bug_locations:
        if bug in ground_truth_locations:
          matching_locations.add(bug)

      count = len(matching_locations)
      total_count += count

      non_matching = ground_truth_locations - matching_locations
      unmatched_ground_truth[bug_type].update(non_matching)
  
      print(f"{count:<15}", end="")
    
    print(f"{total_count:<15}")

  display_table_name("Table 3 (original)")
  print(f"{header[0]:<20}", end="")
  for b in benchmarks:
    print(f"{b:<15}", end="")
  print(f"{'TOTAL':<15}")
  
  for bug_type in ordered_bug_types:
    display_name = row_names.get(bug_type, bug_type)
    print(f"{display_name:<20}", end="")
    total_count = 0
    
    for benchmark in benchmarks:
      bug_locations = bugs.get(bug_type, {}).get(benchmark, set())
      count = len(bug_locations)
      total_count += count
      print(f"{count:<15}", end="")
    
    print(f"{total_count:<15}")

  print("\nUnmatched ground truth locations (not found in bugs):")
  for bug_type, unmatched_set in unmatched_ground_truth.items():
    if unmatched_set:
      print(f"Bug Type: {bug_type}")
      for location in unmatched_set:
        print(f" - {location}")


def display_table_name(msg: str):
  """
  Prints a "stylized" message indicating the table printed.

  Arguments:
    msg (str): The name of the table.
  """
  border_line = "*" * (len(msg) + 4)
  inner_line = "*" + " " * (len(msg) + 2) + "*"
  print(f"\n{border_line}")
  print(f"{inner_line}")
  print(f"*{msg.center(len(border_line) - 2)}*")
  print(f"{inner_line}")
  print(f"{border_line}\n")


def main():
  wasabi_root_dir = os.getenv("WASABI_ROOT_DIR")
  if not wasabi_root_dir:
    print("[WASABI-HELPER]: [ERROR]: The WASABI_ROOT_DIR environment variable is not set.")
    sys.exit(1)
  results_root_dir = os.path.join(wasabi_root_dir, "..", "results")
  ground_truth_file = os.path.join(wasabi_root_dir, "wasabi-testing", "bugs_ground_truth.txt")

  bugs = aggregate_bugs(results_root_dir)
  ground_truth = get_ground_truth_bugs(ground_truth_file)
  print_bug_tables(bugs, ground_truth)

if __name__ == "__main__":
  main()