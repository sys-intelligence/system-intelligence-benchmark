from collections import defaultdict
import os

from utils import RESULTS_ROOT_DIR
from utils import GROUND_TRUTH_FILE
from utils import SIMILARITY_RATIO

from utils import logger

class OracleExperimentRuns:
  def __init__(self):
    pass

  def get_benchmark_name(self, loc):
    """
    Classifies the location based on its prefix.
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
    elif loc.startswith("org.apache.hadoop") or "SecondaryNameNode.doWork" in loc:  # initialy found in hadoop-common, added here to match Table 3
      return "hadoop"
    elif loc.startswith("org.elasticsearch"):
      return "elasticsearch"
    else:
      return "unknown"

  def aggregate_bugs(self, root_dir):
    """
    Searches for bug report files and aggregates bugs based on their type and 
    which application have been found in.
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

                benchmark = self.get_benchmark_name(bug_loc)       
                bugs[bug_type][benchmark].add(bug_loc)
  
    return bugs

  def get_ground_truth_bugs(self, file_path: str):
    """
    Reads the ground truth values from a file into a dictionary.
    """
    ground_truth = defaultdict(lambda: defaultdict(set))
    
    try:
      with open(file_path, 'r') as f:
        for line in f:
          tokens = line.strip().split(",")
          benchmark = tokens[0]
          bug_type = tokens[1]
          retry_location = tokens[2]
          ground_truth[bug_type][benchmark].add(retry_location)
    except Exception:
      logger.info(f"Cannot open {file_path} or file not present.")
    
    return ground_truth

  def count_bugs(self, bugs, ground_truth):
    """
    Compares the total number of bugs found against the ground truth.
    """
    total_ground_truth = 0
    total_found = 0

    for bug_type, benchmarks in ground_truth.items():
      for benchmark, ground_truth_locations in benchmarks.items():
        total_ground_truth += len(ground_truth_locations)
        bug_locations = bugs.get(bug_type, {}).get(benchmark, set())
        matching_locations = ground_truth_locations & bug_locations
        total_found += len(matching_locations)

    if total_ground_truth == 0:
      logger.info("No ground truth bugs available.")
      return False

    coverage = total_found / total_ground_truth
    logger.info(f"Found {total_found} out of {total_ground_truth} ground truth bugs ({coverage:.2%}).")

    passed = coverage >= SIMILARITY_RATIO
    logger.info("Results reproduced: PASS" if passed else "Results reproduced: FAIL")
    return passed


  def run(self):
    bugs = self.aggregate_bugs(str(RESULTS_ROOT_DIR))
    ground_truth = self.get_ground_truth_bugs(str(GROUND_TRUTH_FILE))
    passed = self.count_bugs(bugs, ground_truth)

    if passed:
      return True
    
    return False