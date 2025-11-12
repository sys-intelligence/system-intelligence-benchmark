import argparse
import random
import re
import os
import sys


def injection_locations_graph(filename):
  """
  Builds a graph representing retry locations and their associated tests from the input file.

  Args:
    filename (str): Path to the input file containing retry locations and associated tests.

  Returns:
    dict: A dictionary representing the graph, where keys are retry locations and values are sets of tests.
  """
  graph = {}

  with open(filename, 'r', encoding='utf-8') as file:
    for line in file:
        test_name = line.split(",")[0].strip()
        injection_location = line.split(",")[1].strip()
        graph.setdefault(injection_location, set()).add(test_name)

  return graph


def find_matching(graph):
  """
  Performs a best-effort matching of tests to retry locations.

  Args:
    graph (dict): The retry locations graph where keys are retry locations and values are sets of tests.

  Returns:
    dict: A dictionary representing the matching, where keys are retry locations and values are sets of tests.
  """
  matching = {}
  already_matched = set()

  tests = list(set().union(*graph.values()))
  random.shuffle(tests)

  for test in tests:
    injection_locations = [location for location, tests_set in graph.items() if test in tests_set
                           and all(test not in matching_tests for matching_tests in matching.values())]
    if injection_locations:
      injection_location = min(injection_locations, key=lambda x: len(matching.get(x, set())))
      matching.setdefault(injection_location, set()).add(test)
      already_matched.add(test)

  return matching


def find_unmatched(matching, graph):
  """
  Finds and returns unmatched tests and retry locations.

  Args:
    matching (dict): The matching dictionary where keys are tests and values are matched retry locations.
    graph (dict): The retry locations graph where keys are retry locations and values are sets of tests.

  Returns:
    tuple: A tuple containing three sets - the first set contains unmatched tests, the second set contains
         retry locations that are not matched with any tests, and the third set contains tests that are
         matched to multiple retry locations in the matching dictionary.
  """
  
  # Get the set of all tests and retry locations from the graph
  all_tests = set().union(*graph.values())
  all_injection_locations = set(graph.keys())

  # Get the set of matched tests and retry locations from the matching
  matched_tests = set().union(*matching.values())
  matched_injection_locations = set(matching.keys())

  # Get the set of unmatched tests and retry locations by taking the difference
  unmatched_tests = all_tests - matched_tests
  unmatched_injection_locations = all_injection_locations - matched_injection_locations

  # Get the set of tests that are matched to multiple retry locations by taking the intersection
  multi_matched_tests = {test for test in matched_tests if len([met for met, t in matching.items() if t == test]) > 1}

  return matched_injection_locations, unmatched_injection_locations, unmatched_tests, multi_matched_tests


def append_to_config_file(input_config, dir_path, matching):
  with open(input_config, "r") as file:
    lines = file.readlines()

  header = "Retry location!!!Retry caller!!!Injection site!!!Injection location!!!Exception\n"

  partitions_dir = os.path.join(dir_path, "partitions")
  os.makedirs(partitions_dir, exist_ok=True)
  
  for line in lines:
    injection_location = line.strip().split("!!!")[3]
    # Get the tests that are matched to this retry location
    if injection_location in matching:
      for test in matching[injection_location]:
        # Create a data file for each test
        output_filename = os.path.join(partitions_dir, f"{os.path.splitext(os.path.basename(input_config))[0]}-{test}.data")
        with open(output_filename, "a") as output_file:
          if output_file.tell() == 0:
            output_file.write(header)
          output_file.write(line)
        
        # Create a configuration file for each test
        config_filename = os.path.join(partitions_dir, f"{os.path.splitext(os.path.basename(input_config))[0]}-{test}.conf")
        with open(config_filename, "w") as config_file:
          config_file.write(f"retry_data_file: {output_filename}\n")
          config_file.write("injection_policy: max-count\n")
          config_file.write("max_injection_count: 311\n")


def main():
  parser = argparse.ArgumentParser(description='Matcher')
  parser.add_argument('--retry_locations_input', help='Retry locations input file')
  parser.add_argument('--test_retry_pairs_input', help='Tests-to-retry pairings input file')
  parser.add_argument('--path_to_configs', help='Path to configuration files')
  args = parser.parse_args()

  if not (args.retry_locations_input and args.test_retry_pairs_input and args.path_to_configs):
    print("[wasabi] matcher.py takes three arguments")
    sys.exit(1)

  # Step 1: Construct the "retry locations to tests" graph
  graph = injection_locations_graph(args.test_retry_pairs_input)
  
  # Step 2: Find a matching where each test is matched to a unique retry location.
  matching = find_matching(graph)
  
  # Step 3: Check if matching is complete
  matched_injection_locations, unmatched_injection_locations, unmatched_tests, multi_matched_tests = find_unmatched(matching, graph)
  print("================= Statistics ================")
  print("Total matched retried methods:", len(matched_injection_locations))
  print("Unmatched retried method:\n\t", "\n\t".join(unmatched_injection_locations))
  print("Unmatched tests:\n\t", '\n\t'.join(unmatched_tests))
  print("Tests matched multiple times:\n\t", "\n\t".join(multi_matched_tests))
  print("=================    |||    =================")

  # Step 4: Split the larger config file based on the retry locations to tests matching.
  append_to_config_file(args.retry_locations_input, args.path_to_configs, matching)


if __name__ == "__main__":
  main()

