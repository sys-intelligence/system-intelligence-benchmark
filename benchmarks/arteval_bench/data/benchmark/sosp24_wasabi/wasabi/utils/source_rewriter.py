import os
import re
import shutil
import argparse

RETRY_BOUND = 997
TIMEOUT_BOUND = 303303

""" Retry bounds rewriting
"""
class RetryBoundsRewriter:
  def find_java_file(self, test_class, test_directory_path):
    for root, _, files in os.walk(test_directory_path):
      for file in files:
        if file.endswith(".java") and file.split(".")[0] == test_class:
          return os.path.join(root, file)
    return None

  def find_and_modify_assignment(self, test_class, assign_method, var_name, new_value, test_directory_path):
    java_file = self.find_java_file(test_class, test_directory_path)
    if java_file is None:
      print(f">>> Not found: {test_class}")
      return False

    java_file_copy = f"{os.path.splitext(os.path.join(os.path.dirname(java_file), os.path.basename(java_file)))[0]}.original"
    if os.path.isfile(java_file_copy):
      return False

    shutil.copy2(java_file, java_file_copy)

    with open(java_file, 'r') as file:
      lines = file.readlines()

    modified_lines = []
    index = 0
    while index < len(lines):
      if f"{assign_method}(" in lines[index] and var_name in lines[index]:
        to_change = lines[index].rstrip("\n")
        index += 1
        while index < len(lines) and ");" not in lines[index - 1]:
          to_change += lines[index].strip()
          index += 1
        to_change = re.sub(r"\d+\);", lambda m: f"{new_value});" if int(m.group().strip("\);")) < new_value else m.group(), to_change)
        modified_lines.append(to_change + "\n")
      else:
        modified_lines.append(lines[index])
        index += 1

    with open(java_file, 'w') as file:
      file.writelines(modified_lines)

    return True

  def process_input(self, input_file, test_directory_path):
    with open(input_file, 'r') as file:
      next(file)
      for line in file:
        line = line.strip()
        var_name, assigned_value, assign_method, test_class = line.split("!!!")
        try:
          if int(assigned_value.strip('"')) < int(RETRY_BOUND):
            assign_method = assign_method.strip().split('.')[-1]
            new_value = int(RETRY_BOUND)

          self.find_and_modify_assignment(test_class, assign_method, var_name, new_value, test_directory_path)
        except:
          print(f">>> ERROR: {test_class}")

  def run(self, input_file, test_directory_path):
    self.process_input(input_file, test_directory_path)


""" Timeout bounds rewriting
"""
class TimeoutBoundsRewriter:
  def __init__(self):
    self.tests_to_rewrite = dict()
    self.test_targets = dict()

  def read_test_targets(self, input_file):
    with open(input_file, "r") as target:
      lines = target.read().splitlines()

    for line in lines:
      test_file, test_name = line.strip().split(".")
      test_file = test_file.strip()
      test_name = test_name.strip()

      if test_file not in self.tests_to_rewrite:
        self.tests_to_rewrite[test_file] = []
      self.tests_to_rewrite[test_file].append(test_name)

      if test_file not in self.test_targets:
        self.test_targets[test_file] = True

  def to_modify(self, line, test_class):
    if "test" not in line:
      return False

    for test_name in self.tests_to_rewrite.get(test_class, []):
      if test_name in line:
        return True

    return False

  def is_target_test(self, lines, index, test_class):
    while index > 0:
      if "test" in lines[index] and "public" in lines[index] and "@Test" in lines[index - 1]:
        return self.to_modify(lines[index], test_class)
      index -= 1

    return False

  def modify_timeout_annotations(self, file_path, test_class):
    with open(file_path, "r") as test_file:
      lines = test_file.readlines()

    modified_lines = []
    for index in range(len(lines)):
      modified_line = lines[index]

      line_without_spaces = re.sub(r"\s", "", lines[index])

      if "@Test" in line_without_spaces and "timeout" in line_without_spaces:
        if index + 1 < len(lines) and self.to_modify(lines[index + 1], test_class):
          if re.search(r"@Test\(timeout=(\d+)\)", line_without_spaces):
            current_timeout = int(re.search(r"@Test\(timeout=(\d+)\)", line_without_spaces).group(1))
            if current_timeout < TIMEOUT_BOUND:
              modified_timeout = str(TIMEOUT_BOUND)
              modified_line = re.sub(
                r"@Test\(timeout=\d+\)",
                r"\t@Test (timeout = {0})\n".format(modified_timeout),
                line_without_spaces,
              )

      modified_lines.append(modified_line)

    with open(file_path, "w") as test_file:
      test_file.writelines(modified_lines)

  def modify_wait_for_calls(self, file_path, test_class):
    with open(file_path, 'r') as file:
      lines = file.readlines()

    modified_lines = []
    index = 0
    while index < len(lines):
      if "GenericTestUtils.waitFor(" in lines[index] and self.is_target_test(lines, index, test_class):
        to_change = lines[index]
        opened_count = to_change.count('(')
        closed_count = to_change.count(')')
        index += 1
        while index < len(lines) and opened_count != closed_count:
          modified_lines.append(to_change)
          to_change = lines[index]
          opened_count += to_change.count('(')
          closed_count += to_change.count(')')
          index += 1
        to_change = re.sub(r"\d+\);", lambda m: f"{TIMEOUT_BOUND});" if int(m.group().strip("\);")) < TIMEOUT_BOUND else m.group(), to_change)
        modified_lines.append(to_change + "\n")
      else:
        modified_lines.append(lines[index])
        index += 1

    with open(file_path, "w") as test_file:
      test_file.writelines(modified_lines)

  def run(self, input_file, test_directory_path):
    self.read_test_targets(input_file)
    for root, _, files in os.walk(test_directory_path):
      for file_name in files:
        if file_name.endswith(".java") and file_name.startswith("Test"):
          file_path = os.path.join(root, file_name)
          file_base_name = os.path.splitext(file_name)[0]

          if file_base_name in self.test_targets:
            original_file_path = f"{os.path.splitext(os.path.join(os.path.dirname(file_path), os.path.basename(file_path)))[0]}.original"
            if not os.path.isfile(original_file_path):
              shutil.copy2(file_path, original_file_path)

            self.modify_timeout_annotations(file_path, file_base_name)
            self.modify_wait_for_calls(file_path, file_base_name)


def main():
  parser = argparse.ArgumentParser(description='Modify Java test files based on specified criteria.')
  parser.add_argument('--mode', choices=['bounds-rewriting', 'timeout-rewriting'], help='Mode of operation: "bounds-rewriting" or "timeout-rewriting".')
  parser.add_argument('config_file', help='Path to the config file describing the list of changes.')
  parser.add_argument('target_root_dir', help='Directory path to start the search for Java test files.')
  args = parser.parse_args()

  if args.mode == 'bounds-rewriting':
    rewriter = RetryBoundsRewriter()
  elif args.mode == 'timeout-rewriting':
    rewriter = TimeoutBoundsRewriter()

  rewriter.run(args.config_file, args.target_root_dir)


if __name__ == "__main__":
  main()