import re
import os
from typing import Tuple, Optional

def get_pointcut_coverage_breakdown(log_msg: str) -> Optional[Tuple[str, str, str, str]]:
  """Extract coverage information from a given log message.
  
  Args:
    log_msg (str): A log message in the file.

  Returns:
    Tuple[str, str, str]: returns a tuple containing the relevant coverage strings.
  """
  segments = log_msg.split(" | ")

  test_name = next(s.split("---")[1] for s in segments if "Test " in s)
  injection_site = re.search(
      r'\w+\(.*\s+(.*\(.*?\))\)', 
      next(s.split("---")[1] for s in segments if "Injection site " in s)
    ).group(1)
  injection_location = next(s.split("---")[1] for s in segments if "Injection location " in s)
  retry_caller = next(s.split("---")[1] for s in segments if "Retry caller " in s)

  if test_name is not None and injection_site is not None and injection_location is not None and retry_caller is not None:
    return test_name, retry_caller, injection_site, injection_location
  return None

def get_injection_coverage_breakdown(log_msg: str) -> Optional[Tuple[str, str, str, str]]:
  """Extract coverage information from a given log message.
  
  Args:
    log_msg (str): A log message in the file.

  Returns:
    Tuple[str, str, str]: returns a tuple containing the relevant coverage strings.
  """
  segments = log_msg.split(" | ")

  test_name = next(s.split("---")[1] for s in segments if "Test " in s)
  injection_site = re.search(
      r'\w+\(.*\s+(.*\(.*?\))\)', 
      next(s.split("---")[3] for s in segments if "thrown after calling " in s)
    ).group(1)
  retry_location = next(s.split("---")[1] for s in segments if "Retry location " in s)
  retry_attempt = next(s.split("---")[1] for s in segments if "Retry attempt " in s)

  if test_name is not None and injection_site is not None and retry_location is not None:
    return test_name, injection_site, retry_location
  return None

def main():
  pointcut_cov_methods = set()
  pointcut_cov_breakdown = set()
  injection_cov_methods = set()
  injection_cov_breakdown = set()
  
  for root, _, files in os.walk('.'):
    for fname in files:
      if fname.endswith('-output.txt'):
        with open(os.path.join(root, fname), 'r') as file:
          for line in file:
            if '[wasabi]' in line and '[Pointcut]' in line and "Test ---" in line:
              coverage_info = get_pointcut_coverage_breakdown(line)
              if coverage_info:
                pointcut_cov_breakdown.add(coverage_info)
                pointcut_cov_methods.add(coverage_info[2])
              else:
                print("[wasabi-utils]: Malformed log line: " + line)
            elif '[wasabi]' in line and '[Injection]' in line:
              coverage_info = get_injection_coverage_breakdown(line)
              if coverage_info:
                injection_cov_breakdown.add(coverage_info)
                injection_cov_methods.add(coverage_info[1])
              else:
                print("[wasabi-utils]: Malformed log line: " + line)
            else:
              continue
  
  print("=== Coverage stats ===")
  print("Pointcut coverage: " + str(len(pointcut_cov_methods)))
  print("Injection coverage: " + str(len(injection_cov_methods)))
  
  print("\n\n=== Injection sites not covered ===")
  for method in pointcut_cov_methods:
    if method not in injection_cov_methods:
      print(method)

  print("\n\n=== Pointcut covered breakdown ===")
  for (_, retry_caller, injection_site, injection_location) in pointcut_cov_breakdown:
    print(retry_caller + " " + injection_site + " " + injection_location)

  print("\n\n=== Injection covered breakdown ===")
  for (_, injection_site, retry_location) in injection_cov_breakdown:
    print(injection_site + " " + retry_location)

if __name__ == "__main__":
  main()
