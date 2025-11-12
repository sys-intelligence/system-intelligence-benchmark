import sys

def calculate_test_outcomes_from_file(filename):
  total_tests_passed = 0
  total_tests_executed = 0
  results = False

  with open(filename, 'r') as file:
    for line in file:
      if line.startswith("[INFO] Results:"):
        results = True
      if results == True and "Tests run" in line and "Failures" in line and "Errors" in line:
        tests_run = int(line.split("Tests run: ")[1].split(",")[0])
        failures = int(line.split("Failures: ")[1].split(",")[0])
        errors = int(line.split("Errors: ")[1].split(",")[0])
        
        total_tests_passed += (tests_run - failures - errors)
        total_tests_executed += tests_run

        results = False
  
  return total_tests_passed, total_tests_executed

def main():
  if len(sys.argv) != 2:
    print("Usage: python script.py <build_log_file_path>")
    sys.exit(1)
  
  filename = sys.argv[1]
  total_tests_passed, total_tests_executed = calculate_test_outcomes_from_file(filename)
  print("Total tests passed:", total_tests_passed)
  print("Total tests executed:", total_tests_executed)

if __name__ == "__main__":
  main()
