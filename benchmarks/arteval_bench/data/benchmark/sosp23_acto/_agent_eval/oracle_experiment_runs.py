import json
from dataclasses import dataclass
from pathlib import Path
from typing import Tuple

from utils import RESULTS_PATH_TABLES, REFERENCE_PATH_TABLES, SIMILARITY_RATIO, logger


@dataclass(frozen=True)
class Table5Row:
  operator: str
  undesired_state: int
  system_error: int
  operator_error: int
  recovery_failure: int
  total: int


@dataclass(frozen=True)
class Table6Row:
  symptom: str
  bugs: int


@dataclass(frozen=True)
class Table7Row:
  test_oracle: str
  bugs: int


@dataclass(frozen=True)
class Table8Row:
  operator: str
  operations: int


class OracleExperimentRuns:

  def __init__(self) -> None:
    # File paths for each table
    self.table5_results_path = Path(RESULTS_PATH_TABLES["table5"])
    self.table5_reference_path = Path(REFERENCE_PATH_TABLES["table5"])
    self.table6_results_path = Path(RESULTS_PATH_TABLES["table6"])
    self.table6_reference_path = Path(REFERENCE_PATH_TABLES["table6"])
    self.table7_results_path = Path(RESULTS_PATH_TABLES["table7"])
    self.table7_reference_path = Path(REFERENCE_PATH_TABLES["table7"])
    self.table8_results_path = Path(RESULTS_PATH_TABLES["table8"])
    self.table8_reference_path = Path(REFERENCE_PATH_TABLES["table8"])

    # Parsed rows for tables
    self.table5_rows: list[Table5Row] = []
    self.table6_rows: list[Table6Row] = []
    self.table7_rows: list[Table7Row] = []
    self.table8_rows: list[Table8Row] = []

    # Totals
    self.table5_exp_total: int | None = None
    self.table5_ref_total: int | None = None
    self.table6_exp_total: int | None = None
    self.table6_ref_total: int | None = None
    self.table7_exp_total: int | None = None
    self.table7_ref_total: int | None = None
    self.table8_exp_total: int | None = None
    self.table8_ref_total: int | None = None

    # Raw non-empty lines from result files
    self._table5_raw_lines: list[str] = []
    self._table6_raw_lines: list[str] = []
    self._table7_raw_lines: list[str] = []
    self._table8_raw_lines: list[str] = []

  def is_separator_line(self, line: str) -> bool:
    """
    Return True if this is a header separator line (Markdown spaces and dashes).
    """
    stripped = line.strip()
    if not stripped:
      return False
    return all(ch in "- " for ch in stripped)

  def parse_int(self, text: str) -> Tuple[bool, int]:
    """
    Parse a numeric string into an int.
    """
    try:
      return True, int(text.replace(",", ""))
    except ValueError:
      return False, 0

  # -----------------------
  # TABLE-5 helpers
  # -----------------------

  def load_table5(self) -> Tuple[bool, str]:
    """
    Load raw TABLE-5 file into memory.
    """
    if not self.table5_reference_path.exists():
      return False, f"{self.table5_reference_path} (TABLE-5 reference) not found"

    if not self.table5_results_path.exists():
      return False, f"{self.table5_results_path} (TABLE-5 results) not found"

    text = self.table5_results_path.read_text(encoding="utf-8")
    lines = [line.rstrip("\n") for line in text.splitlines() if line.strip()]
    if not lines:
      return False, f"{self.table5_results_path} is empty"

    self._table5_raw_lines = lines
    return True, ""

  def parse_table5(self) -> Tuple[bool, str]:
    """
    Parse TABLE-5 and extract the bottom-right 'Total' cell.
    """
    EXPECTED_HEADERS: list[str] = [
      "Operator",
      "Undesired State",
      "System Error",
      "Operator Error",
      "Recovery Failure",
      "Total",
    ]

    header_line: str | None = None
    data_lines: list[str] = []
    saw_separator = False

    for line in self._table5_raw_lines:
      if header_line is None:
        header_line = line
        continue

      if not saw_separator and self.is_separator_line(line):
        saw_separator = True
        continue

      if saw_separator:
        data_lines.append(line)

    if header_line is None:
      return False, "TABLE-5: no table header found"

    if any(h not in header_line for h in EXPECTED_HEADERS):
      return False, f"TABLE-5: unexpected headers: {header_line!r}"

    self.table5_rows = []
    self.table5_exp_total = None

    for line in data_lines:
      parts = line.split()
      if len(parts) != 6:
        return False, f"TABLE-5: row has {len(parts)} fields, expected 6: {line!r}"

      operator = parts[0]

      ok, undesired = self.parse_int(parts[1])
      if not ok:
        return False, f"TABLE-5: unparseable int in 'Undesired State': {parts[1]!r}"

      ok, system_err = self.parse_int(parts[2])
      if not ok:
        return False, f"TABLE-5: unparseable int in 'System Error': {parts[2]!r}"

      ok, operator_err = self.parse_int(parts[3])
      if not ok:
        return False, f"TABLE-5: unparseable int in 'Operator Error': {parts[3]!r}"

      ok, recovery_fail = self.parse_int(parts[4])
      if not ok:
        return False, f"TABLE-5: unparseable int in 'Recovery Failure': {parts[4]!r}"

      ok, total = self.parse_int(parts[5])
      if not ok:
        return False, f"TABLE-5: unparseable int in 'Total': {parts[5]!r}"

      row = Table5Row(
        operator=operator,
        undesired_state=undesired,
        system_error=system_err,
        operator_error=operator_err,
        recovery_failure=recovery_fail,
        total=total,
      )
      self.table5_rows.append(row)

      if operator == "Total":
        self.table5_exp_total = total

    if self.table5_exp_total is None:
      return False, "TABLE-5: missing 'Total' row"

    return True, ""

  def load_table5_reference(self) -> Tuple[bool, str]:
    """
    Load TABLE-5 reference JSON.
    """
    path = self.table5_reference_path

    if not path.exists():
      return False, f"{path} not found"

    try:
      raw = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as e:
      return False, f"{path} invalid JSON: {e}"

    if not isinstance(raw, dict):
      return False, f"{path} must contain a JSON object"

    totals = raw.get("totals")
    if not isinstance(totals, dict):
      return False, f"{path} missing 'totals' object"

    if "total_all" not in totals:
      return False, f"{path} missing 'total_all' field in 'totals'"

    try:
      self.table5_ref_total = int(totals["total_all"])
    except (TypeError, ValueError):
      return False, f"{path} field 'totals.total_all' must be an integer"

    return True, ""

  # -----------------------
  # TABLE-6 helpers
  # -----------------------

  def load_table6(self) -> Tuple[bool, str]:
    """
    Load raw TABLE-6 file into memory.
    """
    if not self.table6_reference_path.exists():
      return False, f"{self.table6_reference_path} (TABLE-6 reference) not found"

    if not self.table6_results_path.exists():
      return False, f"{self.table6_results_path} (TABLE-6 results) not found"

    text = self.table6_results_path.read_text(encoding="utf-8")
    lines = [line.rstrip("\n") for line in text.splitlines() if line.strip()]
    if not lines:
      return False, f"{self.table6_results_path} is empty"

    self._table6_raw_lines = lines
    return True, ""

  def parse_table6(self) -> Tuple[bool, str]:
    """
    Parse TABLE-6 and compute the sum of all '# Bugs' values.
    """
    EXPECTED_HEADERS: list[str] = [
      "Consequence",
      "# Bugs",
    ]

    header_line: str | None = None
    data_lines: list[str] = []
    saw_separator = False

    for line in self._table6_raw_lines:
      if header_line is None:
        header_line = line
        continue

      if not saw_separator and self.is_separator_line(line):
        saw_separator = True
        continue

      if saw_separator:
        data_lines.append(line)

    if header_line is None:
      return False, "TABLE-6: no table header found"

    if any(h not in header_line for h in EXPECTED_HEADERS):
      return False, f"TABLE-6: unexpected headers: {header_line!r}"

    self.table6_rows = []
    self.table6_exp_total = 0

    for line in data_lines:
      parts = line.split()
      if len(parts) < 2:
        return False, f"TABLE-6: row has {len(parts)} fields, expected at least 2: {line!r}"

      label = " ".join(parts[:-1])
      bugs_str = parts[-1]

      ok, bugs = self.parse_int(bugs_str)
      if not ok:
        return False, f"TABLE-6: unparseable int in '# Bugs': {bugs_str!r}"

      row = Table6Row(
        symptom=label,
        bugs=bugs,
      )
      self.table6_rows.append(row)
      self.table6_exp_total += bugs

    return True, ""

  def load_table6_reference(self) -> Tuple[bool, str]:
    """
    Load TABLE-6 reference JSON.
    """
    path = self.table6_reference_path

    if not path.exists():
      return False, f"{path} not found"

    try:
      raw = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as e:
      return False, f"{path} invalid JSON: {e}"

    if not isinstance(raw, dict):
      return False, f"{path} must contain a JSON object"

    symptoms = raw.get("symptoms")
    if not isinstance(symptoms, list):
      return False, f"{path} missing 'symptoms' list"

    total = 0
    for idx, obj in enumerate(symptoms):
      if not isinstance(obj, dict):
        return False, f"{path} entry #{idx} in 'symptoms' is not an object"
      if "bugs" not in obj:
        return False, f"{path} entry #{idx} in 'symptoms' missing 'bugs' tag"
      try:
        total += int(obj["bugs"])
      except (TypeError, ValueError):
        return False, f"{path} entry #{idx} in 'symptoms' has non-integer 'bugs' tag"

    self.table6_ref_total = total
    return True, ""

  # -----------------------
  # TABLE-7 helpers
  # -----------------------

  def load_table7(self) -> Tuple[bool, str]:
    """
    Load raw TABLE-7 file into memory.
    """
    if not self.table7_reference_path.exists():
      return False, f"{self.table7_reference_path} (TABLE-7 reference) not found"

    if not self.table7_results_path.exists():
      return False, f"{self.table7_results_path} (TABLE-7 results) not found"

    text = self.table7_results_path.read_text(encoding="utf-8")
    lines = [line.rstrip("\n") for line in text.splitlines() if line.strip()]
    if not lines:
      return False, f"{self.table7_results_path} is empty"

    self._table7_raw_lines = lines
    return True, ""

  def parse_table7(self) -> Tuple[bool, str]:
    """
    Parse TABLE-7 and compute the sum of integer bug counts (ignoring percentages).
    """
    EXPECTED_HEADERS: list[str] = [
      "Test Oracle",
      "# Bugs (Percentage)",
    ]

    header_line: str | None = None
    data_lines: list[str] = []
    saw_separator = False

    for line in self._table7_raw_lines:
      if header_line is None:
        header_line = line
        continue

      if not saw_separator and self.is_separator_line(line):
        saw_separator = True
        continue

      if saw_separator:
        data_lines.append(line)

    if header_line is None:
      return False, "TABLE-7: no table header found"

    if any(h not in header_line for h in EXPECTED_HEADERS):
      return False, f"TABLE-7: unexpected headers: {header_line!r}"

    self.table7_rows = []
    self.table7_exp_total = 0

    for line in data_lines:
      parts = line.split()
      if len(parts) < 2:
        return False, f"TABLE-7: row has {len(parts)} fields, expected at least 2: {line!r}"

      # Ignore last token that is in "(xx.xx%)" format, the integer is second last.
      last = parts[-1]
      if last.startswith("(") and last.endswith("%)"):
        if len(parts) < 3:
          return False, f"TABLE-7: malformed row with percentage but no integer: {line!r}"
        bugs_str = parts[-2]
        label = " ".join(parts[:-2])
      else:
        bugs_str = parts[-1]
        label = " ".join(parts[:-1])

      ok, bugs = self.parse_int(bugs_str)
      if not ok:
        return False, f"TABLE-7: unparseable int in '# Bugs': {bugs_str!r}"

      row = Table7Row(
        test_oracle=label,
        bugs=bugs,
      )
      self.table7_rows.append(row)
      self.table7_exp_total += bugs

    return True, ""

  def load_table7_reference(self) -> Tuple[bool, str]:
    """
    Load TABLE-7 reference JSON.
    """
    path = self.table7_reference_path

    if not path.exists():
      return False, f"{path} not found"

    try:
      raw = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as e:
      return False, f"{path} invalid JSON: {e}"

    if not isinstance(raw, dict):
      return False, f"{path} must contain a JSON object"

    test_oracles = raw.get("test_oracles")
    if not isinstance(test_oracles, list):
      return False, f"{path} missing 'test_oracles' list"

    total = 0
    for idx, obj in enumerate(test_oracles):
      if not isinstance(obj, dict):
        return False, f"{path} entry #{idx} in 'test_oracles' is not an object"
      if "bugs" not in obj:
        return False, f"{path} entry #{idx} in 'test_oracles' missing 'bugs' tag"
      try:
        total += int(obj["bugs"])
      except (TypeError, ValueError):
        return False, f"{path} entry #{idx} in 'test_oracles' has non-integer 'bugs' tag"

    self.table7_ref_total = total
    return True, ""

  # -----------------------
  # TABLE-8 helpers
  # -----------------------

  def load_table8(self) -> Tuple[bool, str]:
    """
    Load raw TABLE-8 file into memory.
    """
    if not self.table8_reference_path.exists():
      return False, f"{self.table8_reference_path} (TABLE-8 reference) not found"

    if not self.table8_results_path.exists():
      return False, f"{self.table8_results_path} (TABLE-8 results) not found"

    text = self.table8_results_path.read_text(encoding="utf-8")
    lines = [line.rstrip("\n") for line in text.splitlines() if line.strip()]
    if not lines:
      return False, f"{self.table8_results_path} is empty"

    self._table8_raw_lines = lines
    return True, ""

  def parse_table8(self) -> Tuple[bool, str]:
    """
    Parse TABLE-8 and compute the sum of '# Operations'.
    """
    EXPECTED_HEADERS: list[str] = [
      "Operator",
      "# Operations",
    ]

    header_line: str | None = None
    data_lines: list[str] = []
    saw_separator = False

    for line in self._table8_raw_lines:
      if header_line is None:
        header_line = line
        continue

      if not saw_separator and self.is_separator_line(line):
        saw_separator = True
        continue

      if saw_separator:
        data_lines.append(line)

    if header_line is None:
      return False, "TABLE-8: no table header found"

    if any(h not in header_line for h in EXPECTED_HEADERS):
      return False, f"TABLE-8: unexpected headers: {header_line!r}"

    self.table8_rows = []
    self.table8_exp_total = 0

    for line in data_lines:
      parts = line.split()
      if len(parts) != 2:
        return False, f"TABLE-8: row has {len(parts)} fields, expected 2: {line!r}"

      operator = parts[0]
      ops_str = parts[1]

      ok, ops = self.parse_int(ops_str)
      if not ok:
        return False, f"TABLE-8: unparseable int in '# Operations': {ops_str!r}"

      row = Table8Row(
        operator=operator,
        operations=ops,
      )
      self.table8_rows.append(row)
      self.table8_exp_total += ops

    return True, ""

  def load_table8_reference(self) -> Tuple[bool, str]:
    """
    Load TABLE-8 reference JSON.
    """
    path = self.table8_reference_path

    if not path.exists():
      return False, f"{path} not found"

    try:
      raw = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as e:
      return False, f"{path} invalid JSON: {e}"

    if not isinstance(raw, dict):
      return False, f"{path} must contain a JSON object"

    operators = raw.get("operators")
    if not isinstance(operators, list):
      return False, f"{path} missing 'operators' list"

    total = 0
    for idx, obj in enumerate(operators):
      if not isinstance(obj, dict):
        return False, f"{path} entry #{idx} in 'operators' is not an object"
      if "operations" not in obj:
        return False, f"{path} entry #{idx} in 'operators' missing 'operations' tag"
      try:
        total += int(obj["operations"])
      except (TypeError, ValueError):
        return False, f"{path} entry #{idx} in 'operators' has non-integer 'operations'"

    self.table8_ref_total = total
    return True, ""

  # -----------------------
  # Shared comparison logic
  # -----------------------

  def totals_within_tolerance(self, found: int, ref: int) -> bool:
    """
    Check whether two values are within a given tolerance.
    """
    if ref == 0:
      return False
    return abs(found - ref) <= (1.0 - SIMILARITY_RATIO) * max(abs(found), abs(ref))

  def compare_table5_against_reference(self) -> Tuple[bool, str]:
    """
    Compare TABLE-5 total with the reference total.
    """
    if self.table5_exp_total is None:
      return False, "TABLE-5: bottom-right total not parsed"

    if self.table5_ref_total is None:
      return False, "TABLE-5: reference total_all not loaded"

    found = self.table5_exp_total
    ref = self.table5_ref_total

    if not self.totals_within_tolerance(found, ref):
      return False, (
        "TABLE-5: bottom-right total differs too much "
        f"(got {found}, ref {ref})"
      )

    return True, ""

  def compare_table6_against_reference(self) -> Tuple[bool, str]:
    """
    Compare TABLE-6 total with the reference total.
    """
    if self.table6_exp_total is None:
      return False, "TABLE6: sum of bugs not computed"

    if self.table6_ref_total is None:
      return False, "TABLE6: reference total_all not loaded"

    found = self.table6_exp_total
    ref = self.table6_ref_total

    if not self.totals_within_tolerance(found, ref):
      return False, (
        "TABLE6: total bugs differs too much "
        f"(got {found}, ref {ref})"
      )

    return True, ""

  def compare_table7_against_reference(self) -> Tuple[bool, str]:
    """
    Compare TABLE-7 total with the reference total.
    """
    if self.table7_exp_total is None:
      return False, "TABLE7: sum of bugs not computed"

    if self.table7_exp_total is None:
      return False, "TABLE7: reference total not loaded"

    found = self.table7_exp_total
    ref = self.table7_ref_total

    if not self.totals_within_tolerance(found, ref):
      return False, (
        "TABLE7: total bugs differs too much "
        f"(got {found}, ref {ref})"
      )

    return True, ""

  def compare_table8_against_reference(self) -> Tuple[bool, str]:
    """
    Compare TABLE-8 total with the reference total.
    """
    if self.table8_exp_total is None:
      return False, "TABLE8: sum of operations not computed"

    if self.table8_ref_total is None:
      return False, "TABLE8: reference total not loaded"

    found = self.table8_exp_total
    ref = self.table8_ref_total

    if not self.totals_within_tolerance(found, ref):
      return False, (
        "TABLE8: total operations differs too much "
        f"(got {found}, ref {ref})"
      )

    return True, ""

  # -----------------------
  # Invocations
  # -----------------------

  def _run_table(self, label: str, steps):
    """
    Run all steps for a single table, stopping on first failure.
    """
    for step in steps:
      ok, why = step()
      if not ok:
        suffix = f" - {why}" if why else ""
        logger.error(f"{label}: FAIL{suffix}")
        return False

    logger.info(f"{label}: PASS")
    return True

  def run_table5(self) -> bool:
    return self._run_table(
      "TABLE-5",
      [
        self.load_table5,
        self.parse_table5,
        self.load_table5_reference,
        self.compare_table5_against_reference,
      ],
    )

  def run_table6(self) -> bool:
    return self._run_table(
      "TABLE-6",
      [
        self.load_table6,
        self.parse_table6,
        self.load_table6_reference,
        self.compare_table6_against_reference,
      ],
    )

  def run_table7(self) -> bool:
    return self._run_table(
      "TABLE-7",
      [
        self.load_table7,
        self.parse_table7,
        self.load_table7_reference,
        self.compare_table7_against_reference,
      ],
    )

  def run_table8(self) -> bool:
    return self._run_table(
      "TABLE-8",
      [
        self.load_table8,
        self.parse_table8,
        self.load_table8_reference,
        self.compare_table8_against_reference,
      ],
    )

  def run(self):
    """
    Run all table checks and return True only if every table passes.
    Each table logs exactly one line: PASS or the first failure.
    """
    results: list[bool] = []

    results.append(self.run_table5())
    results.append(self.run_table6())
    results.append(self.run_table7())
    results.append(self.run_table8())

    return all(results)
