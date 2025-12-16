import json
from dataclasses import dataclass
from pathlib import Path
from typing import Tuple

from utils import RESULTS_PATH, REFERENCE_PATH, SIMILARITY_RATIO, logger


@dataclass(frozen=True)
class TableRow:
  controller: str
  verified_anvil_mean: float
  verified_anvil_max: float
  reference_unverified_mean: float
  reference_unverified_max: float


class OracleExperimentRuns:

  def __init__(self) -> None:
    self.results_path = Path(RESULTS_PATH)
    self.reference_path = Path(REFERENCE_PATH)
    self.rows: list[TableRow] = []
    self.rows_by_controller: dict[str, TableRow] = {}
    self._raw_lines: list[str] = []

  def load(self) -> Tuple[bool, str]:
    """
    Load the raw table file into memory.
    """
    if not self.reference_path.exists():
      return False, f"{self.reference_path} (reference measurement) not found"
  
    if not self.results_path.exists():
      return False, f"{self.results_path} not found"

    text = self.results_path.read_text(encoding="utf-8")
    lines = [line.rstrip("\n") for line in text.splitlines() if line.strip()]
    if not lines:
      return False, f"{self.results_path} is empty"

    self._raw_lines = lines
    return True, ""

  def is_separator_line(self, line: str) -> bool:
    """
    Return True if this looks like the Markdown header separator line.
    """
    stripped = line.strip()
    if not stripped.startswith("|") or not stripped.endswith("|"):
      return False

    inner = stripped.replace("|", "").replace(" ", "")
    return bool(inner) and all(ch in "-:" for ch in inner)

  def parse_float(self, text: str) -> Tuple[bool, float]:
    """
    Parse a numeric string into a float.
    """
    try:
      return True, float(text.replace(",", ""))
    except ValueError:
      return False, 0.0

  def parse_table(self) -> Tuple[bool, str]:
    """
    Parse table saved in markdown format into rows and a dictionary keyed by controller.
    """
    EXPECTED_HEADERS: list[str] = [
      "Controller",
      "Verified (Anvil) Mean",
      "Verified (Anvil) Max",
      "Reference (unverified) Mean",
      "Reference (unverified) Max",
    ]

    def split_row(line: str) -> list[str]:
      """
      Split a markdown table row into individual cells.
      """
      return [cell.strip() for cell in line.strip().strip("|").split("|")]

    header_line: str | None = None
    data_lines: list[str] = []

    for line in self._raw_lines:
      if "|" not in line:
        # Not a table row, skip.
        continue

      if header_line is None:
        header_line = line
        continue

      if self.is_separator_line(line):
        # Skip the ---|--- header separator.
        continue

      # Remaining lines are data rows.
      data_lines.append(line)

    if header_line is None:
      return False, "No table header found"

    headers = split_row(header_line)
    if headers != EXPECTED_HEADERS:
      return False, f"Unexpected table headers: {headers!r}"

    self.rows = []
    self.rows_by_controller = {}

    for line in data_lines:
      cells = split_row(line)
      if len(cells) != len(EXPECTED_HEADERS):
        return False, f"Row has {len(cells)} cells, expected {len(EXPECTED_HEADERS)}: {line!r}"

      ok, verified_anvil_mean = self.parse_float(cells[1])
      if not ok:
        return False, f"Unparseable float in column 'Verified (Anvil) Mean': {cells[1]!r}"

      ok, verified_anvil_max = self.parse_float(cells[2])
      if not ok:
        return False, f"Unparseable float in column 'Verified (Anvil) Max': {cells[2]!r}"

      ok, reference_unverified_mean = self.parse_float(cells[3])
      if not ok:
        return False, f"Unparseable float in column 'Reference (unverified) Mean': {cells[3]!r}"

      ok, reference_unverified_max = self.parse_float(cells[4])
      if not ok:
        return False, f"Unparseable float in column 'Reference (unverified) Max': {cells[4]!r}"

      row = TableRow(
        controller=cells[0],
        verified_anvil_mean=verified_anvil_mean,
        verified_anvil_max=verified_anvil_max,
        reference_unverified_mean=reference_unverified_mean,
        reference_unverified_max=reference_unverified_max,
      )
      self.rows.append(row)
      self.rows_by_controller[row.controller] = row

    return True, ""

  def load_json_rows(self, path: Path) -> Tuple[bool, list[TableRow], str]:
    """
    Load TableRow entries from a JSON file.
    """
    if not path.exists():
      return False, [], f"{path} not found"

    try:
      raw = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as e:
      return False, [], f"{path} invalid JSON: {e}"

    if not isinstance(raw, list):
      return False, [], f"{path} must contain a list of objects"

    rows: list[TableRow] = []
    for idx, obj in enumerate(raw):
      if not isinstance(obj, dict):
        return False, [], f"{path} entry #{idx} is not an object"
      try:
        row = TableRow(
          controller=str(obj["controller"]),
          verified_anvil_mean=float(obj["verified_anvil_mean"]),
          verified_anvil_max=float(obj["verified_anvil_max"]),
          reference_unverified_mean=float(obj["reference_unverified_mean"]),
          reference_unverified_max=float(obj["reference_unverified_max"]),
        )
      except (KeyError, TypeError, ValueError) as e:
        return False, [], f"{path} malformed entry #{idx}: {e}"
      rows.append(row)

    return True, rows, ""

  def compute_ratios(self, row: TableRow) -> Tuple[float, float]:
    """
    Compute mean/max ratios (verified / reference) and compare with 
    similar ratios from reference measurements.
    """
    if row.reference_unverified_mean == 0.0:
      mean_ratio = float("inf")
    else:
      mean_ratio = row.verified_anvil_mean / row.reference_unverified_mean

    if row.reference_unverified_max == 0.0:
      max_ratio = float("inf")
    else:
      max_ratio = row.verified_anvil_max / row.reference_unverified_max

    return mean_ratio, max_ratio

  def ratios_within_tolerance(self, found: float, ref: float) -> bool:
    """
    Check whether two ratio values are within tolerance.
    """
    if ref == 0.0:
      return False
    return abs(found - ref) <= (1.0 - SIMILARITY_RATIO) * max(abs(found), abs(ref))

  def compare_against_reference(self) -> Tuple[bool, str]:
    """
    Compare current measurements (parsed from the markdown table) against
    reference measurements (loaded from JSON) using mean/max ratios.
    """
    if not self.rows_by_controller:
      return False, "No parsed rows available for comparison"

    ok, reference_rows, why = self.load_json_rows(self.reference_path)
    if not ok:
      return False, why

    ref_by_controller = {r.controller: r for r in reference_rows}
    problems: list[str] = []

    if len(self.rows_by_controller) != len(ref_by_controller):
      why = (
            f"Missing or mismatched results: got {len(self.rows_by_controller)}"
          + f", expected {len(ref_by_controller)}"
        )
      return False, why

    for controller, row in self.rows_by_controller.items():
      ref = ref_by_controller.get(controller)
      if ref is None:
        problems.append(f"Missing reference row for controller {controller}")
        continue

      mean_cur, max_cur = self.compute_ratios(row)
      mean_ref, max_ref = self.compute_ratios(ref)

      if not self.ratios_within_tolerance(mean_cur, mean_ref):
        problems.append(
          f"{controller} mean ratio differs too much "
          f"(got {mean_cur:.4f}, ref {mean_ref:.4f})"
        )

      if not self.ratios_within_tolerance(max_cur, max_ref):
        problems.append(
          f"{controller} max ratio differs too much "
          f"(got {max_cur:.4f}, ref {max_ref:.4f})"
        )

    if problems:
      return False, "; ".join(problems)

    return True, ""

  def run(self):
    results: list[bool] = []

    ok, why = self.load()
    logger.info(f"Table present: {'PASS' if ok else 'FAIL' + (' - ' + why if why else '')}")
    results.append(ok)

    ok, why = self.parse_table()
    logger.info(f"Table format: {'PASS' if ok else 'FAIL' + (' - ' + why if why else '')}")
    results.append(ok)

    ok, why = self.compare_against_reference()
    logger.info(f"Compare against reference: {'PASS' if ok else 'FAIL' + (' - ' + why if why else '')}")
    results.append(ok)

    if all(results):
      return True

    return False