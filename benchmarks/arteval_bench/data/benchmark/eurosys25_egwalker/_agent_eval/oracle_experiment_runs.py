#!/usr/bin/env python3
import json
import os
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

from utils import REPO_DIR
from utils import REFERENCE_RESULTS_FILE
from utils import SIMILARITY_RATIO
from utils import logger


class OracleExperimentRuns:
  def __init__(self) -> None:
    self.repo_dir = Path(os.path.expanduser(str(REPO_DIR)))
    self.timings_file = self.repo_dir / "results" / "timings.json"
    self.reference_file = Path(os.path.expanduser(str(REFERENCE_RESULTS_FILE)))
    self.max_mismatches_to_report = (1 - SIMILARITY_RATIO)

  def load_json(self, path: Path) -> Tuple[Optional[Any], str]:
    """
    Load JSON from disk and return (obj, err).
    """
    if not path.exists():
      return None, f"missing json: {path}"
    try:
      with path.open("r", encoding="utf-8") as f:
        return json.load(f), ""
    except Exception as e:
      return None, f"unreadable json: {path} ({e})"

  def as_float(self, v: Any) -> Optional[float]:
    if isinstance(v, (int, float)):
      return float(v)
    return None

  def ratios_within_tolerance(self, actual: float, ref: float) -> Tuple[bool, float]:
    """
    Check whether two measurements are within tolerance.
    """
    if abs(ref) < 1e-12:
      if abs(actual) < 1e-12:
        return True, 0.0
      return False, float("inf")

    rel_diff = abs(actual - ref) / abs(ref)
    return rel_diff <= (1.0 - float(SIMILARITY_RATIO)), rel_diff

  def compare_timings(
      self,
      actual: Dict[str, Any],
      reference: Dict[str, Any],
    ) -> Tuple[bool, str]:
      """
      Compare current timings with the original, reference timings.
      """
      if not isinstance(actual, dict) or not isinstance(reference, dict):
        return False, "timings json invalid format (expected object at top-level)"

      missing: List[str] = []
      mismatches: List[str] = []
      total = 0
      ok_count = 0

      for metric_name, ref_metric in reference.items():
        if not isinstance(ref_metric, dict):
          missing.append(f"{metric_name}: invalid reference section (expected object)")
          continue

        act_metric = actual.get(metric_name)
        if not isinstance(act_metric, dict):
          missing.append(f"{metric_name}: missing metric")
          continue

        for tag, ref_stats in ref_metric.items():
          if not isinstance(ref_stats, dict):
            missing.append(f"{metric_name}.{tag}: invalid reference tag (expected object)")
            continue

          act_stats = act_metric.get(tag)
          if not isinstance(act_stats, dict):
            missing.append(f"{metric_name}.{tag}: missing tag")
            continue

          for field, ref_val_raw in ref_stats.items():
            total += 1

            if field not in act_stats:
              missing.append(f"{metric_name}.{tag}.{field}: missing field")
              continue

            ref_val = self.as_float(ref_val_raw)
            act_val = self.as_float(act_stats.get(field))

            if ref_val is None:
              missing.append(f"{metric_name}.{tag}.{field}: non-numeric reference value")
              continue
            if act_val is None:
              missing.append(f"{metric_name}.{tag}.{field}: non-numeric actual value")
              continue

            ok, sim = self.ratios_within_tolerance(act_val, ref_val)
            if ok:
              ok_count += 1
            else:
              mismatches.append(
                f"{metric_name}.{tag}.{field}: {act_val} vs {ref_val} (similarity {sim:.3f} < {SIMILARITY_RATIO})"
              )

      if missing or mismatches:
        parts: List[str] = []
        summary = f"{ok_count}/{total} fields meet similarity ratio" if total else "0 fields compared"
        if missing:
          parts.append("missing/invalid: " + "; ".join(missing))
        if mismatches:
          parts.append("measurement difference: " + "; ".join(mismatches))
        return False, summary + " - " + " | ".join(parts)

      summary = f"{ok_count}/{total} fields meet similarity ratio" if total else "no reference fields to compare"
      return True, summary

  def run(self) -> bool:
    actual_obj, err = self.load_json(self.timings_file)
    if err:
      logger.info(f"Timings: FAIL - {err}")
      return False

    ref_obj, err = self.load_json(self.reference_file)
    if err:
      logger.info(f"Timings: FAIL - {err}")
      return False

    ok, why = self.compare_timings(actual_obj, ref_obj)
    logger.info(f"Timings: {'PASS' if ok else 'FAIL' + (' - ' + why if why else '')}")
    return ok
