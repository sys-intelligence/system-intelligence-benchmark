from __future__ import annotations
from dataclasses import dataclass
from pathlib import Path
import csv

from evaluator.utils import EntryConfig
from oracle_experiment_runs_primitives import (
    OracleExperimentRunsBase,
    ElementwiseSimilarityThresholdRequirement,
)

@dataclass(frozen=True)
class _BugKey:
  bug_type: str
  benchmark: str
  location: str

class OracleExperimentRuns(OracleExperimentRunsBase):
  _ORACLE_NAME = "WasabiExperimentRuns"

  def __init__(self, *, config: EntryConfig, logger) -> None:
    super().__init__(logger=logger)
    self._config = config
    self._results_root = config.results_paths["results_root"]
    self._gt_file = config.ground_truth_paths["bugs_ground_truth"]
    self._threshold = config.similarity_ratio

    self._prefix_map = config.metadata.get("benchmark_prefix_map", [])
    self._contains_rules = config.metadata.get("benchmark_contains_rules", [])
    self._glob = config.metadata.get("results_file_glob", "*.csv")

  def _classify_benchmark(self, loc: str) -> str:
    for bench, needles in self._contains_rules:
      if any(n in loc for n in needles):
        return bench
    for bench, prefixes in self._prefix_map:
      if any(loc.startswith(p) for p in prefixes):
        return bench
    return "unknown"

  def _load_ground_truth(self) -> dict[tuple[str, str], set[str]]:
    # key: (bug_type, benchmark) -> set(loc)
    out: dict[tuple[str, str], set[str]] = {}
    p = Path(self._gt_file)
    with p.open() as f:
      for line in f:
        bench, bug_type, loc = line.strip().split(",", 2)
        out.setdefault((bug_type, bench), set()).add(loc)
    return out

  def _load_observed(self) -> dict[tuple[str, str], set[str]]:
    out: dict[tuple[str, str], set[str]] = {}
    root = Path(self._results_root)
    for csv_path in root.rglob(self._glob):
      with csv_path.open(newline="") as f:
        reader = csv.reader(f)
        for row in reader:
          if not row:
            continue
          line = ",".join(row)
          if ("how-bug" not in line) and ("when-missing-" not in line):
            continue
          bug_type = row[1]
          bug_loc = row[2]
          bench = self._classify_benchmark(bug_loc)
          out.setdefault((bug_type, bench), set()).add(bug_loc)
    return out

  def requirements(self):
    gt = self._load_ground_truth()
    obs = self._load_observed()

    # Stable ordering over ground truth bug IDs
    buckets = sorted(gt.keys())

    ref_counts = []
    matched_counts = []

    for k in buckets:
      gt_locs = gt[k]
      obs_locs = obs.get(k, set())
      ref_counts.append(float(len(gt_locs)))
      matched_counts.append(float(len(gt_locs & obs_locs)))

    return [
      ElementwiseSimilarityThresholdRequirement(
        name="ground-truth-coverage-by-bucket",
        observed=matched_counts,
        reference=ref_counts,
        threshold=self._threshold,
      ),
    ]
