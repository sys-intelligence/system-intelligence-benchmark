#!/usr/bin/env python3
import json
import os
from dataclasses import dataclass
from pathlib import Path
from typing import Any, List, Optional, Tuple

from utils import HOME
from utils import REPO_DIR
from utils import REFERENCE_BENCHMARK_FILE
from utils import logger


@dataclass(frozen=True)
class DatasetRef:
  filepath: str
  sizeinbytes: int


class OracleBenchmarkPrep:

  def __init__(self) -> None:
    self.home = Path(os.path.expanduser(str(HOME)))
    self.repo_path = Path(os.path.expanduser(str(REPO_DIR)))
    self.ref_json = Path(os.path.expanduser(str(REFERENCE_BENCHMARK_FILE)))

  def load_json(self, path: Path) -> Tuple[Optional[Any], str]:
    """
    Load JSON from disk and return (obj, err).
    """
    if not path.exists():
      return None, f"ref json missing: {path}"
    try:
      with path.open("r", encoding="utf-8") as f:
        return json.load(f), ""
    except Exception as e:
      return None, f"ref json unreadable: {e}"

  def iter_ref_entries(self, obj: Any) -> List[dict]:
    """
    Extract benchmark entries from a reference JSON.
    """
    if isinstance(obj, list):
      return [x for x in obj if isinstance(x, dict)]
    if isinstance(obj, dict):
      for v in obj.values():
        if isinstance(v, list) and v and all(isinstance(x, dict) for x in v):
          return v
    return []

  def parse_entry(self, d: dict) -> Tuple[Optional[DatasetRef], str]:
    """
    Parse a single JSON entry into DatasetRef.
    """
    if "filepath" not in d:
      return None, "missing filepath"
    if "sizeinbytes" not in d:
      return None, "missing sizeinbytes"

    fp = d.get("filepath", "")
    sz = d.get("sizeinbytes", None)

    if not isinstance(fp, str) or not fp:
      return None, "invalid filepath"
    if not isinstance(sz, int) or sz < 0:
      return None, "invalid sizeinbytes"

    return DatasetRef(filepath=fp, sizeinbytes=sz), ""

  def check_entry(self, ref: DatasetRef) -> Optional[str]:
    """
    Validate that dataset files exist and matche the expected sizes (in bytes).
    """
    rel = Path(ref.filepath)

    if rel.is_absolute():
      return f"{ref.filepath}: absolute paths not allowed"

    p = self.repo_path / rel
    if not p.exists():
      return f"{ref.filepath}: missing"
    if not p.is_file():
      return f"{ref.filepath}: not a file"

    try:
      actual = p.stat().st_size
    except OSError as e:
      return f"{ref.filepath}: stat failed ({e})"

    if actual != ref.sizeinbytes:
      return f"{ref.filepath}: size mismatch (expected {ref.sizeinbytes}, got {actual})"

    return None

  def datasets_check(self) -> Tuple[bool, str]:
    """
    Check all referenced dataset files are present and match expected sizes.
    """
    obj, err = self.load_json(self.ref_json)
    if err:
      return False, err

    entries = self.iter_ref_entries(obj)
    if not entries:
      return False, "no entries found in ref json"

    problems: List[str] = []
    for d in entries:
      ref, perr = self.parse_entry(d)
      if perr or ref is None:
        problems.append(perr or "invalid entry")
        continue

      msg = self.check_entry(ref)
      if msg:
        problems.append(msg)

    if problems:
      return False, "; ".join(problems)
    return True, ""

  def run(self) -> bool:
    ok, why = self.datasets_check()
    logger.info(f"Datasets: {'PASS' if ok else 'FAIL' + (' - ' + why if why else '')}")
    return ok