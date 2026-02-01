import subprocess
import pandas as pd
import os
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Optional, Tuple
from utils import HOME, REPO_DIRS, logger, FIG18_REFERENCE_PATH, FIG18_RESULT_PATH, TOLERANCE

# ./collect_data.sh --output ./data/EMT
# (emt) python ipc_with_inst.py --input ./data/EMT --output ./ipc_stats --thp never
# (emt/VM-Bench/) python ./run_scripts/get_unified_kern_inst_ae.py) --input ./data/EMT --output ./inst_stats --thp never

@dataclass(frozen=True)
class Figure16Result:
  radix_page_faults: float
  radix_others: float
  radix_system_calls: float
  radix_timers: float
  radix_thp: float
  ecpt_page_faults: float
  ecpt_others: float
  ecpt_system_calls: float
  ecpt_timers: float
  ecpt_thp: float

@dataclass(frozen=True)
class Figure18Result:
  ipc_speedup: float
  e2e_speedup: float
  pgwalk_speedup: float

class OracleExperimentRuns:
  def __init__(self):
    self.figure16_never_result = None  # type: Optional[Figure16Result]
    self.figure16_never_reference = None  # type: Optional[Figure16Result]

    self.figure16_always_result = None  # type: Optional[Figure16Result]
    self.figure16_always_reference = None  # type: Optional[Figure16Result]

    self.figure18_result = None  # type: Optional[Figure18Result]
    self.figure18_reference = None  # type: Optional[Figure18Result]
        
  def run_shell_command(self, cmd: Iterable[str], cwd: Optional[str] = None) -> Tuple[int, str, str]:
    """
    Run a command and return (rc, stdout, stderr) tuple.
    """
    try:
      cp = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, cwd=cwd)
      return cp.returncode, cp.stdout or "", cp.stderr or ""
    except FileNotFoundError:
      return 127, "", ""
    
  def run_experiment(self) -> Tuple[bool, str]:
    code, _, _ = self.run_shell_command(["./collect_data.sh", "--output", "./data/EMT"], cwd=REPO_DIRS["emt"])
    if code != 0:
      return False, "Data collection failed"
    return True, ""
    
  def generate_figure16_stat(self) -> Tuple[bool, str]:
    code, stdout, stderr = self.run_shell_command(["python", "run_scripts/get_unified_kern_inst_ae.py", "--input", REPO_DIRS["emt"] / "data" / "EMT", "--output", REPO_DIRS["emt"] / "inst_stats", "--thp", "never"], cwd=REPO_DIRS["emt"] / "VM-Bench")
    if code != 0:
      return False, f"Figure 16 statistics generation failed, code {code}\nSTDOUT: {stdout}\nSTDERR: {stderr}"
      # return False, f"Figure 16 statistics generation failed"
    
    df_stats_never = pd.read_csv(REPO_DIRS["emt"] / "inst_stats" / "kern_inst_never_unified.csv")
    # df_stats_always = pd.read_csv(REPO_DIRS["emt"] / "inst_stats" / "kern_inst_always_unified.csv")

    def result_from_df(df_stats: pd.DataFrame) -> Figure16Result:
      return Figure16Result(
        radix_page_faults = df_stats[(df_stats["system"] == "x86") & (df_stats["function"] == "Page Faults")]["instruction"].mean(),
        radix_others = df_stats[(df_stats["system"] == "x86") & (df_stats["function"] == "Others")]["instruction"].mean(),
        radix_system_calls = df_stats[(df_stats["system"] == "x86") & (df_stats["function"] == "System Calls")]["instruction"].mean(),
        radix_timers = df_stats[(df_stats["system"] == "x86") & (df_stats["function"] == "Timers")]["instruction"].mean(),
        radix_thp = df_stats[(df_stats["system"] == "x86") & (df_stats["function"] == "khugepaged (THP)")]["instruction"].mean(),
        ecpt_page_faults = df_stats[(df_stats["system"] == "ecpt") & (df_stats["function"] == "Page Faults")]["instruction"].mean(),
        ecpt_others = df_stats[(df_stats["system"] == "ecpt") & (df_stats["function"] == "Others")]["instruction"].mean(),
        ecpt_system_calls = df_stats[(df_stats["system"] == "ecpt") & (df_stats["function"] == "System Calls")]["instruction"].mean(),
        ecpt_timers = df_stats[(df_stats["system"] == "ecpt") & (df_stats["function"] == "Timers")]["instruction"].mean(),
        ecpt_thp = df_stats[(df_stats["system"] == "ecpt") & (df_stats["function"] == "khugepaged (THP)")]["instruction"].mean(),
      )
    
    self.figure16_never_result = result_from_df(df_stats_never)
    # self.figure16_always_result = result_from_df(df_stats_always)

    return True, ""

  def load_figure16_reference(self) -> Tuple[bool, str]:
    self.figure16_never_reference = Figure16Result(
      radix_page_faults = 0.7300383652855216,
      radix_others = 0.023351508560737654,
      radix_system_calls = 0.20650121781958858,
      radix_timers = 0.04010890833415209,
      radix_thp = 0.0,
      ecpt_page_faults = 1.262443177100101,
      ecpt_others = 0.013669409823525998,
      ecpt_system_calls = 0.22014200872491743,
      ecpt_timers = 0.040398944294302463,
      ecpt_thp = 0.0,
    )

    self.figure16_always_reference = Figure16Result(
      radix_page_faults = 0.6617443111482841,
      radix_others = 0.07205365193671859,
      radix_system_calls = 0.02206782784289519,
      radix_timers = 0.1850494536794656,
      radix_thp = 0.059084755392636586,
      ecpt_page_faults = 1.864657196481908,
      ecpt_others = 0.08507021659294173,
      ecpt_system_calls = 0.012568461521228296,
      ecpt_timers = 0.20019270017105809,
      ecpt_thp = 0.03892931365299785,
    )

    return True, ""

  def compare_figure16_against_reference(self) -> Tuple[bool, str]:
    if self.figure16_never_result is None:
      return False, "Figure 16 results (never) not loaded"
    # if self.figure16_always_result is None:
    #   return False, "Figure 16 results (always) not loaded"
    if self.figure16_never_reference is None:
      return False, "Figure 16 reference (never) not loaded"
    # if self.figure16_always_reference is None:
    #   return False, "Figure 16 reference (always) not loaded"

    def within_tolerance(measured: float, reference: float) -> bool:
      ratio = measured / reference
      return ratio >= (1 - TOLERANCE) and ratio <= (1 + TOLERANCE)

    def check_within_tolerance(result: Figure16Result, reference: Figure16Result, thp: str) -> Tuple[bool, str]:
      if not within_tolerance(result.radix_page_faults, reference.radix_page_faults):
        return False, f"Radix Page Faults do not match reference for THP={thp}"
      if not within_tolerance(result.radix_others, reference.radix_others):
        return False, f"Radix Others do not match reference for THP={thp}"
      if not within_tolerance(result.radix_system_calls, reference.radix_system_calls):
        return False, f"Radix System Calls do not match reference for THP={thp}"
      if not within_tolerance(result.radix_timers, reference.radix_timers):
        return False, f"Radix Timers do not match reference for THP={thp}"
      if not within_tolerance(result.radix_thp, reference.radix_thp):
        return False, f"Radix THP do not match reference for THP={thp}"
      if not within_tolerance(result.ecpt_page_faults, reference.ecpt_page_faults):
        return False, f"ECPT Page Faults do not match reference for THP={thp}"
      if not within_tolerance(result.ecpt_others, reference.ecpt_others):
        return False, f"ECPT Others do not match reference for THP={thp}"
      if not within_tolerance(result.ecpt_system_calls, reference.ecpt_system_calls):
        return False, f"ECPT System Calls do not match reference for THP={thp}"
      if not within_tolerance(result.ecpt_timers, reference.ecpt_timers):
        return False, f"ECPT Timers do not match reference for THP={thp}"
      if not within_tolerance(result.ecpt_thp, reference.ecpt_thp):
        return False, f"ECPT THP do not match reference for THP={thp}"
      return True, ""
    
    ok, why = check_within_tolerance(self.figure16_never_result, self.figure16_never_reference, "never")
    if not ok:
      return False, why

    # ok, why = check_within_tolerance(self.figure16_always_result, self.figure16_always_reference, "always")
    if not ok:
      return False, why

    return True, ""

  def generate_figure18_stat(self) -> Tuple[bool, str]:
    code, _, _ = self.run_shell_command(["python", "ipc_with_inst.py", "--input", "./data/EMT", "--output", "./ipc_stats", "--thp", "never"], cwd=REPO_DIRS["emt"])
    if code != 0:
      return False, "Figure 18 statistics generation failed"
    
    df_radix = pd.read_csv(REPO_DIRS["emt"] / "ipc_stats" / "ipc_unified_never_radix_result.csv")
    df_ecpt = pd.read_csv(REPO_DIRS["emt"] / "ipc_stats" / "ipc_unified_never_ecpt_result.csv")

    ipc_speedup = (df_ecpt["ipc"].mean() / df_radix["ipc"].mean())
    e2e_speedup = (df_radix["total_cycles"].mean() / df_ecpt["total_cycles"].mean())
    pgwalk_speedup = (df_radix["page_walk_latency"].mean() / df_ecpt["page_walk_latency"].mean())

    self.figure18_result = Figure18Result(
      ipc_speedup=ipc_speedup,
      e2e_speedup=e2e_speedup,
      pgwalk_speedup=pgwalk_speedup,
    )

    # print(f"Figure 18 Results:\nIPC Speedup: {ipc_speedup:.4f}\nE2E Speedup: {e2e_speedup:.4f}\nPage Walk Speedup: {pgwalk_speedup:.4f}")
    return True, ""
  
  def load_figure18_reference(self) -> Tuple[bool, str]:
    try:
      # df_ref = pd.read_csv(FIG18_REFERENCE_PATH)
      # ref_ipc_speedup = df_ref["ipc_speedup"].iloc[0]
      # ref_e2e_speedup = df_ref["e2e_speedup"].iloc[0]
      # ref_pgwalk_speedup = df_ref["pgwalk_speedup"].iloc[0]

      self.figure18_reference = Figure18Result(
        ipc_speedup=1.044740928,
        e2e_speedup=1.007018443,
        pgwalk_speedup=1.224302584,
      )
      return True, ""
    except Exception as e:
      return False, f"Failed to load Figure 18 reference: {e}"
    
  def compare_figure18_against_reference(self) -> Tuple[bool, str]:
    if self.figure18_result is None:
      return False, "Figure 18 results not loaded"
    if self.figure18_reference is None:
      return False, "Figure 18 reference not loaded"

    def within_tolerance(measured: float, reference: float) -> bool:
      ratio = measured / reference
      return ratio >= (1 - TOLERANCE) and ratio <= (1 + TOLERANCE)
    
    if not within_tolerance(self.figure18_result.ipc_speedup, self.figure18_reference.ipc_speedup):
      return False, "IPC speedup does not match reference"
    if not within_tolerance(self.figure18_result.e2e_speedup, self.figure18_reference.e2e_speedup):
      return False, "E2E speedup does not match reference"
    if not within_tolerance(self.figure18_result.pgwalk_speedup, self.figure18_reference.pgwalk_speedup):
      return False, "Page walk speedup does not match reference"

    return True, ""

  def run(self) -> bool:
    ok, why = self.run_experiment()
    if not ok:
      logger.error(why)
      return False

    ok, why = self.generate_figure16_stat()
    if not ok:
      logger.error(why)
      return False

    ok, why = self.load_figure16_reference()
    if not ok:
      logger.error(why)
      return False

    ok, why = self.compare_figure16_against_reference()
    if not ok:  
      logger.error(why)
      return False
    
    ok, why = self.generate_figure18_stat()
    if not ok:
      logger.error(why)
      return False
    
    ok, why = self.load_figure18_reference()
    if not ok:
      logger.error(why)
      return False
    
    ok, why = self.compare_figure18_against_reference()
    if not ok:
      logger.error(why)
      return False
    
    return True
  
# if __name__ == "__main__":
#   OracleExperimentRuns().run()