***********************
The CS:APP Architecture Lab
Directions to Students
***********************

Goal: optimize the pipelined Y86-64 implementation so that the benchmark ncopy.ys runs correctly and achieves average CPE ≤ 10.5 on the provided pipeline simulator.

What you must produce
---------------------
Modify the code under sim/ as needed, then provide optimized sources in place (most commonly:
- sim/pipe/ncopy.ys (optimize the loop)
- optionally HCL files such as sim/pipe/pipe-*.hcl if you choose microarchitectural changes)

Artifacts required for grading (already referenced in config.json):
- sim/pipe/ncopy.ys (always)
- sim/pipe/pipe-std.hcl, sim/pipe/pipe-full.hcl, sim/pipe/pipe-lf.hcl, sim/pipe/pipe-nt.hcl, sim/pipe/pipe-btfnt.hcl (if modified)

Resources provided
------------------
- sim/misc/: yas, yis, hcl2c, etc.
- sim/pipe/: pipeline simulator sources, HCL specs, benchmark/correctness scripts, baseline ncopy.ys
- sim/seq/: SEQ simulator sources (optional for reference)
- make targets: from sim/, run `make all GUIMODE= TKLIBS= TKINC=` to build TTY tools; from sim/pipe, run `make drivers` to regenerate drivers.

How evaluation works
--------------------
1) Setup builds TTY simulators (no GUI) and patches Makefiles for modern GCC.
2) Correctness: in sim/pipe, `./correctness.pl -q -p -f ncopy.ys` (pipeline mode). Must pass.
3) Performance: `./benchmark.pl -q -f ncopy.ys` is run; the Average CPE must be ≤ 10.5 (per lab rubric, full credit ≤ 7.5 but threshold set to 10.5 here).

Tips
----
- Start with ncopy.ys loop unrolling and strength reduction; measure with benchmark.pl.
- Use `make drivers` after changing ncopy.ys so the small/large drivers rebuild.
- `psim` is built in TTY mode; no Tcl/Tk needed.
- Keep code size reasonable (correctness.pl enforces byte limit default 1000).

Submission checklist
--------------------
- sim/pipe/ncopy.ys exists and assembles.
- correctness and benchmark scripts run without errors; Average CPE ≤ 10.5.
- Do not delete provided infra files (checked by checksums for benchmark/correctness scripts and tools).
