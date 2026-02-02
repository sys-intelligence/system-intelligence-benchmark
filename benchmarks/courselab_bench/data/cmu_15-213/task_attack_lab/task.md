***********************
The CS:APP Attack Lab
Directions to Students
***********************

Goal: craft five exploit payloads that drive the provided vulnerable
binaries to the target functions without triggering misfires.

What you must produce
---------------------
Create the following hex-encoded payload files in the workspace root:

- phase1.txt: exploit for ctarget that calls touch1
- phase2.txt: exploit for ctarget that calls touch2 with the correct cookie
- phase3.txt: exploit for ctarget that calls touch3 with the correct cookie string
- phase4.txt: exploit for rtarget that calls touch2 with the correct cookie
- phase5.txt: exploit for rtarget that calls touch3 with the correct cookie string

Each file should contain whitespace-separated hex byte pairs (the format
expected by hex2raw). Keep the binaries (ctarget, rtarget, hex2raw,
cookie.txt, farm.c, README.txt) unmodified; they are checksumed.

Resources provided
------------------
- ctarget: buffer-overflow target for phases 1-3 (code injection)
- rtarget: ROP target for phases 4-5
- cookie.txt: 4-byte signature required by touch2/touch3
- farm.c: gadget farm for rtarget (compile with -Og to study gadgets)
- hex2raw: converts hex text to raw bytes
- README.txt: original lab handout excerpt

How evaluation works
--------------------
For each phase, the grader runs:

1) ./hex2raw < phaseN.txt > /tmp/rawN
2) ./ctarget -q -i /tmp/rawN   # phases 1-3
   ./rtarget -q -i /tmp/rawN   # phases 4-5

A phase passes only if the program exits 0, prints the corresponding
"TouchX!" success message, and does not print "Misfire".

Tips
----
- Run with -q to suppress server submission: ./ctarget -q -i raw
- Use objdump -d and gdb to understand stack layout and gadgets.
- Phases 2/4 require the cookie as a 32-bit value; phases 3/5 require it
  as an ASCII string (little-endian on the stack).
- You can regenerate raw payloads repeatedly; cleaning files is fine as
  long as the final phase*.txt files remain present.

Submission checklist
--------------------
- phase1.txt ... phase5.txt exist and are non-empty
- Each file contains only hex bytes (no addresses of lab binaries altered)
- Protected binaries unchanged (checksummed during evaluation)
