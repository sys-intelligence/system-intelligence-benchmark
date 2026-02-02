***********************
The CS:APP Buffer Lab
Directions to Students
***********************

Goal: craft five exploit payloads that drive the IA32 buffer bomb through all levels without triggering misfires.

What you must produce
---------------------
Create these hex-encoded payload files in the workspace root:

- smoke.txt  : exploit for smoke level, calls smoke()
- fizz.txt   : exploit for fizz level, calls fizz(cookie)
- bang.txt   : exploit for bang level, sets global_value to cookie
- boom.txt   : exploit for boom level, makes getbuf return desired address
- kaboom.txt : exploit for kaboom level (hardest), makes getbufn return desired address

Each file must contain whitespace-separated hex byte pairs (input format for hex2raw). Keep provided binaries unmodified.

Resources provided
------------------
- bufbomb   : vulnerable binary with levels smoke/fizz/bang/boom/kaboom
- hex2raw   : converts hex text to raw bytes
- makecookie: computes your cookie from userid (use agent007 as in grader)
- README.md : original lab handout excerpt

How evaluation works
--------------------
For each phase, the grader runs:

1) ./hex2raw < phase.txt > /tmp/raw_phase
2) cat /tmp/raw_phase | ./bufbomb -u agent007

A phase passes only if the program exits 0, prints the corresponding success string (Smoke!/Fizz!/Bang!/Boom!/KABOOM!), and does not print "Misfire". Cookies are derived from `./makecookie agent007`.

Tips
----
- Use objdump -d and gdb to inspect bufbomb and stack frames; disable ASLR is attempted in setup.
- For fizz/bang, the cookie is a 32-bit value; embed it in little-endian form as required.
- For boom/kaboom, you will need to redirect control flow to supplied code or gadgets; study saved registers and buffer layout carefully.
- You can regenerate payloads repeatedly; only the final smoke.txt..kaboom.txt files are checked.

Submission checklist
--------------------
- smoke.txt .. kaboom.txt exist and are non-empty
- Only hex bytes in files; binaries unchanged (checksummed during evaluation)
