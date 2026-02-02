This file contains materials for one instance of the attacklab.

Files:

    ctarget

Linux binary with code-injection vulnerability.  To be used for phases
1-3 of the assignment.

    rtarget

Linux binary with return-oriented programming vulnerability.  To be
used for phases 4-5 of the assignment.

     cookie.txt

Text file containing 4-byte signature required for this lab instance.

     farm.c

Source code for gadget farm present in this instance of rtarget.  You
can compile (use flag -Og) and disassemble it to look for gadgets.

     hex2raw

Utility program to generate byte sequences.  See documentation in lab
handout.

##################################################
# CS:APP Attack Lab
# Directions to Instructors
#
# Copyright (c) 2016, R. Bryant and D. O'Hallaron
#
##################################################

This directory contains the files that you will use to build and run
the CS:APP Attack Lab. 

The purpose of the Attack Lab is to help students develop a detailed
understanding of the stack discipline on x86-64 processors.  It
involves applying a total of five buffer overflow attacks on some
executable files. There are three code injection attacks and two
return-oriented programming attacks.

The lab must be done on an x86-64 Linux system. It requires a version
of gcc that supports the -Og optimization flag (e.g., gcc
4.8.1). We've tested it at CMU on Ubuntu 12.4 systems.

***********
1. Overview
***********

---- 
1.1. Targets 
---- 
Students are given binaries called ctarget and rtarget that have a
buffer overflow bug.  They are asked to alter the behavior of their
targets via five increasingly difficult exploits. The three attacks on
ctarget use code injection. The two attacks on rtarget use
return-oriented programming.

----
1.2. Solving Targets
----
Each exploit involves reading a sequence of bytes from standard input
into a buffer stored on the stack. Students encode each exploit string
as a sequence of hex digit pairs separated by whitespace, where each
hex digit pair represents a byte in the exploit string. The program
"hex2raw" converts these strings into a sequence of raw bytes, which
can then be fed to the target:
 
    unix> cat exploit.txt | ./hex2raw | ./ctarget

Each student gets their own custom-generated copy of ctarget and
rtarget.  Thus, students must develop the solutions on their own and
cannot use the solutions from other students.

The lab writeup has extensive details on each phase and solution
techniques. We suggest that you read the writeup carefully before
continuing with this README file.


************
3. Solutions
************

TargetID: Each target in a given instance of the lab has a unique
non-negative integer called the "targetID."

The five solutions for target n are avalable to you in the
targets/target<n> directory, in the following files: 

Phase 1: ctarget.l1,
Phase 2: ctarget.l2, 
Phase 3: ctarget.l3, 
Phase 4: rtarget.l2, 
Phase 5: rtarget.l3, 

where "l" stands for level.