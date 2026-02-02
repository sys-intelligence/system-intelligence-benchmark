#####################################################################
# CS:APP Buffer Lab
# Directions to Instructors
#
# Copyright (c) 2002-2012, R. Bryant and D. O'Hallaron
#
######################################################################

This directory contains the files that you will use to build and run
the CS:APP Buffer Lab.

The purpose of the Buffer Lab is to help students develop a detailed
understanding of the stack discipline on IA32 processors.  It involves
applying a series of buffer overflow attacks on an executable file.

This version of the lab has been specially modified to defeat the
stack randomization techniques used by newer versions of Linux. It
works by using mmap() and an assembly language insert to move the
stack pointed at by %esp to an unused part of the heap.

***********
1. Overview
***********

----
1.1. Buffer Bombs
----

A "buffer bomb" is an executable bomb, called "./bufbomb", that is
solved using a buffer overflow attack (exploit).  In this lab,
students are asked to alter the behavior of a buffer bomb (called
bufbomb) via five increasingly difficult levels of exploits.

The levels are called smoke (level 0), fizz (level 1), bang (level 2),
boom (level 3), and kaboom (level 4), with smoke being the simplest
and kaboom being the most difficult. 

----
1.2. Solving Buffer Bombs
----
Each exploit involves reading a sequence of bytes from standard input
into a buffer stored on the stack. Students encode each exploit string
as a sequence of hex digit pairs separated by whitespace, where each
hex digit pair represents a byte in the exploit string. The program
"hex2raw" converts these strings into a sequence of raw bytes, which
can then fed to the buffer bomb:
 
    unix> cat exploit.txt | ./hex2raw | ./bufbomb -u <userid>

Each student works on an identical buffer bomb, but the solution to
the individual phases is a function of each student's userid.  Thus,
students must develop the solution on their own and cannot use the
solutions from other students.

The solution to each phase is unique for each student because it
typically involves the manipulation on the runtime stack of a unique
"cookie" computed from the userid by the "makecookie" program:

    unix> ./makecookie bovik
    0x1005b2b7
	
The lab writeup has extensive details on each phase and solution
techniques.


**************************
1. Buffer Bomb Terminology
**************************
Notifying Bomb: A buffer bomb can be compiled with a NOTIFY option
that allows the student to submit successful exploit strings to the
autograding service. Such bombs are called "notifying bombs."

Quiet Bomb: A buffer bomb that is not a notifying bomb is called a
"quiet bomb."

Cookie: Unlike the Bomb Lab, each student works on the same
binary. However, the solution to each phase is different for each
student because the exploit string typically must contain a 32-bit
"cookie" that is computed from the student's userid.