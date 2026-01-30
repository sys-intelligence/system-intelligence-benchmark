#!/bin/bash
# Reference solution for Lab 3b (Mmap Files)
# Source: CuteNPC/pintos (24/24 Lab 3b tests)

set -e
cd /home/PKUOS

git clone https://github.com/CuteNPC/pintos.git /tmp/ref 2>/dev/null

# Copy VM implementation
cp /tmp/ref/src/vm/*.c pintos/src/vm/
cp /tmp/ref/src/vm/*.h pintos/src/vm/

# Copy modified userprog files
cp /tmp/ref/src/userprog/syscall.c pintos/src/userprog/
cp /tmp/ref/src/userprog/syscall.h pintos/src/userprog/
cp /tmp/ref/src/userprog/process.c pintos/src/userprog/
cp /tmp/ref/src/userprog/process.h pintos/src/userprog/
cp /tmp/ref/src/userprog/exception.c pintos/src/userprog/

# Copy modified threads files
cp /tmp/ref/src/threads/thread.c pintos/src/threads/
cp /tmp/ref/src/threads/thread.h pintos/src/threads/
cp /tmp/ref/src/threads/init.c pintos/src/threads/

# Copy modified filesys files
cp /tmp/ref/src/filesys/filesys.c pintos/src/filesys/
cp /tmp/ref/src/filesys/filesys.h pintos/src/filesys/

# Copy Makefile.build for VM compilation
cp /tmp/ref/src/Makefile.build pintos/src/

rm -rf /tmp/ref
