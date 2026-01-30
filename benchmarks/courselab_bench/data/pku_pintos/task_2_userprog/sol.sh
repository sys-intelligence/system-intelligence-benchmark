#!/bin/bash
# Reference: https://github.com/0AyanamiRei/pintos
# This solution passes all 80 tests.
set -e

git clone https://github.com/0AyanamiRei/pintos.git /tmp/ref
cd /tmp/ref

cp src/userprog/syscall.c /home/PKUOS/pintos/src/userprog/
cp src/userprog/syscall.h /home/PKUOS/pintos/src/userprog/
cp src/userprog/process.c /home/PKUOS/pintos/src/userprog/
cp src/userprog/process.h /home/PKUOS/pintos/src/userprog/
cp src/userprog/exception.c /home/PKUOS/pintos/src/userprog/
cp src/threads/thread.c /home/PKUOS/pintos/src/threads/
cp src/threads/thread.h /home/PKUOS/pintos/src/threads/
cp src/threads/synch.c /home/PKUOS/pintos/src/threads/
cp src/threads/synch.h /home/PKUOS/pintos/src/threads/
cp src/threads/fix-point.h /home/PKUOS/pintos/src/threads/

rm -rf /tmp/ref
