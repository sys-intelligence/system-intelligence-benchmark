#!/bin/bash
# Reference: https://github.com/Dhanya-Abhirami/PintOS
set -e

git clone https://github.com/Dhanya-Abhirami/PintOS.git /tmp/ref
cd /tmp/ref

cp src/threads/thread.c /home/PKUOS/pintos/src/threads/
cp src/threads/thread.h /home/PKUOS/pintos/src/threads/
cp src/threads/synch.c /home/PKUOS/pintos/src/threads/
cp src/threads/synch.h /home/PKUOS/pintos/src/threads/
cp src/threads/fixed_point.h /home/PKUOS/pintos/src/threads/
cp src/devices/timer.c /home/PKUOS/pintos/src/devices/
cp src/devices/timer.h /home/PKUOS/pintos/src/devices/

rm -rf /tmp/ref
