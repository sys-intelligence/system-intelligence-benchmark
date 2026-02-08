#!/bin/bash
set -euo pipefail

apt-get update -y > /dev/null
apt-get install -y python3 net-tools > /dev/null

sha256sum \
  driver.sh \
  nop-server.py \
  free-port.sh \
  port-for-user.pl \
  tiny/Makefile \
  tiny/tiny.c \
  tiny/csapp.c \
  tiny/csapp.h \
  tiny/home.html \
  tiny/cgi-bin/adder.c \
  > .test_files.sha256
