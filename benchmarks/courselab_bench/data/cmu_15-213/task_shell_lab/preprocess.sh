#!/bin/bash
set -e

chmod +x sdriver.pl tshref

# Hash test and driver files to detect tampering
sha256sum sdriver.pl trace*.txt myspin.c mysplit.c mystop.c myint.c Makefile tshref > .tests.sha256
