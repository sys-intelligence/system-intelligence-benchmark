#!/bin/bash
set -e

# Hash test file to detect tampering
sha256sum test_server.py > .test_server.sha256
