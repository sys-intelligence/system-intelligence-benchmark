#!/bin/bash

set -e  # Exit immediately on error.

apt-get update -y
apt-get install -y nodejs npm

npm install -g @anthropic-ai/claude-code
