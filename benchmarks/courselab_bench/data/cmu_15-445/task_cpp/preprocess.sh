#!/bin/bash
set -e

echo "=== Setting up CMU 15-445 Database Lab ==="

cd /workspace

echo "Installing git"

apt-get update > /dev/null 2>&1
apt-get install -y git > /dev/null 2>&1

echo "Cloning bustub repository"

mkdir -p src
cd src

git init

git clone --bare https://github.com/cmu-db/bustub.git src > /dev/null 2>&1

git remote add public https://github.com/cmu-db/bustub.git

git fetch public
git merge public/master

# rm -rf src/.git

echo "Installing build dependencies"

build_support/packages.sh -y

mkdir -p build
cd build
cmake -DCMAKE_BUILD_TYPE=Debug ..
make -j`nproc`

echo "Setup complete"
exit 0
