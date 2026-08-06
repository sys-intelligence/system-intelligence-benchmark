#!/bin/bash
# This script simulates what an agent might execute to solve the task

cat > dummy.cpp << 'EOF'
#include <iostream>

int main() {
    std::cout << "Hello, World!" << std::endl;
    return 0;
}
EOF