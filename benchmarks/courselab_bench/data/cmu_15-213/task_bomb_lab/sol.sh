#!/bin/bash
set -euo pipefail

cd /workspace

cat > solution.txt <<'EOF_SOL'
Border relations with Canada have never been better.
1 2 4 8 16 32
7 327
7 0
9on567
4 3 2 1 6 5
EOF_SOL

chmod +x bomb
./bomb solution.txt > /tmp/bomb_sol_output.txt
grep -q "Congratulations! You've defused the bomb!" /tmp/bomb_sol_output.txt
printf "Bomb lab reference solution produced:\n%s\n" "$(tail -n 5 /tmp/bomb_sol_output.txt)"
