# CMU 15-213: Bomb Lab

You are given a pre-built binary bomb. It has six phases. Each phase expects a specific input line; if any line is wrong the bomb explodes. Your job is to reverse engineer the binary and write the correct six lines to a file called `solution.txt`.

The binary and supporting materials are in the starter directory:

- `bomb`: the ELF64 binary bomb
- `bomb.c`: the main driver (does not reveal the phase internals)
- `README.bomb`: background about the lab

## Task

1. Work inside `/workspace`.
2. Recover the correct input for each of the six phases of the bomb.
3. Write the six inputs in order, one per line, to `solution.txt`.
4. Do not modify the starter artifacts (`bomb`, `bomb.c`, `README.bomb`).

The grading script will run `./bomb solution.txt` and expects the bomb to report success without ever printing `BOOM!!!`.

## Useful commands

- `strings bomb` to scan embedded text
- `objdump -d bomb | less` to disassemble
- `gdb ./bomb` to step through phases (set breakpoints on `phase_1`…`phase_6`)
- `./bomb` to run interactively during testing

## What is evaluated

- `solution.txt` exists and has at least six lines
- Starter files are unchanged
- `./bomb solution.txt` completes without exploding and prints "Congratulations! You've defused the bomb!"

Secret phases are not required. Focus only on phases 1–6.