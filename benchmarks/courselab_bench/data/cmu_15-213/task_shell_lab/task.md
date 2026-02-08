# Task: Shell Lab (tsh)

In this task, you will implement a Unix shell with job control. The workspace already includes the Tiny Shell skeleton `tsh.c`, along with the driver script and trace files.

## Goals

Complete the key logic in `tsh.c` so your shell correctly handles:

- Foreground/background jobs (fg/bg)
- The job list (`jobs`)
- Signal handling (SIGCHLD/SIGINT/SIGTSTP)
- Process group control and job state transitions

The functions you must implement are marked in `tsh.c`:

- `eval`
- `builtin_cmd`
- `do_bgfg`
- `waitfg`
- `sigchld_handler`
- `sigtstp_handler`
- `sigint_handler`

## Testing

Use the provided driver script and trace files to test your implementation:

```bash
make
./sdriver.pl -t trace01.txt -s ./tsh -a "-p"
```

`trace01.txt` through `trace16.txt` cover most job-control behaviors.

## Notes

- Do not modify `sdriver.pl` or `trace*.txt`.
- Do not change the test logic in `Makefile`.
- Your output must match the reference implementation.
