# Task: CS:APP Malloc Lab (Malloc/Free/Realloc)

Implement a working dynamic memory allocator in `mm.c`.

## Requirements

- Implement `mm_init`, `mm_malloc`, `mm_free`, and `mm_realloc` in `mm.c`.
- You may edit `mm.c` only. Other files are part of the driver.
- Your allocator must return 8-byte aligned payload pointers.
- Your solution must pass the provided trace tests.

## Build and Test

```bash
make
./mdriver -V -f short1-bal.rep
./mdriver -V -f short2-bal.rep
```

The task is considered solved if both traces complete without errors.
