# Task: CS:APP Proxy Lab

Implement a concurrent, caching HTTP proxy in C.

You are given the CS:APP Proxy Lab starter code in this workspace. Your goal is to complete `proxy.c` so that the proxy:

- Forwards HTTP requests from clients to origin servers and relays responses back.
- Handles multiple clients concurrently.
- Caches web objects with an LRU eviction policy.
- Uses the provided `user_agent_hdr` exactly as specified in the starter.

## Build

```bash
make clean
make
```

## Test

Run the provided autograder:

```bash
./driver.sh
```

The autograder checks:

- Basic proxy correctness (matching content with and without proxy)
- Concurrency (proxy remains responsive under blocking requests)
- Caching (serves cached objects when the origin is down)

Your solution should achieve a full score in `driver.sh`.
