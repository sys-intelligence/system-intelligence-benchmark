# The CMU 15-445 Database Lab

**YOU ARE ONLY ALLOWED TO MODIFY OR ADD FILES IN THE src DIRECTORY.**

## Task

Implement a basic Count-min sketch data structure supporting insertion, count estimation, and merging.

In `count_min_sketch.h`, following functions are to be implemented:

- `CountMinSketch(width, depth)`: constructor, creates a count-min sketch with width columns (buckets) and depth rows (hash functions).
- `CountMinSketch(&&other)`: move constructor, transfers ownership of sketch resources from another instance.
- `operator=(&&other)`: move assignment, moves sketch resources from another instance to this one.
- `Insert(item)`: inserts the specified item into the count-min sketch. This is expected to be thread-safe.
- `Count(&item)`: returns the estimated frequency of the item.
- `Clear()`: resets the data structure from previous streams.
- `Merge(&other)`: creates a new sketch by combining counter values from two compatible sketches.
- `TopK(k, &candidates)`: practical usage of count-min sketch--given the candidates that have been stored in the count-min sketch, return the k candidates with the most estimated counts.

## Project Specification

Consider the following scenario: you are the administrator of a popular blog website, and you've been receiving reports on certain accounts spamming excessively. To map out overall network usage and detect potential DDoS attacks, you want a real-time approach to count how often each IP address appears in the incoming request stream. However, the stream is huge, which makes traditional data structures either too slow or too memory-hungry. This is where the Count–Min Sketch comes in!

Count-min sketch (CM Sketch) is a probabilistic data structure that approximates frequency counts of items in a stream using sublinear memory. It maintains a compact 2-dimensional array of counters addressed by d independently seeded hash functions. Each update increments one cell per row, and a query returns the minimum of those counters. Moreover, count-min sketch is mergeable, meaning that the sum of two sketches is equivalent to constructing a single sketch over the concatenation of the corresponding input streams. Count-min sketch is widely used for network traffic monitoring, streaming analytics, and database system optimization.

Count-min sketch is based on the following parameters:

- `width (w)` – Number of columns in the hash matrix; each hash maps an item to an index in [0, w-1]. Larger w ⇒ smaller additive error.
- `depth (d)` – Number of rows / independent hash functions. Larger d ⇒ lower probability of a bad overestimate.
- `hash family / seeds` – A way to derive d pairwise-independent hash functions (e.g., by seeding a base hash differently for each row).

To explain how this data structure functions, let follow the example at the beginning and consider the following input stream: `["24.156.99.202", "172.217.22.14", "64.104.78.227", "24.156.99.202"]`. Let's use a count-min sketch with width 4 and depth 3. For each of the 3 rows, hash the string (using that row's seed) to produce an integer, reduce it modulo 4 to get a column index, and increment the counter at (row, column).

First, initialize the hash matrix (3 rows × 4 columns) with all zeros:

```
0 0 0 0
0 0 0 0
0 0 0 0
```

Now process the stream. We first insert "24.156.99.202". Assume the following hash positions (mod 4):

```
hash1 → 2
hash2 → 0
hash3 → 3
```

We update the cells accordingly:

```
0 0 1 0
1 0 0 0
0 0 0 1
```

Next, we insert "172.217.22.14" and increment counters at the hash positions below:

```
hash1 → 1
hash2 → 0 (collision with the first item in row 1)
hash3 → 2
```

Update:

```
0 1 1 0
2 0 0 0
0 0 1 1
```

Now we insert "64.104.78.227":

```
hash1 → 3
hash2 → 1
hash3 → 2 (collision with the second item in row 3)
```

The table becomes:

```
0 1 1 1
2 1 0 0
0 0 2 1
```

Finally, repeat "24.156.99.202" (same hash positions as before: 2, 0, 3). Increment those cells again:

```
0 1 2 1
3 1 0 0
0 0 2 2
```

Now, let's estimate the frequency of "24.156.99.202". Let's look up the same columns used when inserting that key:

```
Row 0, col 2 → 2
Row 1, col 0 → 3
Row 2, col 3 → 2
```

The estimate is the minimum across rows:

```
Estimate("24.156.99.202") = min(2, 3, 2) = 2
```

Why take the minimum? Each row's counter can be inflated by collisions with other items, but the minimum across independent hash rows gives the tightest upper bound on the true frequency.

---

## Important Information

For constructing hash functions for the matrix, please use the seeded hash function "common/util/hash_util.h" from the bustub repository. Please refrain from using hash functions from external libraries or implementing your own, since this might influence whether you pass the test suite we provide!

The test suite includes parallel tests. However, we ONLY expect thread-safe implementation for `Insert(item)`. In other words, your implementation must correctly handle scenarios where multiple threads simultaneously perform insertions into multiple count-min sketches.

You may notice the last test compares the performance of your implementation for `Insert(item)` against one that is strictly sequential. You could only pass this test if the relative speedup of your implementation is larger than 1.2. We expect you NOT to use only a single global latch to guard the whole data structure. If you do so, the contention ratio will be effectively around 1.0. There are many ways to do this. As a hint, try thinking of ways to break down the latch granularity or, even better, not to use a latch at all (you may find compare_exchange helpful if you aim for the latter). If you find this difficult to reason about, try passing other tests with a global latch first before attempting to optimize for this one.

## Testing

You can test the individual components of this assignment using our testing framework. We use GTest for unit test cases. You can disable tests in GTest by adding a `DISABLED_` prefix to the test name. To run the tests from the command-line:

```bash
cd build
make -j$(nproc) count_min_sketch_test
./test/count_min_sketch_test
```

## Memory Leaks

For this project, we use LLVM Address Sanitizer (ASAN) and Leak Sanitizer (LSAN) to check for memory errors. To enable ASAN and LSAN, configure CMake in debug mode and run tests as you normally would. If there is memory error, you will see a memory error report. Note that macOS only supports address sanitizer without leak sanitizer.

In some cases, address sanitizer might affect the usability of the debugger. In this case, you might need to disable all sanitizers by configuring the CMake project with:

```bash
cmake -DCMAKE_BUILD_TYPE=Debug -DBUSTUB_SANITIZER= ..
```

## Development Hints

You can use `BUSTUB_ASSERT` for assertions in debug mode. Note that the statements within `BUSTUB_ASSERT` will NOT be executed in release mode. If you have something to assert in all cases, use `BUSTUB_ENSURE` instead.

We will test your implementation in release mode. To compile your solution in release mode:

```bash
mkdir build_rel && cd build_rel
cmake -DCMAKE_BUILD_TYPE=Release ..
make -j`nproc`
```
