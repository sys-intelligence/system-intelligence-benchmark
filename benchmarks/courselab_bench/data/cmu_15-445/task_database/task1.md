# Phase 1

**YOU ARE ONLY ALLOWED TO MODIFY OR ADD FILES IN THE src DIRECTORY.**

## Overview

In this lab, you will build a disk-oriented database management system (DBMS) called **BusTub**. A disk-oriented architecture means that the DBMS's primary storage location is in persistent storage, like a hard drive (HDD) or flash storage (SSDs). This is different from an in-memory DBMS, where data is stored in volatile memory.

The first programming project is to implement the DBMS's **buffer pool manager**. The buffer pool is responsible for moving physical pages of data back and forth from buffers in main memory to persistent storage. It also behaves as a cache, keeping frequently used pages in memory for faster access, and evicting unused or cold pages back out to storage.

A page in BusTub is 8192 bytes (8 KB) of data, meaning the buffer pool manages data in 8 KB units. Since pages in BusTub are fixed size, the buffer pool manager stores these pages into fixed-size buffers called **frames**. The distinction between a page and a frame is somewhat subtle. A page is 8 KB of logical (virtual) data, and can be stored in memory, on disk, or both in memory and on disk. A frame, on the other hand, is a fixed-length 8 KB block of memory (i.e., a pointer to this memory) that stores a single page of data. The analogy here is storing (logical) pages inside (physical) fixed frames.

In addition to behaving as a cache, the buffer pool manager allows a DBMS to support databases that are larger than the amount of memory available to the system. Consider a computer with 1 GB of memory (RAM). If we want to manage a 2 GB database, a buffer pool manager gives us the ability to interact with this database without needing to fit its entire contents in memory.

The I/O operations that the buffer pool executes are abstracted away from other parts of the DBMS. For example, when one of the DBMS's components (e.g., execution engine) asks the buffer pool manager for a page of data using its unique identifier (`page_id_t`), that component does not need to know whether that page is already in memory or whether the system has to retrieve it from disk. Similarly, the buffer pool manager does not need to understand the contents of these pages, it only needs to know where the data is located.

## Implementation

Your implementation of the buffer pool must be thread-safe. Multiple threads will concurrently access the internal data structures of your buffer pool, and you must make sure that critical sections are protected with latches (these are called "locks" in operating systems).

You must implement the following storage manager components:

* **Adaptive Replacement Cache (ARC) Replacement Policy**
* **Disk Scheduler**
* **Buffer Pool Manager**

## Project Specification

Remember to pull latest code from the BusTub repository.

For each of the following components, we have provided stub classes that contain the API that you must implement. You should not modify the signatures for the pre-defined functions in these classes. If you modify the signatures, our grading test code will not work and you will not get credit for this project.

If a class already contains data members, you should not remove them. For example, the `BufferPoolManager` class contains `DiskScheduler` and `ArcReplacer` members that are required to implement functionality needed by the rest of the system. You may add data members and helper functions to these classes to correctly implement the required functionality.

You may use any built-in C++17 containers in your project unless specified otherwise. It is up to you to decide which ones you want to use. Be warned that these containers are not thread-safe, and you will need to use latches to protect access to them. You may not use additional third-party libraries (e.g., Boost).

### Task #1 - Adaptive Replacement Cache (ARC) Replacement Policy

This component is responsible for tracking page usage in the buffer pool in order to determine candidate pages / frames to evict out of memory and back to disk.

You will implement a class called `ArcReplacer` in `src/include/buffer/arc_replacer.h` and its corresponding implementation file in `src/buffer/arc_replacer.cpp`. Note that `ArcReplacer` is a standalone class and is not related to any of the other `Replacer` classes. You are only expected to implement the Arc replacement policy, and you don't have to implement the LRU-K, LRU or Clock replacement policies (even though there are corresponding files for them).

The ARC replacement policy, originally developed at IBM, is an adaptive replacement policy that changes to the workload it observes. It involves two lists that tracks the cached pages, two lists that tracks the recently evicted pages, and a target size that is adaptive to the workload. Because of this adaptiveness, the ARC replacement policy generally performs better than LRU. Refer to the original paper for more details.

You will be implementing a variant of the ARC replacement policy for this project.

You will need to implement the following methods for ARC as defined in the header file (`src/include/buffer/arc_replacer.h`) and in the source file (`src/buffer/arc_replacer.cpp`):

* **`Size() -> size_t`**: This method returns the number of evictable frames that are currently in the `ArcReplacer`.
* **`SetEvictable(frame_id_t frame_id, bool set_evictable)`**: This method controls whether a frame is evictable or not. It also controls the ARCReplacer's size. You'll know when to call this function when you implement the `BufferPoolManager`. To be specific, when the pin count of a page hits 0, its corresponding frame should be marked as evictable.
* **`RecordAccess(frame_id_t frame_id, page_id_t page_id)`**: Record that the given page has has been accessed at the current timestamp, in the given frame. This method should be called after a page has been pinned to a frame in the `BufferPoolManager`. The algorithm for this has been given below.
* **`Evict() -> std::optional<frame_id_t>`**: Evict a frame following the eviction process of the ARC algorithm. If there are no evictable frames, return `std::nullopt`. The algorithm for this has been given below.
* **`Remove(frame_id_t frame_id)`**: Remove a frame and its corresponding page from the replacer if it exists and is evictable. This method should be called only when a page is deleted in the `BufferPoolManager`.

#### ARC Replacement Algorithm

The ARC algorithm has the following parts. We start with two lists: the **MRU** (most recently used) list tracks the frames and their corresponding pages that were recently accessed exactly once, while the **MFU** (most frequently used) list tracks the frames and their corresponding pages that were recently accessed more than one time. We also start with two ghost lists: an **MRU ghost list** and an **MFU ghost list**. These lists tracks pages that are no longer in the buffer pool, but were recently evicted. Lastly, we also have a **target size** for the MRU list that adapts to the change of the workload, which starts at 0. Note that the actual MRU list size could be different than the target, it may be smaller or larger, this is just our target size.

When working with the ARC replacer, there are generally five concepts here involving sizes, which is to be distinguished from each other:

1. **The capacity of the replacer (`replacer_size_`)**: The maximum number of frames that the ArcReplacer supports is the same as the size of the buffer pool since it contains placeholders for all of the frames in the BufferPoolManager.
2. **The total size of the four lists**: Due to the tracking of the evicted pages in the ghost list, although the capacity of the ArcReplacer is only the number of frames of the buffer pool, the four lists could have a total size up to 2 * capacity.
3. **The current evictable size (`curr_size_`)**: Not all frames in the replacer may be considered as evictable at any given time. The evictable size of the ArcReplacer is represented by the number of evictable frames. The ArcReplacer is first initialized to have no frames in it. Only when a frame is marked as evictable will replacer's size will increase. Similarly, when a frame is pinned or not in use, the replacer's size will decrease.
4. **The MRU list target size (`mru_target_size_`)**: The target size of the MRU list, which adapts to the workload observed. The adaption algorithm is given below.
5. **The MRU list actual size (`mru_.size()`)**: The actual size of the MRU list, which could defer from the MRU target size.

Also, please make sure you understand the relationship between frames and pages here, so it might make sense to you why tracking page ids along with frame ids is needed:

* A page that is in the buffer pool has a one-to-one mapping to a frame.
* Until a page in the bufferpool is evicted, the one-to-one mapping between page and frame should not change.
* An evicted page is not associated with any frames.

When performing `RecordAccess` over a frame and its corresponding page, there are four cases where exactly one of them will happen:

1. **Page already exists in MRU/MFU**: This is the case where the actual cache hits. Move the page to the front of MFU.
2. **Page already exists in MRU ghost**: This is the case where the actual cache misses but we hit on the ghost list. In this case we treat it as a pseudo-hit and adapt the target size. If the size of the MRU ghost list is greater than or equal to the size of the MFU ghost list, increase the MRU target size by one. Else increase it by MFU ghost size / MRU ghost size (rounded down). Do not increase the target size above `replacer_size`. Then move the page to the front of MFU. The rational of this is if the MRU list is a little larger, then the DBMS could have had a cache hit.
3. **Page already exists in MFU ghost**: Similar to the previous case, this is when the actual cache misses but we hit on the ghost list. If the size of the MFU ghost list is greater than or equal to the size of the MRU ghost list, decrease the MRU target size by 1. Else decrease the MRU target size by MRU ghost size / MFU ghost size (rounded down). Do not decrease the target size below 0. Then move the page to the front of MFU. The rational of this is if the MFU list is a little larger, the DBMS could have had a cache hit.
4. **Page is not in the replacer**: This is the case where the actual cache misses and the ghost list misses. Then either of the following should happen.
* (a) If MRU size + MRU ghost size = replacer size: Kill the last element in the MRU ghost list, then add the page to the front of MRU.
* (b) Else MRU size + MRU ghost size should be smaller than replacer size (it should never be larger if you do things correctly). In this case:
* If MRU size + MRU ghost size + MFU size + MFU ghost size = 2 * replacer size: Kill the last element in the MFU ghost list, then add the page to the front of MRU.
* Else simply add the page to the front of the MRU.

Try considering why in case 4(a) and 4(b), there must be items in the ghost lists.

#### Implementation

When you implement this algorithm, it is important to understand when should a page go to MRU, and when should it go to MFU. It also helps to think about why the given action is taken for each of the cases and what it's tring to do, rather than transpiling English into C++ code. If the MRU list size is smaller than the target size, we try to evict from the MFU list. If the MRU list size is greater than or equal to the target size, we try to evict from the MRU list. In either case, if eviction is not possible from the intended side (nothing is evictable in that list), try evicting from the other list. If still nothing is evictable, the eviction fails and return `std::nullopt`.

The implementation details are up to you. You are allowed to use built-in STL containers. You may assume that you will not run out of memory for these data structures (you cannot assume the same for the buffer pool in Task #3, you will run out of available frames). You must make sure that your implementation is thread-safe.

You might notice there is a test that tests for the performance of your `RecordAccess` implementation. If your implementation fails / times out on the test, try think of what makes `RecordAccess` slow and how you could fix it. As a reminder, you will modify the data structures and member variables we provided you in the header file, but you can also add additional data structures to speed up operations.

If you would like to read more about the ARC replacement algorithm, refer to [this paper](https://www.usenix.org/legacy/events/fast03/tech/full_papers/megiddo/megiddo.pdf). This project does not require you to implement the original algorithm exactly. You are also welcome to think about what we required you to do that is in addition to what the original algorithm could achieve.


### Task #2 - Disk Scheduler

This component is responsible for scheduling read and write operations on the `DiskManager`. You will implement a class called `DiskScheduler` in `src/include/storage/disk/disk_scheduler.h` and its corresponding implementation file in `src/storage/disk/disk_scheduler.cpp`.

The disk scheduler can be used by other components (in this case, your `BufferPoolManager` in Task #3) to queue disk requests, represented by a `DiskRequest` struct (already defined in `src/include/storage/disk/disk_scheduler.h`). The disk scheduler will maintain a background worker thread which is responsible for processing scheduled requests.

The disk scheduler will utilize a shared queue (channel) to schedule and process the `DiskRequests`. One thread will add a request to the queue, and the disk scheduler's background worker will process the queued requests. We have provided a `Channel` class in `src/include/common/channel.h` to facilitate the thread-safe sharing of data between threads, but feel free to use your own implementation if you find it necessary.

The `DiskScheduler` constructor and destructor are already implemented and are responsible for creating and joining the background worker thread. You will only need to implement the following methods as defined in the header file (`src/include/storage/disk/disk_scheduler.h`) and in the source file (`src/storage/disk/disk_scheduler.cpp`):

* **`Schedule(std::vector<DiskRequest> &requests)`**: Schedules a vector of requests for the `DiskManager` to execute. The `DiskRequest` struct specifies whether the request is for a read or write, where the data should be read from / written into, and the page ID for the operation. The `DiskRequest` also includes a `std::promise` whose value should be set to true once the request is processed. See below for more information about `std::promise`. The implementation details are up to you, but you may wish to use a vector of requests as a way to pre-fetch data for the leaderboard challenges.
* **`StartWorkerThread()`**: The startup method for the background worker thread which processes the scheduled requests. The worker thread is created in the `DiskScheduler` constructor and calls this method. This worker thread is responsible for receiving queued requests and dispatching them to the `DiskManager`. Remember to set the value correctly on the `DiskRequest`'s callback to signal to the request issuer that the request has been completed. This should not return until the `DiskScheduler`'s destructor is called.

We mentioned that one of the fields of a `DiskRequest` is a `std::promise`. If you are unfamiliar with C++ promises and futures, you can check out the documentation [here](https://en.cppreference.com/w/cpp/thread/promise). For the purposes of this project, they essentially provide a callback mechanism for a thread to know when their scheduled request is completed. To see an example of how they might be used, check out `disk_scheduler_test.cpp`.

Again, the implementation details are up to you. You must make sure that your implementation is thread-safe.

#### Disk Manager

The header containing the `DiskManager` class is located at (`src/include/storage/disk/disk_manager.h`). It reads page data from disk and writes data to disk. Your disk scheduler will use `DiskManager::ReadPage()` and `DiskManager::WritePage()` while it is processing a read or write request.


### Task #3 - Buffer Pool Manager

Finally, you must implement the buffer pool manager (**BufferPoolManager**)! Echoing the beginning of this page, the `BufferPoolManager` is responsible for fetching database pages from disk with the `DiskScheduler` and storing them in memory. The `BufferPoolManager` can also schedule writes of dirty pages out to disk when it is either explicitly instructed to do so or when it needs to evict a page to make space for a new page.

Your `BufferPoolManager` implementation will use the `ArcReplacer` and `DiskScheduler` classes that you created in the previous steps of this assignment. The `ArcReplacer` will keep track of when pages are accessed so that it can decide which frame to evict when it must make room for a new page. The `DiskScheduler` will schedule writes and reads to disk on the `DiskManager`.

We have provided a helper class called `FrameHeader`, which helps manage the in-memory frames. All access to page data should be through `FrameHeaders`. `FrameHeader` has a method called `GetData` that returns a raw pointer to its frame's memory, and the `DiskScheduler` / `DiskManager` will use this pointer to copy the contents of a physical page on disk into memory.

As a reminder, the buffer pool manager does not need to understand the contents of these pages. The only information that the `BufferPoolManager` knows about pages are the page IDs (`page_id_t`) and the `FrameHeaders` they are stored inside of. Also, the `BufferPoolManager` will reuse the same `FrameHeader` object to store data as it moves back and forth between disk and memory. In other words, all `FrameHeaders` will store many different pages throughout the lifetime of the system.

#### Concurrency

When implementing a multi-threaded buffer pool manager, we must take care to synchronize data access. This means that we do not want multiple copies of the same page in different frames of the buffer pool. If we allowed this, we would encounter this scenario:

1. Thread T1 loads page X1 from disk into a frame and starts modifying page X1, and let's call this new version page X2.
2. Thread T2 loads page X1 from disk into a different frame and starts modifying this version of page X1, and let's call this other modified version page X3.
3. Thread T2 finishes writing and writes X3 back to disk.
4. Thread T1 finishes writing and writes X2 back to disk.
5. Data race ☠️!

Thus, we keep only 1 version of a page in memory at a time to prevent data synchronization races. Additionally, to prevent us from evicting a page while threads are accessing it, we maintain a reference count / pin count on the frame that stores it. Finally, in order to keep track of which pages are stored in which frames, we also maintain a page table using a hash map that maps page IDs to frames.

The pin count of a frame is the number of threads that have access to the page's data. As long as the pin count on a frame is greater than 0 (implying there is at least 1 thread accessing the page's data), the buffer pool manager is not allowed to evict the page being stored. You can maintain the pin count using the atomic field `pin_count_` in the `FrameHeader` class. Keep in mind that `pin_count_` is separate from `ArcReplacer::SetEvictable`, so you will need to make sure those are synced properly. You will also have to update the `is_dirty_` flag of the `FrameHeader` when you think it is necessary. If this flag is set when you want to evict a page, you will have to act accordingly to maintain data synchronization between memory and disk.

Lastly, you will have to implement both `ReadPageGuard` and `WritePageGuard`. These classes are RAII objects that provide thread-safe read / write access to the underlying pages. See the implementation section below for more information. You will probably need to implement this in tandem with the `BufferPoolManager` methods `CheckedReadPage` and `CheckedWritePage`. However, if you want to make sure your page guard implementations are correct, you may choose to implement `BufferPoolManager::GetPinCount` first and then stitch together something that will pass the page guard tests.

#### Implementation

You will need to implement the following page guard methods defined in the header file (`src/include/storage/page/page_guard.h`) and in the source file (`src/storage/page/page_guard.cpp`):

* `ReadPageGuard::ReadPageGuard()`
* `ReadPageGuard::ReadPageGuard(ReadPageGuard &&that)`
* `ReadPageGuard::operator=(ReadPageGuard &&that) -> ReadPageGuard &`
* `ReadPageGuard::Flush()`
* `ReadPageGuard::Drop()`
* `WritePageGuard::WritePageGuard()`
* `WritePageGuard::WritePageGuard(WritePageGuard &&that)`
* `WritePageGuard::operator=(WritePageGuard &&that) -> WritePageGuard &`
* `WritePageGuard::Flush()`
* `WritePageGuard::Drop()`

You do not have to implement these methods before the `BufferPoolManager` methods. You should probably work on them at the same time.

These methods implement move semantics and RAII for the page guards. If you are unfamiliar with these things, please familiarize yourself with learning materials online. There are many great resources (including articles, Microsoft tutorials, YouTube videos) that explain this in depth. You should not attempt to implement these methods without having a solid understanding of how RAII and move semantics work.

There will likely be a lot of code duplication here (i.e. the two guards should be identical except for a handful of lines). If you want to derive these classes based on a class you create, you are welcome to do so. Just make sure that no interfaces and method signatures are changed!

You will also need to implement the following `BufferPoolManager` methods defined in the header file (`src/include/buffer/buffer_pool_manager.h`) and in the source file (`src/buffer/buffer_pool_manager.cpp`):

* `NewPage() -> page_id_t`
* `DeletePage(page_id_t page_id) -> bool`
* `CheckedWritePage(page_id_t page_id) -> std::optional<WritePageGuard>`
* `CheckedReadPage(page_id_t page_id) -> std::optional<ReadPageGuard>`
* `FlushPageUnsafe(page_id_t page_id) -> bool`
* `FlushPage(page_id_t page_id) -> bool`
* `FlushAllPagesUnsafe()`
* `FlushAllPages()`
* `GetPinCount(page_id_t page_id)`

All of these methods have detailed documentation comments in the source file. Make sure to read all of these in their entirety because they contain many useful hints!

You do not need to make your buffer pool manager super efficient. For all of the public `BufferPoolManager` method, holding the buffer pool latch from beginning to end should be enough (except for when you need to release it early to prevent deadlocks). However, you do need to ensure that your buffer pool manager has reasonable performance, otherwise there will be problems in future projects. You can compare your benchmark result (QPS.1 and QPS.2) with other students and see if your implementation is too slow.

Please refer to the source files (`src/storage/page/page_guard.cpp` and `src/buffer/buffer_pool_manager.cpp`) for significantly more detailed specifications and documentation.

### Testing

You can test the individual components of this assigment using our testing framework. We use GTest for unit test cases. There are three separate files that contain tests for each component:

* **ArcReplacer:** `test/buffer/arc_replacer_test.cpp`
* **DiskScheduler:** `test/storage/disk_scheduler_test.cpp`
* **PageGuard:** `test/storage/page_guard_test.cpp`
* **BufferPoolManager:** `test/buffer/buffer_pool_manager_test.cpp`

You can compile and run each test individually from the command-line:

```bash
$ make arc_replacer_test -j `nproc`
$ ./test/arc_replacer_test

```

### Formatting

Your code must follow the Google C++ Style Guide. We use Clang to automatically check the quality of your source code. Your project grade will be zero if your submission fails any of these checks.

Execute the following commands to check your syntax. The `format` target will automatically correct your code. The `check-lint` and `check-clang-tidy-p1` targets will print errors and instruct you how to fix it to conform to our style guide.

```bash
$ make format
$ make check-lint
$ make check-clang-tidy-p1

```

### Memory Leaks

For this project, we use LLVM Address Sanitizer (ASAN) and Leak Sanitizer (LSAN) to check for memory errors. To enable ASAN and LSAN, configure CMake in debug mode and run tests as you normally would. If there is memory error, you will see a memory error report. Note that macOS only supports address sanitizer without leak sanitizer.

In some cases, address sanitizer might affect the usability of the debugger. In this case, you might need to disable all sanitizers by configuring the CMake project with:

```bash
$ cmake -DCMAKE_BUILD_TYPE=Debug -DBUSTUB_SANITIZER= ..

```

### Development Hints

* You can use `BUSTUB_ASSERT` for assertions in debug mode. Note that the statements within `BUSTUB_ASSERT` will NOT be executed in release mode. If you have something to assert in all cases, use `BUSTUB_ENSURE` instead.
* Post all of your questions about this project on Piazza. Do not email the TAs directly with questions.
* We encourage you to use a graphical debugger to debug your project if you are having problems.
* If you are having compilation problems, running `make clean` does not completely reset the compilation process. You will need to delete your build directory and run `cmake ..` again before you rerun `make`.