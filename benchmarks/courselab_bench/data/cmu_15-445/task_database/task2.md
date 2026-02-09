# Phase 2

**YOU ARE ONLY ALLOWED TO MODIFY OR ADD FILES IN THE src DIRECTORY.**

## Overview

In this project you will implement a B+Tree index in your database system. A B+Tree is a balanced search tree in which the internal pages direct the search and leaf pages contain the actual data entries. The index provides fast data retrieval without needing to search every row in a database table, enabling rapid random lookups and efficient scans of ordered records. Your implementation will support thread-safe search, insertion, deletion (including splitting and merging nodes), and an iterator to support in-order leaf scans. You need to complete the following tasks:

* **Task #1** - B+Tree Pages
* **Task #2** - B+Tree Operations (Insertion, Deletion, and Point Search)
* **Task #3** - Index Iterator
* **Task #4** - Concurrency Control

---

## Project Specification

We have provided stub classes that define the APIs that you must implement. You should not modify the signatures of these pre-defined functions; if you do, our test code will not work and you will receive little or no credit for the project. Similarly, you should not remove existing member variables from the code we provide. You may add functions and member variables to these classes to implement your solution.

---

## Task #1 - B+Tree Pages

You must implement the following three Page classes to store the data of your B+Tree.

1. B+Tree Page
2. B+Tree Internal Page
3. B+Tree Leaf Page

### Base Page

This is a base class that the Internal Page and Leaf Page inherit from, and contains only information that both child classes share. The B+Tree Page has the following fields:

| Variable Name | Size | Description |
| --- | --- | --- |
| `page_type_` | 4 | Page type (invalid page / leaf page / internal page) |
| `size_` | 4 | Number of key & value pairs in a page |
| `max_size_` | 4 | Max number of key & value pairs in a page |

You must implement the B+Tree Page by modifying only its header file (`src/include/storage/page/b_plus_tree_page.h`) and the corresponding source file (`src/storage/page/b_plus_tree_page.cpp`).

### Internal Page

An Internal Page (i.e., inner node) stores  ordered keys and  child pointers (i.e. `page_id`s) to other B+Tree Pages. These keys and pointers are internally represented as an array of key/page_id pairs. As the number of child pointers is one more than the number of keys, the first key in `key_array_` (see `src/include/storage/page/b_plus_tree_internal_page.h`) is set to be invalid, and lookups should always start from the second key.

At any time, each internal page should be at least half full. During deletion, two half-full pages can be merged, or keys and pointers can be redistributed to avoid merging. During insertion, one full page can be split into two, or keys and pointers can be redistributed to avoid splitting. These are examples of the many design choices that you will make while implementing your B+Tree.

You must implement the Internal Page by modifying only its header file (`src/include/storage/page/b_plus_tree_internal_page.h`) and the corresponding source file (`src/storage/page/b_plus_tree_internal_page.cpp`).

### Leaf Page

The Leaf Page stores  ordered keys and their  corresponding values. In your implementation, the value should always be the 64-bit record id for where the actual tuples are stored -- see the `RID` class, in `src/include/common/rid.h`. Leaf pages have the same restrictions on the number of key/value pairs as Internal pages, and should follow the same operations for merging, splitting, and redistributing keys.

For this project, we will extend our leaf page implementation by also including a tombstone buffer for recent deletions. This tombstone buffer stores the last  indexes of entries in key/value arrays that have been deleted. Thus, when a key is deleted from the index (if ) its entry in its corresponding leaf page is not actually deleted but the index is appended to the tombstone buffer. Only when the buffer of said leaf page has  entries in it is the oldest buffered deletion actually applied to the key/value arrays. This is a simplified version of the Bε-tree discussed in the lectures.

You must implement `GetTombstones()` to report the keys that the tombstones in a given page correspond to. `KeyAt` must however return the physical entry at a given index regardless of whether a tombstone exists for that entry.

You must implement your Leaf Page by modifying only its header file (`src/include/storage/page/b_plus_tree_leaf_page.h`) and corresponding source file (`src/storage/page/b_plus_tree_leaf_page.cpp`).

> **Note:** Even though Leaf Pages and Internal Pages contain the same key type, they may have different value types. Thus, the `max_size` can be different.

Each B+Tree leaf/internal page corresponds to the content (i.e., the `data_` part) of a memory page fetched by the buffer pool. Every time you read or write from/to a leaf or internal page, you must first fetch the page from the buffer pool (using its unique `page_id`), Use `reinterpret_cast` to convert it to either a leaf or an internal page, and unpin the page after reading or writing from/to it.

---

## Task #2 - B+Tree Operations (Insertion, Deletion, and Point Search)

In this task, your B+Tree Index needs to support insertion (`Insert()`), deletion (`Remove()`), and search (`GetValue()`) for single values. The index should support only unique keys; if you try to reinsert an existing key into the index, insertion should not be performed and false will be returned. You must implement this task by modifying the source file `src/storage/index/b_plus_tree.cpp` and optionally its corresponding header file `src/include/storage/index/b_plus_tree.h`.

B+Tree pages should be split (or keys should be redistributed) if an insertion would violate the B+Tree's invariants. Furthermore, leaf page tombstones (and their ordering) must be maintained across any merging, splitting, and redistributing operations. When a leaf is coalesced or redistributed into another leaf we consider all of its pending deletions to be more recent than any pending deletion in the recipient leaf (in other words: the node with entries being inserted into it should have its tombstones processed first).

If an insertion changes the page ID of the root, you must update the `root_page_id` in the B+Tree index's header page. You can do this by accessing the `header_page_id_` page, which is given to you in the constructor. Then, by using `reinterpret_cast`, you can interpret this page as a `BPlusTreeHeaderPage` (from `src/include/storage/page/b_plus_tree_header_page.h`) and update the root page ID from there. You also must implement `GetRootPageId`.

Similarly, your B+Tree Index must support including merging or redistributing keys between pages if necessary to maintain the B+Tree invariants when deleting a key. As with insertions, you must correctly update the B+Tree's root page ID if the root changes.

We recommend that you use the page guard classes from Project #1 to avoid synchronization problems. You should use `ReadPage` or `WritePage` accordingly.

You may optionally use the `Context` class (defined in `src/include/storage/index/b_plus_tree.h`) to track the pages that you've read or written (via the `read_set_` and `write_set_` fields) or to store other metadata that you need to pass into other functions recursively.

**If you are using the Context class, here are some tips:**

* You might only need to use `write_set_` when inserting or deleting. It is possible that you do not use `read_set_`, depending on your implementation.
* You might want to store the root page id in the context and acquire write guard of header page when modifying the B+Tree.
* To find a parent of the current node, look at the back of `write_set_`. It should contain all nodes along the access path.
* You may use `BUSTUB_ASSERT` to help you find inconsistent data in your implementation. For example, if you want to split a node (except root), you should ensure that there is still at least one node in the `write_set_`. If you need to split root, you should check if `header_page_` is `std::nullopt`.
* To unlock the header page, simply set `header_page_` to `std::nullopt`. To unlock other pages, pop from the `write_set_` and drop.

The B+Tree is parameterized on arbitrary key, value, and key comparator types. We've defined a macro, `INDEX_TEMPLATE_ARGUMENTS`, that generates the template parameter declaration for you:

```cpp
template <typename KeyType,
          typename ValueType,
          typename KeyComparator>

```

The type parameters are:

* **KeyType:** The type of each key in the index. In practice this will be a `GenericKey`. The actual size of a `GenericKey` varies, and is specified with its own template argument that depends on the type of indexed attribute.
* **ValueType:** The type of each value in the index. In practice, this will be a 64-bit RID.
* **KeyComparator:** A class used to compare whether two `KeyType` instances are less than, greater than, or equal to each other. These will be included in the `KeyType` implementation files.

---

## Task #3 - Index Iterator

After you have implemented and thoroughly tested your B+Tree in Tasks #1 and #2, you must add a C++ iterator that efficiently supports an in-order scan of the entries in the index. The basic idea is store sibling pointers so that you can efficiently traverse the leaf pages, and then implement an iterator that iterates through every key-value pair, in order, in the index. Note that this iterator must respect tombstones and thus you should skip any key-value pair with a corresponding tombstone.

Your iterator must be a C++17-style Iterator, including at least the following methods:

* `isEnd()`: Return whether this iterator is pointing at the last key/value pair.
* `operator++()`: Move to the next key/value pair.
* `operator*()`: Return the key/value pair this iterator is currently pointing at.
* `operator==()`: Return whether two iterators are equal.
* `operator!=()`: Return whether two iterators are not equal.

Your `BPlusTree` also must correctly implement `begin()` and `end()` methods, to support C++ for-each loop functionality on the index.

You must implement your index iterator by modifying only its header file (`src/include/storage/index/index_iterator.h`) and corresponding source file (`src/index/storage/index_iterator.cpp`).

---

## Task #4 - Concurrency Control

In the last task, you will modify your B+Tree implementation so that it safely supports concurrent operations. You should use the optimistic latch coupling/crabbing technique described in class and in the textbook. The thread traversing the index should acquire latches on B+Tree pages as necessary to ensure safe concurrent operations, and should release latches on parent pages as soon as possible when it is safe to do so.

> **Note:** You should never acquire the same read latch twice in a single thread. It might lead to deadlock.

## Instructions

See the Project #0 instructions on how to create your private repository and setup your development environment.

### Development Roadmap

There are several ways in which you could go about building a B+Tree Index. This road map only serves as a rough conceptual guideline, which is based on the algorithm outlined in the textbook.

1. **Simple Inserts:** Given a key-value pair KV and a non-full node N, insert KV into N. *Self check: What are the different types of nodes and can key-values be inserted in all of them?*
2. **Simple Search:** Given a key K, define a search mechanism on the tree to determine the presence of the key. *Self check: Can keys exist in multiple nodes and are all these keys the same?*
3. **Simple Splits:** Given a key K, and a target leaf node L that is full, insert the key into the tree, while keeping the tree consistent. *Self check: When do you choose to split a node and how to define a split?*
4. **Multiple Splits:** Define inserts for a key K on a leaf node L that is full, whose parent node M is also full. *Self check: What happens when the parent of M is also full?*
5. **Simple Deletes:** Given a key K and a target leaf node L that is at-least half full, delete K from L. *Self check: Is the leaf node L the only node that contains the key K?*
6. **Simple Coalesces:** Define deletion for a key K on a leaf node L that is less than half-full after the delete operation. *Self check: Is it mandatory to coalesce when L is less than half-full and how do you choose which node to coalesce with?*
7. **Not-So-Simple Coalesces:** Define deletion for a key K on a node L that contains no suitable node to coalesce with. *Self check: Does coalescing behavior vary depending on the type of nodes?* This should take you through to Task 1 and 2.
8. **Index Iterators:** The section on Task #3 describes the implementation of an iterator for the B+Tree.
9. **Concurrent Indexes:** The section on Task #4 describes the implementation of the latch crabbing technique to support concurrency in your design.

### Requirements and Hints

* You are not allowed to use a global latch to protect your data structure; your implementation must support a reasonable level of concurrency. In other words, you may not latch the whole index and only unlatch when operations are done.
* We recommend that you use the page guard classes `ReadPageGuard` and `WritePageGuard` to implement thread safety for your B+Tree. You can receive full credit on this project if you use these constructs correctly.
* You may add functions to your implementation as long as you keep all our original public interfaces intact for testing purposes.
* Do not use `malloc` or `new` to allocate large blocks of memory for your tree. If you need to need to create a new node for your tree or need a buffer for some operation, you should use the buffer pool manager.
* Use binary search to find the place to insert a value when iterating an internal or leaf node. Otherwise, your implementation will probably timeout on Gradescope.
* We recommend (but do not require) that you to follow this rule when implementing split: split a leaf node when the number of values reaches `max_size` after insertion, and split an internal node when number of values reaches `max_size` before insertion.

### Common Pitfalls

* We do not test your iterator for thread-safe leaf scans. A correct implementation, however, would require the Leaf Page to throw a `std::exception` when it cannot acquire a latch on its sibling to avoid potential dead-locks.
* If you implement a concurrent B+Tree index correctly, every thread will always acquire latches from the header page to the bottom. When you release latches, make sure you release them in the same order (from the header page to the bottom).
* When implementing the page classes (Task 1), make sure you only add class fields of trivially-constructed types (e.g. `int`). Do not add vectors and do not modify `key_array_` and `value_array_`.

---

## Testing

You can test your B+ Tree implementation locally using the following tests:

* `test/storage/b_plus_tree_insert_test.cpp`
* `test/storage/b_plus_tree_sequential_scale_test.cpp`
* `test/storage/b_plus_tree_delete_test.cpp`
* `test/storage/b_plus_tree_concurrent_test.cpp`

We strongly encourage you to write additional test cases for yourself to better understand your implementation.

**Compile and run each test:**

```bash
$ mkdir build
$ cd build
$ make b_plus_tree_insert_test -j$(nproc)
$ ./test/b_plus_tree_insert_test

```

## Formatting

Your code must follow the Google C++ Style Guide.

```bash
$ make format
$ make check-lint
$ make check-clang-tidy-p2

```

## Memory Leaks

We use LLVM Address Sanitizer (ASAN) and Leak Sanitizer (LSAN) to check for memory errors. Configure CMake in debug mode to enable them.
