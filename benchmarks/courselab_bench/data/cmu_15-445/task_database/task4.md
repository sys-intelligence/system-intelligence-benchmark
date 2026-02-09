# Phase 4

**YOU ARE ONLY ALLOWED TO MODIFY OR ADD FILES IN THE src DIRECTORY.**

## Overview

In this project, you will add transaction support for BusTub by implementing optimistic multi-version concurrency control (MVOCC). The project consists of four required tasks and two leaderboard benchmarks.

* **Task #1 - Timestamps**
* **Task #2.1 - Storage Format**
* **Task #2.2 - Sequential Scan / Tuple Retrieval**
* **Task #3 - MVCC Executors**
* **Task #4 - Primary Key Index**

This project must be completed individually (i.e., no groups). Before you start, please run `git pull public master` to pull the latest code from the public BusTub repo and then rerun `cmake` to reconfigure the Makefile.

We would recommend reading over everything once before starting to write code. If you don't have time to do that (since this writeup is quite long), you can focus on reading the sections for just Task 1 and 2, as they contain specific guidance on implementation. This will be much faster than missing out on some information, implementing something incorrectly, and then having to start over.

## Background

In the previous projects, BusTub operated as a single-versioned DBMS. You will now add support for MVCC without modifying its core table storage architecture (i.e., table heaps). The high-level version of this MVCC protocol has been used in DBMSs like HyPer and DuckDB.

The storage model in this protocol is similar to the delta table architecture discussed in the lecture. For every single tuple that is stored, the DBMS additionally stores tuple deltas in undo logs. The tuple in the table heap and its corresponding undo logs / deltas form a singly-linked list called the **version chain**. With this version chain, the DBMS logically "stores" every previous version of a tuple. That is, the DBMS only stores the deltas between each version and not complete versions of a tuple.

The DBMS stores undo logs within a transaction's in-memory workspace, and transactions themselves are stored in the transaction manager's in-memory data structure. In a production system these logs would be persisted to disk, but this project does not require that for BusTub.

You will first need to implement the **SNAPSHOT ISOLATION** isolation level for all of your transactions. You will then expand your concurrency control protocol to support the **SERIALIZABLE** isolation level in Task #4.4.

In every test case, all transactions in the test case run at the same isolation level. All concurrent test cases are public, and all hidden test cases are single-threaded. On Gradescope, you will find a description of what each test case is doing.

---

## Project Specification

Like previous projects, we have provided classes that define the APIs you must implement. Do not modify the signatures of the predefined functions or remove predefined member variables in these classes unless indicated. If you do, our test code will not work, and you will not receive credit for the project. You may add private helper functions and member variables to these classes as needed.

Here are the list of files you will likely need to modify in this project:

* `src/include/concurrency/transaction_manager.h`
* `src/concurrency/transaction_manager.cpp`
* `src/include/execution/execution_common.h`
* `src/execution/execution_common.cpp`
* `src/include/execution/executors/seq_scan_executor.h`
* `src/execution/seq_scan_executor.cpp`
* `src/include/execution/executors/index_scan_executor.h`
* `src/execution/index_scan_executor.cpp`
* `src/include/execution/executors/insert_executor.h`
* `src/execution/insert_executor.cpp`
* `src/include/execution/executors/update_executor.h`
* `src/execution/update_executor.cpp`
* `src/include/execution/executors/delete_executor.h`
* `src/execution/delete_executor.cpp`
* `src/include/concurrency/watermark.h`
* `src/concurrency/watermark.cpp`

And here is a list of functions / classes that might be helpful in this project:

* **TableHeap:** `MakeIterator`, `GetTuple`, `GetTupleMeta`, `UpdateTupleMeta`, `UpdateTupleInPlace`, `MakeIterator`, `MakeEagerIterator` (and for Task #3.6 and beyond, everything with `Lock`).
* **Tuple:** `SetRid`, `GetRid`, additional `Tuple` constructors, `Empty`, `IsTupleContentEqual`, `GetValue`.
* **Value:** `ValueFactory::Get____`, `ValueFactory::GetNullValueByType`, `CompareExactlyEquals`.
* **Schema:** `GetColumn`, `GetColumnCount`.
* **TransactionManager:** `UpdateUndoLink`, `GetUndoLink`, `GetUndoLog`, `GetUndoLogOptional`, `UpdateTupleAndUndoLink`, `GetTupleAndUndoLink`
* **Transaction:** All member functions are important, as well as the `UndoLink` and `UndoLog` structs.

You will likely need to frequently map an optional value to something else. You can use the following syntax to write more concise code (monadic operations): `auto x = opt.has_value() ? operation(*opt) : std::nullopt;`.

You can also use C++14 tuple unpacking syntax: `auto [meta, tuple] = iter->GetTuple();`.

The correctness of this project depends on the correctness of your implementation of Project #1 and Project #2. You can get a full score in this project without a complete implementation of Project #3, but this is because you will need to rewrite most of the access method executors you already implemented based on MVCC storage. Additionally, a working implementation of the optimizer rule that transforms a sequential scan into an index scan is required for Task 4.2. Finally, a working aggregation executor from Project #3 is required to complete the leaderboard test in this project.

We do not provide solutions for previous projects.

---

## Task #1 - Timestamps

In BusTub, each transaction is assigned two timestamps: a read timestamp and commit timestamp. We will walk through how those timestamps are assigned. In this task, you will need to implement this on the transaction manager so that it can assign timestamps correctly to transactions.

### 1.1 Timestamp Allocation

When a transaction begins, it is assigned a **read timestamp** that is equal to the commit timestamp of the most recently committed transaction. At a high level, you can think of this as recording the timestamp of the latest atomic write into the database. The read timestamp determines what data can be safely and correctly read by a transaction. That is, the read timestamp determines the latest version of a tuple that the current transaction can see.

When a transaction commits, it is assigned a monotonically-increasing **commit timestamp**. The commit timestamp determines the serialization order of the transactions. Since these commit timestamps are unique, we can also uniquely identify committed transactions by their commit timestamp.

Here is an example of a table heap and version chain after several writes / updates to 4 tuples in the table heap (A, B, C, D):

![](https://15445.courses.cs.cmu.edu/fall2025/project4/img/1-1-ts.png)

In this diagram, A1 refers to the first version of tuple A, and A3 refers to third version of tuple A. A4 refers to the fourth version of tuple A, and it is also the most recent or "true" version of tuple A. B4 and C4 are actually the third version of tuples B and C respectively, and we are only notating it like this for the sake of the explanation below.

The timestamps (ts=#) refer to the commit timestamps of the transactions that each of the tuples belong to. So [A1, B1, C1] belong to the transaction with commit timestamp = 1 (which we can shorthand refer to as transaction 1), and [A3, B3, D3] belong to the transaction with commit timestamp = 3 (transaction 3). The most recent committed transaction in this diagram is the transaction with commit timestamp = 4 with [A4, B4, C4].

Suppose we have a transaction with an assigned read timestamp of 3. This means our transaction started after transaction 3 committed and before transaction 4 committed. Thus, our transaction is only be able to observe [A3, B3, C2, D3].

For [A, B, C], our transaction cannot observe [A4, B4, C4] because those version of the tuples all have a timestamp of 4 (which is in the future relative to our read timestamp of 3). Our transaction needs to traverse the undo logs for each tuple and read the first version it encounters that has a version less than or equal to 3. For A and B, the first versions it encounters are A3 and B3. For C, the first version encountered is C2. For D, since the current version of the tuple already has a timestamp of 3, it is safe to read directly.

Another example is if our read timestamp was 2, then our transaction would see only [A2, B1, C2], since D was only created at timestamp 3 (which is in the future relative to our read timestamp 2).

You will need to assign the transactions with the correct read timestamp and commit timestamp in this task. See `TransactionManager::Begin` and `TransactionManager::Commit` in `src/include/concurrency/transaction_manager.h` for more information. We have already provided the starter code for `TransactionManager::Abort`, and you do not need to change anything in `Abort` in order to get full points for Task #1.

### 1.2 Watermark

The **watermark** is the lowest read timestamp among all transactions that have not yet committed or aborted. If there is no such a transaction, the watermark is the latest commit timestamp. The easiest way of computing the watermark is to iterate over all transactions in the transaction manager map and find the minimum `read_ts` among all in-progress transactions.

However, this simple strategy is inefficient. In this task, you will need to implement an algorithm in O(log N) time complexity that computes the watermark. Please refer to `watermark.h` and `watermark.cpp` for more information. You will also need to call `Watermark::AddTxn` and `Watermark::RemoveTxn` when a transaction starts / commits / aborts.

There are many ways to do this. The reference solution implements an amortized O(1) algorithm using a hash map, and there is additionally a useful container in the C++ standard library that might make an O(log N) implementation easy.

You should pass all test cases in the `TxnTimestampTest` suite at this point.

---

## Task #2 - Storage Format and Sequential Scan

BusTub stores transaction data in three places: the table heap, the transaction manager, and inside each transaction's workspace. The table heap always contains the latest tuple data. The transaction manager stores a pointer to the latest undo log for every tuple (`PageVersionInfo`). Transactions store the undo logs that they create, which record how a transaction has modified a tuple.

Below is a representation of the same diagram as above, but with the `PageVersionInfo` struct included and the undo logs located in a specific transaction's workspace. The dotted lines in the diagram are not pointers, but rather are logical connections via the transaction manager.

![](https://15445.courses.cs.cmu.edu/fall2025/project4/img/2-1-storage-format.png)

To retrieve a tuple at any given read timestamp, you will need to (1) fetch all modifications (aka. undo logs) that happened after the given timestamp, and (2) roll back those modifications (“undo” the undo logs) from the latest version of the tuple to recover the past version of that tuple.

This is similar to the delta table storage model that we covered in the lectures, except that there is no physical “delta table” to store the delta records. Instead, these records are stored within the workspace of each transaction (not being persisted on the disk) so as to simplify the implementation.

### Data Structures & Helper Functions

This section is an introduction to guide you through the data structures you will need for tuple reconstruction and further operations. We would recommend reading this introduction together with the starter code. You come back to this section if you encounter any problems or confusion in other tasks.

The DBMS stores `Tuple` and `TupleMeta` data in `TableHeap` (`src/include/storage/table_heap.h`). You can call helper functions like `GetTuple` or `GetTupleMeta` to get that data, `UpdateTupleInPlace` to update tuple for single-threaded test cases, and `InsertTuple` to insert tuples into the table heap (these functions are defined in `table_heap.h`). You may notice that there are also functions like `UpdateTupleInPlaceWithLockAcquired`, which are functions you will use for the concurrent tasks.

The transaction header (`src/include/concurrency/transaction.h`) contains the classes and objects used to track a transaction's runtime behavior and state.

The `UndoLog` struct stores the information about the modification / deletion of a tuple by a transaction. Task 2.1 introduces the format of `UndoLog` in detail. The DBMS can reconstruct tuples based on these `UndoLogs`. Each transaction stores a vector of `UndoLogs` deltas of every tuple that the transaction has modified. For example, if txn1 updates tuple 1 and tuple 2, txn1 will store an `UndoLog` for both tuple 1 and tuple 2. The transaction will record both the delta between the previous versions of tuple 1 and tuple 2 as well as txn1's version of them. Your implementation should call `ModifyUndoLog` to modify an existing `UndoLog` and `AppendUndoLog` to append new `UndoLogs` (`src/include/concurrency/transaction.h`). By storing all of the `UndoLog` of a single transaction together, we can easily make updates to these modified tuples and their version info when the transaction commits or aborts.

The `UndoLink` struct is the pointer to the `UndoLog`. We use `UndoLink` to link all the `UndoLog` for each tuple together. They are defined as below:

```cpp
/** Represents a link to a previous version of this tuple */
struct UndoLink {
  /* Previous version can be found in which txn */
  txn_id_t prev_txn_{INVALID_TXN_ID};
  /* The log index of the previous version in `prev_txn_` */
  int prev_log_idx_{0};
};

```

An `UndoLink { prev_txn_: txn5, prev_log_idx_: i }` points to the ith `UndoLog` in txn5's `undo_logs_` buffer. You can get the target `UndoLog` from given `UndoLink` by calling `GetUndoLog` and `GetUndoLogOptional` (`src/concurrency/transaction_manager_impl.cpp`). If the `prev_txn_` in the `UndoLink` has an invalid transaction id, it means that the `UndoLink` is invalid and it does not point to any valid `UndoLog`, so you only want to use `GetUndoLog` when you know the `UndoLink` is valid, otherwise you can use `GetUndoLogOptional`.

### 2.1 Tuple Reconstruction

In this task, you will implement the tuple reconstruction algorithm via the `ReconstructTuple` function, defined in `execution_common.cpp`. During this project, you will likely find that many functionalities can be shared by different components in the system. You can define helper functions in `execution_common.cpp`.

`ReconstructTuple` takes four inputs:

1. A tuple schema.
2. A base tuple.
3. Metadata (both stored in the table heap).
4. A list of undo logs in order of most recent modification to oldest modification.

Here is an example of reconstructing a tuple:
![](https://15445.courses.cs.cmu.edu/fall2025/project4/img/2-2-undo-log.png)

Base tuples (under "latest version in table heap") always store a value for every column in their schema (or in other words, they are complete and valid tuples). Undo logs, however, only contain the columns that were changed by an operation. Undo logs also have an `is_delete` flag that represents the deletion of the entire tuple.

Both the base tuple metadata and the undo logs will have `is_delete` flags, and they will not always be equal. In task 4.2, you will have to "insert" a tuple into an existing RID, and therefore you will need this `is_delete` flag in your `UndoLog` to perform this kind of operation (imagine inserting and deleting the same exact tuple in a cycle). An example of the `is_delete` flag works is illustrated below. Make sure you understand that these undo logs are going backwards in time. As an exercise, try to figure out the sequence of operations that could have led to this specific version chain:

![](https://15445.courses.cs.cmu.edu/fall2025/project4/img/2-2-undo-log-with-del.png)

`ReconstructTuple` should apply all modifications provided to the function without looking at the timestamp in the metadata or undo logs. It does not need to access data other than the ones provided in the function parameter list. In other words, make sure you are not passing too many undo logs to `ReconstructTuple`.

Below is an illustration of the structure of `UndoLog`:

![](https://15445.courses.cs.cmu.edu/fall2025/project4/img/2-4-undo-log-format.png)

`UndoLog` represents a partial modification to some tuple (at some point in time determined by the `ts_` field). The `modified_fields_` member in `UndoLog` is a vector of `bool` that has the same length as the number of columns in the table schema. If one of the booleans is set to true, it indicates that the corresponding field in the tuple has been updated by that `UndoLog`. For example, if the 3rd element (index 2) of the `modified_fields_` vector is set to true, then that means the third column of the tuple was updated.

The `tuple_` field contains the partial `Tuple`, and it should have the same number of values / columns as the `modified_fields_` vector has trues. To retrieve a value from the partial tuple, you will need to construct a partial `Schema` based on the table schema and the modified fields. You can then use that partial `Schema` to extract values out of the partial `Tuple`.

The timestamp (`ts_`) is the commit timestamp that this `UndoLog` corresponds to. We also store a link to the next `UndoLog` (`prev_version_` is stored via an `UndoLink`). If an `UndoLog` is the last in the version chain, `TxnId` (which corresponds to `prev_txn_` inside `UndoLink` in the code) will be set to `INVALID_TXN`. You can use the `prev_version_.IsValid()` helper to check this quickly. As a reminder, you do not need to use or even examine the timestamp (`ts_`) field and the previous version (`prev_version_`) field in `ReconstructTuple`, as `prev_version_` should only be used by the caller of `ReconstructTuple` to figure out what `UndoLogs` to place in the input vector.

In the example above, we are storing tuples with four columns. This specific `UndoLog` represents a modification of fields 2 and 3. Try to write out pseudocode (on paper) of how to reconstruct the past tuple with these 2 specific fields changed back. Then, try to generalize that algorithm for any type of input tuple, any number of fields modified, and for any number of undo logs. Once you've done that, you can write `ReconstructTuple`!

### 2.2 Sequential Scan (Tuple Retrieval)

In this task, you will need to rewrite your sequential scan executor from Project #3 to support retrieving data from the past (based on the read timestamp of a transaction).

For every tuple that your new sequential scan executor scans from the table heap, it should retrieve all of the undo logs for that tuple up to the transaction read timestamp, reconstruct the past tuple version, and then output that past tuple. You will need to implement the `CollectUndoLogs` helper function in `execution_common.cpp`. This function returns all of the undo logs you need to reconstruct the tuple with respect to the given transaction's read timestamp.

Given the current transaction's read timestamp, there are three cases you will need to handle:

1. **The tuple in the table heap is the most recent data relative to the read timestamp.** You can figure this out by checking the timestamp in the tuple's metadata. In this case, no undo needs to be performed, and `CollectUndoLogs` should return an empty vector.
2. **The tuple in the table heap has either been modified by another uncommitted transaction, or it is newer than the transaction read timestamp.** In this case, you will need to iterate the version chain to collect all undo logs that are after the read timestamp.
3. **The tuple in the table heap contains modifications by the current transaction.** In other words, we are reading a tuple that we ourselves have modified. An explanation of this case is below.

To support case 3 without making changes to the structure of our timestamps (which are just `int64_t`), we will use the higher bits of the timestamps as tags to represent "temporary" timestamps. In BusTub, a commit timestamp is valid if it is in between 0 and `TXN_START_ID - 1`. `TXN_START_ID` is defined as the second most significant bit of a 64-bit integer (`1 << 62`).

If the second most significant bit of a timestamp is set to 1 (`& 1 << 62`), it means that the tuple has been modified by a transaction and that transaction has not been committed yet. We call this timestamp a **“temporary transaction timestamp”**, which is computed via `TXN_START_ID + txn_human_readable_id = temp_txn_id`. We adopt this methodology to distinguish between a committed tuple with a commit timestamp and an uncommitted tuple under some specific transaction ID. `UndoLogs` should never contain temporary transaction timestamps (we will explain in later sections).

The reason we do not use the actual most significant bit (`1 << 63`) is so that we can continue to compare temporary timestamps in a straightforward way with `<` and `>`. Setting the most significant bit would cause timestamps to be negative.

The first transaction ID in BusTub is `TXN_START_ID`, and IDs are monotonically increasing. Make sure you understand that transaction IDs are not the same as commit timestamps, even though both are monotonically increasing. Since `TXN_START_ID` is a large number that is hard to interpret, we will generate a human-readable id by stripping the highest bit when logging and debugging. You should not need to manually calculate the temporary timestamp for uncommitted transactions, and you can use the existing helper function `GetTransactionTempTs` to return temporary timestamp for this transaction (`src/include/concurrency/transaction.h`).

We will use the notation `txn***`, where `***` is a human-readable ID, for representing transaction IDs. For example, `txn42` represents the transaction with ID `TXN_START_ID + 42`, or the transaction with a human-readable ID of 42. Suppose that the current transaction has a human-readable ID of 3, and it scans a base tuple with timestamp `TXN_START_ID + 3`. The transaction then knows that it itself was the most recent modifier of the tuple. Handling this sub-case of case 3 is equivalent to handling case 1. Think about what should happen if it sees the temporary transaction timestamp of a different uncommitted transaction.

#### Examples

Suppose `txn9` updates tuple A, which means tuple A's timestamp will be set to `TXN_START_ID + 9`. When `txn9` eventually commits, tuple A's timestamp will be replaced with `txn9`'s commit timestamp. In code, this will look like the following:

1. `txn9` modifies tuple A.
2. `txn9` uses `GetTransactionTempTs` to set tuple A's timestamp to `TXN_START_ID + 9`.
3. When `txn9` commits, it replaces tuple A's timestamp with its new commit timestamp via `GetCommitTs`.
4. Other transactions can use tuple A's timestamp to distinguish between whether it has been modified by a committed or uncommitted transaction.
5. You can do this by simply comparing the timestamp with `TXN_START_ID`.

Here's our final example for `SeqScanExecutor`. To make our illustration easier to understand, `TXN_START_ID` in the below example will be 1000 instead of (`1 << 62`). Therefore, 1009 represents the temporary transaction timestamp where the transaction has an ID of 9 (`TXN_START_ID + 9 = 1009` in this example).

Let's take a look at the following example, where we traverse the version chain to collect the undo logs to construct the tuples that the user requests:

![](https://15445.courses.cs.cmu.edu/fall2025/project4/img/2-3-seqscan.png)

Suppose we have a transaction with ID 9 and read timestamp of 3. `txn9` has not yet committed (due to the presence of the temporary transaction timestamp 1009). The result of a sequential scan in `txn9` of the table should be: `[(A, 9), (B, 9), (C, 2), (D, 9)]`. For all of the tuples except `(C, 2)`, transaction 9 was the one that already modified them, so it does not need to traverse the undo logs. However, `(C, 2)` has a commit timestamp of 4, which is greater than our read timestamp of 3. Transaction 9 then knows to traverse the undo logs to find the first version of this tuple that has a commit timestamp less than or equal to 3.

Consider some other transaction that has a read timestamp of 4. The result of a sequential scan of this transaction will be: `[(A, 3), (B, 3), (C, 4)]`. For `(A, 3)` and `(B, 3)`, the table heap contains a pending update from `txn9`, so the transaction will need to traverse the version chain to get the last update before/at timestamp 4. `(C, 4)` is the latest update at read timestamp 4. `(D, 9)` is a pending update by transaction 9, and since it does not have a version chain, we do not need to return it. In general, if there are no previous versions of a tuple at a given read timestamp, then the transaction should treat it as if the tuple does not exist.

These example are oversimplified compared with the test cases. You will also need to think about NULL data and data types other than integers when implementing `SeqScanExecutor`.

Once you have finished implementing `CollectUndoLogs` and `ReconstructTuple`, it should be clear how to finish the MVCC version of `SeqScanExecutor` using these two functions. The base tuple, tuple metadata, and the first undo link belonging to the tuple can be obtained via `GetTupleAndUndoLink`.

Our test cases will manually set up some transactions and the table heap content. You do not need to implement the insert executor to test your sequential scan implementation. At this point, you should pass all test cases in `TxnScanTest`.

---

## Task #3 - MVCC Executors

In this section, you will need to implement the data modification executors. This includes the insert executor, delete executor, and update executor. Starting from this task, your implementation will not be compatible with Project #3, as we only support schemas of fixed-sized data types.

### 3.1 Insert Executor

Your insert executor implementation should be similar to the one in Project #3. You can create a new tuple in the table heap, and you will need to correctly construct the tuple's metadata. The timestamp in the table heap should be set to the transaction temporary timestamp, as described in Task 2.2. You should also add the RID to the write set via `AppendWriteSet` at this point. Here is a simple illustration of `txn9` inserting (D, 3) into the table:

![](https://15445.courses.cs.cmu.edu/fall2025/project4/img/3-1-insert.png)

We have provided the helper functions `UpdateTupleInPlace` and `UpdateUndoLink` to update the tuple in the table heap and the undo link respectively. These functions mimic an atomic compare-and-swap operation, where you will need to provide a check function. The pseudo code for the two functions are as below:

```cpp
UpdateUndoLink(rid, new_undo_link, check_function) {
  take the table heap lock / undo link lock
  retrieve the data from table heap / undo link
  call user-provided check function, if check failed, return false
  update the data and return true
}

```

All test cases for this task are single-threaded, and therefore you can simply pass a `nullptr` to the check parameter to skip the check and use `UpdateTupleInPlace` and `UpdateUndoLink` separately. For the future concurrent test cases, you will need to get / update both the `Tuple` and the `UndoLink` atomically so that other transactions cannot change another transaction's intermediate result. Consider the following scenario:

1. `txn1` calls `GetTuple` to check whether it can update a tuple.
2. `txn2` modifies the tuple and its `UndoLink`.
3. `txn1` then calls `GetUndoLink` and gets the incorrect `UndoLink`.
4. `txn1` updates the tuple and `UndoLink` based on incorrect information.

In this example, you might want to use `UpdateTupleAndUndoLink` and `GetTupleAndUndoLink` to get/set atomically (`src/concurrency/transaction_manager_impl.cpp`). Starting at Task 4.2, you may need to implement the check logic to detect write-write conflicts when there are multiple threads updating a tuple and its metadata / `UndoLink` concurrently.

### 3.2 Commit

Only one transaction is allowed to execute the `Commit` function at a time, and you should ensure this by using the `commit_mutex_` in the transaction manager. In this task, you will need to extend your `Commit` implementation in the transaction manager with transaction commit logic. Here is some rough pseudocode:

1. Take the commit mutex.
2. Obtain a commit timestamp (you will likely need to do a `.load() + 1` instead of `.fetch_add(1)` here, think about why in relation to `Begin`).
3. Iterate through every tuple that has been modified by this transaction (via the write set) and set the timestamp of the base tuples to the commit timestamp. You will need to maintain the write set in all modification executors (insert, update, delete).
4. Set the transaction to the `COMMITTED` state.
5. Update the commit timestamp of the transaction.
6. Update `last_committed_ts_` (you can do the `.fetch_add(1)` here).

![](https://15445.courses.cs.cmu.edu/fall2025/project4/img/3-2-commit.png)

You should have implemented most of the above logic as a part of task 1, so you will just need to add the iterating table logic.

#### TxnMgrDbg

At this point, we strongly recommend that you implement the debug function `TxnMgrDbg`. This should print out the table heap content and the version chain for each tuple. If you come to us without this function written, we will ask you to implement it first.

Our test cases will call your debug function after each important operation and you can print anything you want to examine the version chain. This debug function will be incredibly helpful in debugging your implementation for future tests. An example debug function can be seen in our reference solution running in the BusTub Web Shell with the command `\dbgmvcc {table_name}` (you can find the developer console on Chrome by pressing F12).

Our debug function is prettier than what yours needs to be. Your version can look like this (taken from `CollectUndoLogTest` in `txn_scan_test`):

On the BusTub Web Shell, `\dbgmvcc` looks like this:

#### Interactive Testing

Here is an example of using the BusTub Web Shell to compare your implementation against ours.

```bash
make -j`nproc` shell && ./bin/bustub-shell
bustub> CREATE TABLE t1(v1 int, v2 int);
bustub> INSERT INTO t1 VALUES (1, 1), (2, 2), (3, 3);
bustub> \dbgmvcc t1 -- call your `TxnMgrDbg` function to dump the version chain
bustub> BEGIN;
txn?> INSERT INTO t1 VALUES (4, 4);
txn?> \txn -1
bustub> SELECT * FROM t1; -- the newly-inserted row should not be visible to other txns
bustub> \txn ? -- use the id you see before
txn?> COMMIT;

```

You can also use the BusTub Netcat shell to start an interactive session with transactions. You will need to install `nc` (netcat) in order to use this interactive shell.

```bash
make -j`nproc` nc-shell && ./bin/bustub-nc-shell
bustub> CREATE TABLE t1(v1 int, v2 int);
bustub> INSERT INTO t1 VALUES (1, 1), (2, 2), (3, 3);
bustub> \dbgmvcc t1 -- call your `TxnMgrDbg` function to dump the version chain
# in another terminal
nc 127.0.0.1 23333
bustub> INSERT INTO t1 VALUES (4, 4);
# in yet another terminal
nc 127.0.0.1 23333
bustub> SELECT * FROM t1; -- the newly-inserted row should not be visible to this txn
bustub> COMMIT;

```

We provide the reference solution running in your browser in the BusTub Web Shell.

Starting from this task, all of our test cases are written in SQL. As long as your SQL query result matches the reference output, you will get full points for a test case. We do not check the exact content of your version chain, but we will check for the number of `UndoLogs` and number of table heap tuples to ensure you are maintaining the version chain correctly and efficiently. We will also use your `ReconstructTuple` to verify the correctness of your generated `UndoLogs`.

### 3.3 Generate Undo Log

Before implementing the update and delete executors, you will need to implement `GenerateNewUndoLog` and `GenerateUpdatedUndoLog`. Given the original base tuple and the modified target tuple, you should return the `UndoLog` that should be stored in the transaction making the modification.

Make sure you understand the difference between `GenerateNewUndoLog` and `GenerateUpdatedUndoLog`. Suppose a transaction updates a tuple several times. We expect only one `UndoLog` for every update within a specific transaction. `GenerateNewUndoLog` is used for every first modification of each tuple. After that, `GenerateUpdatedUndoLog` is used to consolidate modifications into one `UndoLog`.

There are three cases to consider:

* **Update:** In this case, generate the `UndoLog` based on base tuple and target tuple. If this is not the first update within this transaction, combine it with the original `UndoLog` via `GenerateUpdatedUndoLog`. A transaction should hold at most one undo log for each RID. If a transaction needs to update a tuple twice, it should only update the base tuple and its current undo log.
* **Delete:** In this case, you need to store the entire tuple in the `UndoLog` so that the entire tuple can be reconstructed. Think about how you would achieve this with several modifications within a transaction.
* **Insert:** The insertion you implemented in Task 3.1 always creates a new tuple in the table heap with a new RID. In other words, you never need a `UndoLog` for an insertion. However, in Task 4.2, you might have to insert a tuple back into a deleted tuple. You will know it's an insert case when the `base_tuple` is a `nullptr`.

You will find `Tuple::IsTupleContentEqual` and `Value::CompareExactlyEquals` useful when computing the `UndoLog`.

### 3.4 Update & Delete Executor

In this task, you will need to implement the logic that actually generates `UndoLogs` and updates the table heap base tuples. The update and delete executors are quite similar.

Before updating or deleting a tuple, you will need to check for **write-write conflicts**. There are a few cases to be aware of. If a tuple is being modified by an uncommitted transaction, no other transactions are allowed to modify it. If they do, there will be a write-write conflict and the transaction conflicting with a previous transaction should be aborted. Another write-write conflict case is when a transaction A deletes a tuple and commits, and another transaction B that starts before A deletes the same tuple after transaction A has committed. The transaction state should be set to `TAINTED` when a write-write conflict is detected, and you will need to throw an `ExecutionException` in order to mark the SQL statement as failed. `ExecuteSqlTxn` will return false if there is an execution exception. At this point, we do not require you to implement the actual abort logic. The test cases in this task will not call the `Abort` function.

Your update executor should be implemented as a pipeline breaker: it should first store all tuples from the child executor to a local buffer before writing any updates. After that, it should pull the tuples from the local buffer, compute the updated tuple, and then perform the updates on the table heap.

At this point, all test cases are single-threaded, and therefore you do not need to think hard about race conditions that might occur during the update / delete process. The only condition for detecting write-write conflict is to check the timestamp of the base tuple metadata.

![](https://15445.courses.cs.cmu.edu/fall2025/project4/img/3-4-write-conflict.png)

Let's go through the example above, where we show the 3 different cases you will need to handle before making any changes.

1. In case (1), `txn10` has deleted the (A, 2) tuple and has not committed yet. Suppose `txn9` has a read timestamp of 3. `txn9` can then still read the old version of the tuple (A, 2).
2. In case (2), if any other transactions other than `txn9` try to update / delete this B tuple, they will need to abort. For example, if `txn10` eventually needs to update / delete the tuple, `txn10` should be aborted with a write-write conflict.
3. In case (3), there was some other transaction that updated (C, 2) to (C, 4) with a commit timestamp of 4. `txn9` can read an old version of the tuple (C, 2). Again, if `txn9` eventually needs to update / delete the tuple, `txn9` should be aborted with a write-write conflict, because there is a newer update that happens after the transaction read timestamp.
4. There is also a 4th case, where a transaction wants to update a modification it made itself (self modification). If a tuple has already been modified by the current transaction, you should not regard this as write-write conflict.

After checking the write-write conflict (you should write a helper function for that), you can proceed with implementing the update / delete logic:

1. Create the undo log for the modification by `GenerateNewUndoLog` or `GenerateUpdatedUndoLog`.
2. Update the next undo link of the tuple to point to the new undo log.
3. Update the base tuple and metadata in the table heap (this step can be done with the previous step atomically using `UpdateTupleAndUndoLink`).

Here's an example illustrating a delete:

![](https://15445.courses.cs.cmu.edu/fall2025/project4/img/3-4-delete.png)

Here's an example illustrating an update:

![](https://15445.courses.cs.cmu.edu/fall2025/project4/img/3-4-update.png)

Make sure you understand these diagrams before you start implementing your executors. If you have any questions, please ask us for clarifications!

In the example below, `txn9` first updates the tuple to (A, 4), then to (A, 5), then to (B, 5), then to (A, 5), and then finally deletes it. Throughout the process, `txn9` keeps exactly one `UndoLog` for the tuple. When we update (B, 5) to (A, 5), we could have gone all the way back to the beginning of the transaction to compute the partial update (_, 5) (since combining all of the deltas gets you from (A,3) to (A, 5)). However, we recommend simply adding modifications to the existing `UndoLog` (so that it has the full change (A, 5)), which will make it easier to handle concurrency issues. In other words, make sure you only add / update data in the undo log, and do not remove data.

![](https://15445.courses.cs.cmu.edu/fall2025/project4/img/3-4-update-2.png)

In this next example, `txn9` inserts a tuple, makes several modifications, and then removes it. In this case, you can directly modify the table heap tuple without generating any undo logs.

![](https://15445.courses.cs.cmu.edu/fall2025/project4/img/3-4-update-3.png)

We have set the commit timestamp to 0 at the end because this tuple is inserted by `txn9` and removed by `txn9`, which means that it never actually existed. If the version chain did contain undo logs, it should be set to the actual commit timestamp instead of 0 so that the undo logs can be accessed with a transaction with lower read timestamp. You could also just ignore this case and follow the usual commit logic. As long as you can read the correct data at each timestamp, this does not matter until Task #4.4.

In this project, we will always use fixed-sized types, and therefore `UpdateTupleInPlace` should always succeed without throwing an exception.

Putting everything together for update / deletes, you should:

1. Get the RID from the child executor.
2. Generate the updated tuple.
3. For self-modification, update the table heap tuple, and optionally the undo log in the current transaction if there is one.
4. Otherwise, generate the undo log, and link them together.

At this point, you should pass everything in the `TxnExecutorTest` test besides the garbage collection test case.

### 3.5 Stop-the-world Garbage Collection

In the code we have given you, once we have added the transaction into the transaction map, we never remove it. We do this because transactions with a lower read timestamp might need to read the undo logs stored in the previous committed or aborted transactions. However, imagine if we have had thousands or even millions of transactions. It is likely that many of the past transactions have been completely overwritten by more recent ones, and we no longer need to store their undo logs. In this task, you will need to implement a simple garbage collection strategy that removes unused transactions.

Garbage collection is triggered manually when `GarbageCollection` is called. The test cases will only call this function when all transactions are paused. Therefore, you do not need to worry too much about race conditions when doing garbage collection. In Task 1, you have already implemented an algorithm to compute the watermark (the lowest read timestamp in the system). In this task, you will need to remove all transactions that do not contain any undo logs visible to a transaction with the lowest read timestamp.

You will need to traverse the table heap and the version chain to identify undo logs that are still accessible by a transaction with the lowest read timestamp (make sure that you understand this: an undo log that is invisible to this transaction should be invisible to all transactions). If a transaction is committed / aborted, and does not contain any undo logs visible to a transaction with the lowest read timestamp, you can simply remove it from the transaction map.

The example below illustrates the case where the watermark timestamp is 3 and we have `txn1`, `txn2`, and `txn9` committed. `txn1`'s undo logs are no longer accessible because every undo log with commit timestamp 1 has been overwritten by updates with commit timestamps less than or equal to 3. Thus we can directly remove `txn1`. `txn2`'s undo log for tuple (A, 2) is not accessible, but its undo log for tuple (C, 2) is still accessible because there has been no additional updates, so we cannot remove it right now.

![](https://15445.courses.cs.cmu.edu/fall2025/project4/img/3-5-garbage-collection.png)

After removing `txn1`, there will be dangling pointers to a removed undo log, as indicated in dashed lines. You **DO NOT** need to update the previous undo log to modify the dangling pointer and make it an invalid pointer, and it is fine to leave it there for this project. If everything in your implementation is correct, your sequential scan executor should never even attempt to dereference these dangling pointers, as they are below the watermark. However, we still recommend you to add some asserts in your code to ensure this will never happen.

At this point, you should pass the `TxnExecutorTest`.

### 3.6 Abort

Before this task, transactions that go into the `TAINTED` state will cause other transactions to abort on the write-conflicting tuples. In this task, you are required to implement the abort logic, so that we can continue modifying the tuples when any of the transactions aborts. Recall that we detect write-write conflicts by checking if there is an ongoing modification to a tuple. When aborting a transaction, we should revert this change, so that other transactions can write to the tuple.

You can choose which design you want to implement in this task.

#### Implementation #1

![](https://15445.courses.cs.cmu.edu/fall2025/project4/img/5-abort-2.png)

In this example, we are going to abort `txn9`. You can simply undo the tuple and set the table heap to the original value. This is easier to implement and will leave your version chain with two items with timestamp 3. Your sequential scan / index scan executor should correctly handle this situation after the transaction is aborted.

With this implementation, aborted transactions will have undo logs in the version chain, and cannot be immediately reclaimed in garbage collection.

#### Implementation #2

![](https://15445.courses.cs.cmu.edu/fall2025/project4/img/5-abort.png)

In this example, aborting `txn9` will atomically link the undo link to the previous version and update the table heap. You will need to use `UpdateTupleAndUndoLink` / `GetTupleAndUndoLink` to update / read tuples and undo links atomically. With this implementation, you do not need to wait until the watermark before removing the aborted transaction from the transaction map.

If the transaction inserts a fresh new tuple without undo logs, the abort process simply sets it to a deletion marker with ts = 0. The commit timestamp in BusTub starts from 1, and therefore setting it to 0 will be safe.

You do not need to revert index modifications. Anything added to the index will stay there and will not be removed. You also do not need to actually remove a tuple from the table heap. If you need to revert an insertion, simply set it to a deletion marker.

You should allow multiple threads aborting in parallel. That is, do not take the `commit_mutex` or any other locks throughout the whole function.

---

## Task #4 - Primary Key Index

BusTub supports primary key indexes, which can be created in the following way:

```sql
CREATE TABLE t1(v1 int PRIMARY KEY);
CREATE TABLE t1(v1 int, v2 int, PRIMARY KEY(v1, v2));

```

When the primary key is specified in a `CREATE TABLE` statement, BusTub will automatically create an index with its `is_primary_key` property set to true. In BusTub, a table can have at most one primary key index. Primary key indexes ensure the uniqueness of the primary key. In this task, you will need to handle primary key indexes in your MVCC executors. The test cases will not create secondary indexes using `CREATE INDEX`, and thus you do not need to maintain secondary indexes in this task.

### 4.1 Index Insert

You will need to modify your insert executor to correctly handle the primary key index. At the same time, you will also need to think about the case where multiple transactions are inserting the same primary key from multiple threads. Inserting into an index can be done with the following steps:

1. First, check if the tuple already exists in the index. If it exists, abort* the transaction.
* *This only applies to Task 4.1. If you are going to implement Task 4.2, then it is possible that the index points to a deleted tuple, and in this case, you should not abort.*


2. You only need to set the transaction state to `TAINTED` in Task 4. `TAINTED` means that the transaction is about to be aborted, but the data has not been cleaned up yet. You do not need to implement the actual abort process until Task #3.6. The tainted transaction will leave some tuple in the table heap, and you do not need to clean it up. When another transaction inserts into the same place and detects a write-write conflict, it should still be regarded as a conflict. After setting the transaction to `TAINTED` state, you will also need to throw an `ExecutionException` so that `ExecuteSql` will return false and the test case will know that the transaction / SQL was aborted.
3. Next, create a tuple on the table heap with a temporary transaction timestamp.
4. After that, insert the tuple into the index. Your index should return false if the unique key constraint is violated.

Between steps (1) and (3), it is possible that other transactions are doing the same thing. A new entry could be created in the index before the current transaction could create it. In this case, you will need to abort the transaction, and there will be a tuple in the table heap that is not referenced by any entry in the index.

In this example, let us go through `txn9` attempting to insert A, B, and C separately (assuming the only column of the tuple is the primary key). Assume that A already exists in the index, and C has been inserted by an uncommitted transaction. We have removed the `PageVersionInfo` structure in the diagram for clarity.

![](https://15445.courses.cs.cmu.edu/fall2025/project4/img/4-1-insert-index.png)

1. **Inserting A:** the key already exists in the index, violating the uniqueness requirement for primary key, thus aborting the transaction.
2. **Inserting B:** as there is no conflict in the index, first create a tuple in the table heap, and then insert the RID of the newly-created tuple into the index.
3. **Inserting C:** we assume here that there is another `txn10` also trying to insert C. `txn9` first detects no conflict in the index and creates a tuple in the table heap. Then, in the background, `txn10` does (2) and (3), creating a tuple and updating the index. When `txn9` tries inserting into the index in step (4), there will be a unique key violation reported by the index, and therefore `txn9` should go into the `TAINTED` state.

You do not need to implement the MVCC index scan executor at this point. Our test case will use range queries instead of equal queries to avoid the sequential scan to index scan rule being invoked, so that sequential scans will not be converted to index scans.

Once you finish this, you should pass the first concurrent test case in this project, where we test if your implementation works correctly when multiple threads insert the same key.

### 4.2 Index Scan, Delete, & Update

In this task, you will need to add index support for the delete and update executors, as well as the MVCC index scan executor.

Once an entry is created in the index, it will always point to the same RID and will **NOT** be removed even if a tuple is marked deleted. We do this so that an earlier transaction can still access the history with the index scan executor. To support this, you will need to revisit your insert executor. Consider the case that the insert executor inserts into a tuple which has been removed by the delete executor. Your implementation should update the deleted tuple instead of creating a new entry, because an index entry always points to the same RID once created. You will need to correctly handle the write-write conflict detection and unique constraint detection.

In this example, tuple (B, 2) has been deleted by a transaction with commit timestamp 3. We **DO NOT** remove the entry from the index when a tuple is deleted, and therefore the index may point to a deletion marker, and will **ALWAYS** point to the same RID once it is there. When `txn9` inserts (B, 3) into the table with the insert executor, it should **NOT** create a new tuple. Instead, it should update the deletion marker to the inserted tuple, as if it were an update.

![](https://15445.courses.cs.cmu.edu/fall2025/project4/img/4-2-update-index.png)

You will also need to think about other race conditions at this point. For example, if multiple transactions are updating the `UndoLink` at the same time. You should correctly abort some of them and let exactly one of them proceed without losing any data. Starting from this task, you will need to use the atomic helper function `UpdateTupleAndUndoLink`/`GetTupleAndUndoLink` and pass in the check function to avoid race conditions.

You should observe in the above example, there will be a small amount of time when the table heap contains a (deleted) tuple with the same timestamp as the first undo log. Your sequential scan executor should also handle this case correctly after you have implemented updates and deletes.

### 4.3 Primary Key Updates

You will need to handle when the primary key gets updated. In this case, the update should be implemented as a delete on the original key and an insert on the new key.

Let us go through the case where `txn9` is executing `UPDATE table SET col1 = col1 + 1` in order, where `col1` is the primary key. `txn9` first inserts (2, B) (along with any tuples that have new primary keys) into the table:

![](https://15445.courses.cs.cmu.edu/fall2025/project4/img/4-3-update-pk.png)

Now we start updating the table with `col1 = col1 + 1`, where we delete all tuples that will be updated:

![](https://15445.courses.cs.cmu.edu/fall2025/project4/img/4-3-update-pk-2.png)

Next, we insert the updated tuple back to the table with new primary keys:

![](https://15445.courses.cs.cmu.edu/fall2025/project4/img/4-3-update-pk-3.png)

Finally, we commit the changes:

![](https://15445.courses.cs.cmu.edu/fall2025/project4/img/4-3-update-pk-4.png)

That's all there is to it!

### 4.4 Serializable Verification

If a transaction runs in serializable isolation level, you will need to verify if it satisfies the serializability when committing the transaction. We use OCC backward validation for serializable verification. The verification method we talked about in the lecture only applies to a static database. In BusTub, you will need to consider newly-inserted and deleted records. To complete the serializable verification, you will need to store the scan filter (aka. scan predicate) in the transaction each time the sequential scan executor or the index scan executor are called. You will also need to track the write set correctly. With all the information, we can do serializable verification by checking if the scan predicate (read set) intersects with the write set of transactions that starts after the current transaction starts, as follows when we commit a transaction:

1. You do not need to verify a read-only transaction.
2. Collect all transactions that commits after the read timestamp of the current transaction. We call these “conflict transactions”.
3. Collect all RIDs that are modified by conflict transactions.
4. For each tuple, iterate through its version chain to verify if the current transaction reads any “phantom”. You can collect all undo logs up to the transaction read timestamp. Then, replay it one by one to check the intersection.
* For each update in the version chain,
* For **insert**, you should check if the new tuple satisfies any of the scan predicates of the current transaction. If yes, abort.
* For **delete**, you should check if the deleted tuple satisfies any of the scan predicates of the current transaction. If yes, abort.
* There is an edge case where a transaction inserts and then removes a tuple, which leaves a delete marker in the table heap. This should be regarded as a no-op instead of a delete.
* For **update**, you should check both the “before image” and the “after image”. If any of them overlaps with any of the scan predicates of the current transaction, abort.
* Consider the case that a transaction modifies a tuple but then reverts it back, which leaves an undo log that updates some columns to the same value. In this case, you should still process it as an identical update instead of ignoring it, and abort the transaction if necessary.
* However, if there are two transactions, where the first one modifies the value from X to Y, and then, the second one, Y to X, you should still detect the conflicts that X is changed, if there is a txn3 starting before txn1 starts and committing after txn2 commits.


5. If a transaction needs to be aborted in the commit phase, you should directly go through the abort logic to revert the changes, and set the transaction status to `ABORTED` instead of `TAINTED`.

This verification method is inefficient because (1) only one transaction can enter the verification process (2) we loop over all write sets of possible-conflicting transactions and evaluate scan predicates on that. You may consider implementing parallel verification, or precision locking (attribute-level checking instead of checking the record), in leaderboard tests.

To test your implementation using BusTub shell,

```bash
./bin/bustub-shell
bustub> set global_isolation_level=serializable;

```

For BusTub Netcat shell,

```bash
./bin/bustub-nc-shell --serializable

```

---

## Leaderboard Benchmark - T-NET, the Terrier NFT Exchange Network

In a galaxy far, far away, there is a universe in which Jack Russell terriers live in a highly-civilized society. We say that the society is highly civilized, except that NFTs (non-fungible tokens) are becoming increasingly popular. One day, the terriers decide to find a database system to track their NFTs, and BusTub is one of their candidate systems.

### Benchmark #1 - Token Transfer over T-NET / Snapshot Isolation

Terriers transfer their NFTs over T-NET. T-NET works like bank transfers: one terrier can initiate a transfer of a number of NFTs to another terrier. For this scenario, the transactions will be running in snapshot isolation mode.

```sql
CREATE TABLE terriers(terrier int primary key, token int);
-- each transaction: transfer A tokens from X to Y
UPDATE terriers SET token = token + A WHERE terrier = X;
UPDATE terriers SET token = token - A WHERE terrier = Y;

```

### Benchmark #2 - Trading-Network over T-NET / Serializable

When transferring NFTs on T-NET, terriers will be charged for transfer fees. The transfer fees will be waived if two terriers are on the same trading network. The network is represented by an integer ID.

```sql
CREATE TABLE terriers(terrier int primary key, token int, network int);
-- each transaction: transfer A tokens from X to Y
X_network = SELECT network FROM terriers WHERE terrier = X;
Y_network = SELECT network FROM terriers WHERE terrier = Y;
UPDATE terriers SET token = token + A * 0.97 WHERE terrier = X; -- if X_network != Y_network
UPDATE terriers SET token = token + A WHERE terrier = X; -- if X_network == Y_network
UPDATE terriers SET token = token - A WHERE terrier = Y;

```

At the same time, terriers can invite others to join their network with a sign-on bonus:

```sql
-- X invites Y to join the network
A = SELECT network FROM terriers WHERE terrier = X;
UPDATE terriers SET network = A, token = token + 1000 WHERE terrier = Y;

```

Terriers can also start their own network with a network registration fee.

```sql
-- X starts a new trading network
UPDATE terriers SET network = ?, token = token - 1000 WHERE terrier = X;

```

All transactions in this benchmark will run at serializable level.

Due to how T-NET works, it is possible that a terrier can own a negative amount of NFTs.

You might need to implement a more fine-grained garbage collection when sequential scan is running or on transaction commit / abort. The leaderboard test will not call the stop-the-world garbage collector you have implemented in Task 3. Some of our test cases need to access `commit_ts` after commit, and therefore you can clear the undo buffer instead of removing the transaction from the map when doing fine-grained garbage collection instead of removing it as in stop-the-world garbage collection.

Implementing a more efficient serializable verification (i.e., precision locking) might be helpful in leaderboard benchmarks. It might also be helpful to implement parallel serializable verification.

You will be ranked on speed of transfers and space usage of the database system respectively. The speed of transfers is measured by the throughput of the system, and the space usage is measured by the total number of rows in table tuples and undo logs in the system. There will be a background thread collecting number of rows in the system periodically, and the space usage is computed with the maximum number of rows at any time throughout the benchmark. The final leaderboard bonus score will be computed as: `min{speed_rank_bonus+space_rank_bonus, leaderboard_maximum_bonus}`. For each ranking, you will get 25 points for the 1st place, 15 points for 2nd-10th place, and 5 points for 11th-20th place.


## Instructions

### Formatting

Your code must follow the Google C++ Style Guide. We use Clang to automatically check the quality of your source code. Your project grade will be zero if your submission fails any of these checks.

Execute the following commands to check your syntax. The `format` target will automatically correct your code. The `check-lint` and `check-clang-tidy-p4` targets will print errors and instruct you how to fix it to conform to our style guide.

```bash
$ make format
$ make check-lint
$ make check-clang-tidy-p4

```

### Memory Leaks

For this project, we use LLVM Address Sanitizer (ASAN) and Leak Sanitizer (LSAN) to check for memory errors. To enable ASAN and LSAN, configure CMake in debug mode and run tests as you normally would. If there is memory error, you will see a memory error report. Note that macOS only supports address sanitizer without leak sanitizer.

In some cases, address sanitizer might affect the usability of the debugger. In this case, you might need to disable all sanitizers by configuring the CMake project with:

```bash
$ cmake -DCMAKE_BUILD_TYPE=Debug -DBUSTUB_SANITIZER= ..

```

### Development Hints

* You can use `BUSTUB_ASSERT` for assertions in debug mode. The statements within `BUSTUB_ASSERT` will NOT be executed in release mode. If you have something to assert in all cases, use `BUSTUB_ENSURE` instead.
* We encourage you to use a graphical debugger to debug your project if you are having problems.
* If you are having compilation problems, running `make clean` does not completely reset the compilation process. You will need to delete your build directory and run `cmake ..` again before you rerun `make`.
* Post all of your questions about this project on Piazza. Do not email the TAs directly with questions.

