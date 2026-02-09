# Phase 3

**YOU ARE ONLY ALLOWED TO MODIFY OR ADD FILES IN THE src DIRECTORY.** 

## Overview

In this project, you will implement the components that allow BusTub to execute queries. You will create the operator executors that execute SQL queries and implement optimizer rules to transform query plans.

This project is composed of several tasks:

* **Task #1: Access Method Executors**
* **Task #2: Aggregation and Join Executors**
* **Task #3: HashJoin Executor and Optimization**
* **Task #4: External Merge Sort + Limit Executors + Window Functions**
* **Optional Leaderboard Task**

This project must be completed individually (i.e., no groups). Before starting, run `git pull public master` to pull the latest code from the public BusTub repo.

---

## Background

Please read this section carefully because you will need to construct your own SQL queries to test your executor implementation. You can also use the bustub shell to understand:

* Use `EXPLAIN` or `EXPLAIN (o)` to show raw and optimized plans
* Understand parameters in plan nodes (i.e., what the first and second 0 means in `#0.0`)
* Read a few simple plan node implementations in `include/execution/plans/`
* Pay attention to various expression types in `include/execution/expressions/`

### Introduction

BusTub's architecture is as follows:

In the public BusTub repository, we provide a full query processing layer. You can use the BusTub shell to execute SQL queries, much like in other database systems. Use the following command to compile and run the BusTub shell:

```bash
cd build && make -j$(nproc) shell
./bin/bustub-shell

```

You can also use **BusTub Web Shell** to run the examples below. It is a complete reference solution of the system running in your browser!

Within the shell, you can use `\dt` to view all tables. By default, the BusTub shell will automatically create three tables that are pre-populated with data. This is provided as a convenience so that you do not need to load data every time you rebuild your solution. Changes to these tables will not be persisted when you restart the DBMS.

```text
bustub> \dt
+-----+----------------+------------------------------+
| oid | name           | cols                         |
+-----+----------------+------------------------------+
| 0   | __mock_table_1 | (colA:INTEGER, colB:INTEGER) |
| 1   | __mock_table_2 | (colC:VARCHAR, colD:VARCHAR) |
| 2   | __mock_table_3 | (colE:INTEGER, colF:VARCHAR) |
| ... | ...            | ...                          |
+-----+----------------+------------------------------+

```

You can view all data from a table by using the `SELECT` statement:

```text
bustub> SELECT * FROM __mock_table_1;
+---------------------+---------------------+
| __mock_table_1.colA | __mock_table_1.colB |
+---------------------+---------------------+
| 0                   | 0                   |
| 1                   | 100                 |
| 2                   | 200                 |
| 3                   | 300                 |
| 4                   | 400                 |
| 5                   | 500                 |
| ...                 | ...                 |
+---------------------+---------------------+

```

**Please note:**

* BusTub only supports a small subset of SQL. Don't be surprised if it does not work with some SQL queries. For all SQL queries supported in BusTub, refer to the SQLLogicTest files in `tests/sql`.
* If you are using CLion to run the BusTub shell, please add a `--disable-tty` parameter to the shell, so that it works correctly in the CLion terminal.
* Always end your statement with `;` (except internal commands).
* BusTub only supports `INT` and `VARCHAR(n)` type. Also you should use single quotes for strings, e.g., `INSERT INTO table VALUES ('a')`.

### Inspecting SQL Query Plans

BusTub supports the `EXPLAIN` command to print a query's execution plan. You can add `EXPLAIN` in front of any query. For example:

```text
bustub> EXPLAIN SELECT * FROM __mock_table_1;
=== BINDER ===
BoundSelect {
  table=BoundBaseTableRef { table=__mock_table_1, oid=0 },
  columns=[__mock_table_1.colA, __mock_table_1.colB],
  groupBy=[],
  having=,
  where=,
  limit=,
  offset=,
  order_by=[],
  is_distinct=false,
}
=== PLANNER ===
Projection { exprs=[#0.0, #0.1] } | (__mock_table_1.colA:INTEGER, __mock_table_1.colB:INTEGER)
MockScan { table=__mock_table_1 } | (__mock_table_1.colA:INTEGER, __mock_table_1.colB:INTEGER)
=== OPTIMIZER ===
MockScan { table=__mock_table_1 } | (__mock_table_1.colA:INTEGER, __mock_table_1.colB:INTEGER)

```

The result of `EXPLAIN` provides an overview of the transformation process within the query processing layer. The statement is first processed by the parser and the binder, which produces an abstract syntax tree (AST) representing the query. In this example, the query is represented by a `BoundSelect` on `__mock_table_1` that will retrieve two columns (`colA` and `colB`). Note that the binder automatically expands the `*` character from the original SQL query into the actual columns in the table.

Next, the binder AST is processed by the planner, which will produce an appropriate query plan. In this case, the query plan is a tree of two nodes, with data flowing from the leaves to the root:

After that, the optimizer will optimize the query plan. In this case, it removes the projection because it is redundant.

Let's consider a more complex example:

```text
bustub> EXPLAIN (o) SELECT colA, MAX(colB) FROM
  (SELECT * FROM __mock_table_1, __mock_table_3 WHERE colA = colE) GROUP BY colA;
=== OPTIMIZER ===
Agg { types=[max], aggregates=[#0.1], group_by=[#0.0] }
  NestedLoopJoin { type=Inner, predicate=(#0.0=#1.0) }
    MockScan { table=__mock_table_1 }
    MockScan { table=__mock_table_3 }

```

For this example, the optimized query plan is:

In this project, you will need to construct SQL queries to test each of your executor's implementations. `EXPLAIN` is extremely helpful for you to know if a SQL query is using a specific executor.

---

## Sample Executors

In the BusTub public repository, we provide several sample executor implementations.

### Projection

A projection node can represent various computations on its input. It will always have exactly one child node. In the BusTub shell, inspect the query plans for the following queries:

* `EXPLAIN SELECT 1 + 2;`
* `EXPLAIN SELECT colA FROM __mock_table_1;`
* `EXPLAIN SELECT colA + colB AS a, 1 + 2 AS b FROM __mock_table_1;`

A projection plan node consists of one or more expressions representing a computation:

* **ColumnValueExpression**: directly places a column of the child executor to the output. The syntax `#0.0` means the first column in the first child. You will see something like `#0.0 = #1.0` in a plan for joins.
* **ConstantExpression**: represents a constant value (e.g., 1).
* **ArithmeticExpression**: a tree representing an arithmetic computation. For example, `1 + 2` would be represented by an `ArithmeticExpression` with two `ConstantExpression` (1 and 2) as children.

### Filter

A filter plan node is used to filter the output of a child given a predicate. For example:
`EXPLAIN SELECT * FROM __mock_table_1 WHERE colA > 1;`
A filter node has exactly one child and contains a predicate.

### Values

A values plan node is used to directly produce values:

* `EXPLAIN values (1, 2, 'a'), (3, 4, 'b');`
* `CREATE TABLE table1(v1 INT, v2 INT, v3 VARCHAR(128));`
* `EXPLAIN INSERT INTO table1 VALUES (1, 2, 'a'), (3, 4, 'b');`
Values plan nodes are useful when inserting user-supplied values into a table.

### Query Plan Syntax

As you might have noticed, `EXPLAIN` produces a string of column descriptions after each plan node. That's the output schema of the node. Consider this example output:
`Projection { exprs=[#0.0, #0.1] } | (__mock_table_1.colA:INTEGER, __mock_table_1.colB:INTEGER)`
This indicates that the executor representing this plan node will produce two columns, both of integer types. The output schema is inferred within the planner. For this project, your executor implementations must produce tuples with schema exactly as specified in the plan node, or they will fail our unit tests.

---

## Project Specification

In this project, you will add new operator executors and query optimizations to BusTub. BusTub uses the row-based vectorization query processing model, in which every executor implements a `Next` function to get the next tuple batch result of max `BUSTUB_BATCH_SIZE` tuples. When the DBMS invokes an executor's `Next` function, the executor returns either (1) a batch of some tuples or (2) an indicator that there are no more tuples. With this approach, each executor implements a loop that continues calling `Next` on its children to retrieve tuples and process them batch by batch.

In BusTub's implementation of the vectorization model, the `Next` function for each executor returns a batch of record identifiers (RID) in addition to a batch of tuples. A record identifier serves as a unique identifier for a tuple.

The executors are created from an execution plan in `src/execution/executor_factory.cpp`.

All test cases in this project are written in a special file format called SQLLogicTest (derived from SQLite). You can find how to use it at the end of this page.

---

## Task #1 - Access Method Executors

In the background section above, we saw that the BusTub can already retrieve data from mock tables in `SELECT` queries. This is implemented without real tables by using a `MockScan` executor to always generate the same tuples using a predefined algorithm. This is why you cannot update these tables.

In this task, you will implement executors that read from and write to tables in the storage system. You will complete your implementation in the following files:

* `src/include/execution/executors/seq_scan_executor.h`
* `src/execution/seq_scan_executor.cpp`
* `src/include/execution/executors/insert_executor.h`
* `src/execution/insert_executor.cpp`
* `src/include/execution/executors/update_executor.h`
* `src/execution/update_executor.cpp`
* `src/include/execution/executors/delete_executor.h`
* `src/execution/delete_executor.cpp`
* `src/include/execution/executors/index_scan_executor.h`
* `src/execution/index_scan_executor.cpp`
* `src/optimizer/seqscan_as_indexscan.cpp`

Each of these executors is described below.

### SeqScan

The `SeqScanPlanNode` can be planned with a `SELECT * FROM table` statement.

```text
bustub> CREATE TABLE t1(v1 INT, v2 VARCHAR(100));
Table created with id = 15
bustub> EXPLAIN (o,s) SELECT * FROM t1;
=== OPTIMIZER ===
SeqScan { table=t1 } | (t1.v1:INTEGER, t1.v2:VARCHAR)

```

The `SeqScanExecutor` iterates over a table and returns its tuples one batch at a time.

**Hint:** Make sure that you understand the difference between the pre-increment and post-increment operators when using the `TableIterator` object. (Check [here](https://en.cppreference.com/w/cpp/language/operator_incdec) for a quick refresher.)

**Hint:** Do not emit tuples that are deleted in the `TableHeap`. Check the `is_deleted_` field of the corresponding `TupleMeta` for each tuple.

**Hint:** The output of sequential scan is a copy of each matched tuple and its original record identifier (RID).

**Note:** BusTub does not support `DROP TABLE` or `DROP INDEX`. You can reset your database by restarting the shell.

### Insert

The `InsertPlanNode` can be planned with an `INSERT` statement. Note that you will need to use a single quote to specify a `VARCHAR` value.

```text
bustub> EXPLAIN (o,s) INSERT INTO t1 VALUES (1, 'a'), (2, 'b');
=== OPTIMIZER ===
Insert { table_oid=15 } | (__bustub_internal.insert_rows:INTEGER)
  Values { rows=2 } | (__values#0.0:INTEGER, __values#0.1:VARCHAR)

```

The `InsertExecutor` inserts tuples into a table and updates any affected indexes. It has exactly one child producing values to be inserted into the table. The planner will ensure that the values have the same schema as the table. The executor will produce a single tuple of integer type as the output, indicating how many rows have been inserted into the table. Remember to update indexes when inserting into the table, if there are indexes associated with it.

**Hint:** See the **System Catalog** section below for information about the system catalog. To initialize this executor, you will need to look up information about the table being inserted into.

**Hint:** See the **Index Updates** section below for further details about updating a table's indexes.

**Hint:** You will need to use the `TableHeap` class to perform table modifications.

### Update

The `UpdatePlanNode` can be planned with an `UPDATE` statement. It has exactly one child with the records to be updated in the table.

```text
bustub> explain (o,s) update test_1 set colB = 15445;
=== OPTIMIZER ===
Update { table_oid=20, target_exprs=[#0.0, 15445, #0.2, #0.3] } | (__bustub_internal.update_rows:INTEGER)
  SeqScan { table=test_1 } | (test_1.colA:INTEGER, test_1.colB:INTEGER, test_1.colC:INTEGER, test_1.colD:INTEGER)

```

The `UpdateExecutor` modifies existing tuples in a specified table. The executor will produce a single tuple of integer type as the output, indicating how many rows have been updated. Remember to update any indexes affected by the updates.

**Hint:** To implement an update, first delete the affected tuple and then insert a new tuple.

### Delete

The `DeletePlanNode` can be planned with a `DELETE` statement. It has exactly one child with the records to be deleted from the table. Your delete executor should produce an integer output that represents the number of rows that it deleted from the table. It will also need to update any affected indexes.

```text
bustub> EXPLAIN (o,s) DELETE FROM t1;
=== OPTIMIZER ===
Delete { table_oid=15 } | (__bustub_internal.delete_rows:INTEGER)
  Filter { predicate=true } | (t1.v1:INTEGER, t1.v2:VARCHAR)
    SeqScan { table=t1 } | (t1.v1:INTEGER, t1.v2:VARCHAR)

bustub> EXPLAIN (o,s) DELETE FROM t1 where v1 = 1;
=== OPTIMIZER ===
Delete { table_oid=15 } | (__bustub_internal.delete_rows:INTEGER)
  Filter { predicate=#0.0=1 } | (t1.v1:INTEGER, t1.v2:VARCHAR)
    SeqScan { table=t1 } | (t1.v1:INTEGER, t1.v2:VARCHAR)

```

You may assume that the `DeleteExecutor` is always at the root of the query plan in which it appears. The `DeleteExecutor` should not modify its result set.

**Hint:** To delete a tuple, you need to get a RID from the child executor and update the `is_deleted_` field of the corresponding `TupleMeta` for that tuple.

### IndexScan

The `IndexScanExecutor` does point lookup and ordered scan using the b-plus tree index to retrieve tuples in the table. The executor should be able to support several point lookups on the same index.

You will need to implement the index scan by supporting the following two types of queries:

1. **Point Lookup**: `SELECT FROM <table> WHERE <index column> = <val>`. You will implement the optimizer rule to transform a `SeqScan` into an `IndexScan` in the next section.
2. **Ordered Scan**: `SELECT FROM <table> ORDER BY <index column>`. The optimizer rule to generate an `IndexScan` for queries with `ORDER BY` on an index column has been implemented for you. Your task is to handle ASC (or default) ordering only in `IndexScan`.

```text
bustub> CREATE TABLE t1(v1 int, v2 int);
Table created with id = 22

bustub> CREATE INDEX t1v1 ON t1(v1);
Index created with id = 0

bustub> EXPLAIN (o,s) SELECT * FROM t1 WHERE v1 = 1;
=== OPTIMIZER ===
IndexScan { index_oid=0, filter=(#0.0=1) } | (t1.v1:INTEGER, t1.v2:INTEGER)

bustub> EXPLAIN (o,s) SELECT * FROM t1 ORDER BY v1;
=== OPTIMIZER ===
IndexScan { index_oid=0 } | (t1.v1:INTEGER, t1.v2:INTEGER)

```

The type of the index object in the plan will always be `BPlusTreeIndexForTwoIntegerColumn` in this project. You can safely cast the object to this type and store it in the executor wherever needed:
`tree_ = dynamic_cast<BPlusTreeIndexForTwoIntegerColumn *>(index_info_->index_.get())`

You can then do point lookup or ordered scan with the b-plus tree index and emit the satisfying tuple. In this semester, you only need to support the index on a single, unique integer column. Our test cases will not contain duplicate keys. Hence, this executor returns one tuple per point lookup if it exists.

You will need to finish the optimizer rule in the next section to transform a `SeqScan` into an `IndexScan`. It may make more sense to implement the optimizer rule before implementing `IndexScan` to understand the kind of queries `IndexScanExecutor` will need to support.

**Hint:** We will never insert duplicate rows into tables with indexes.
**Hint:** As above, do not emit tuples that are deleted.
**Hint:** Please use `ScanKey` for the point lookup, and use Index Iterator for the ordered scan.

### Optimizing SeqScan to IndexScan

As we learned in lecture, when we are querying on the indexed column, using an `IndexScan` will significantly boost the lookup performance. To this end, we need to push down the filter into the scanner so that we know the key to lookup in the index. Then we can directly retrieve the value over the index, instead of doing a full table scan.

You would need to modify the optimizer to transform a `SeqScanPlanNode` into a `IndexScanPlanNode` when it is possible.

Consider the following example:
`bustub> EXPLAIN (o) SELECT * FROM t1 WHERE v1 = 1;`
Without applying the `MergeFilterScan` and the `SeqScan as IndexScan` optimizer rule, the plan may look like the following:

```text
 Filter { predicate=(#0.0=1) } | (t1.v1:INTEGER, t1.v2:INTEGER, t1.v3:INTEGER)
   SeqScan { table=t1 } | (t1.v1:INTEGER, t1.v2:INTEGER, t1.v3:INTEGER)

```

After applying the `MergeFilterScan` and `SeqScan as IndexScan` optimizer rule, we can just do a quick index lookup instead of iterating the entire table. The resulting plan will look like the following:

```text
 IndexScan { index_oid=0, filter=(#0.0=1) } | (t1.v1:INTEGER, t1.v2:INTEGER, t1.v3:INTEGER)

```

Here's the brief steps to implement this optimizer rule:

* **Enable Predicate pushdown to SeqScan**: We can implement a predicate filter in `SeqScanExecutor` so that later the index scan node will have the predicate. We've already enabled `MergeFilterScan` optimizer rule `src/optimizer/merge_filter_scan.cpp` in the starter optimizer rules for you.
* **Use Index**: You can check the filtering columns from the predicate. If there happens to exist an index on this column, create an `IndexScanPlanNode`. Note that to get full score, you will need to support this optimizer rule in a few different situations: (1) when there's one equality test on the indexed column in predicate (i.e., `WHERE v1 = 1`) (2) when the indexed column ordering is flipped (i.e., `WHERE 1 = v1`) (3) when there are several point lookups on the same index (i.e., `WHERE v1 = 1 or v1 = 4`). Note that queries of the form `SELECT * FROM t1 WHERE v1 = 1 AND v2 = 2` should still use a seq scan, thus you do not need to split the predicates.

Please check **Optimizer Rule Implementation Guide** section for details on implementing an optimizer rule.

Now that you have implemented all storage related executors. In the following tasks, you can create tables and insert some values by yourself to test your own executor implementation! At this point, you should also have passed SQLLogicTests #1 to #6.

**Hint:** You may find the utility `BPlusTreeIndex::ScanKey` function helpful.
**Hint:** Think about how to handle queries of the form `WHERE v1 = 1 OR v1 = 1`. It may help to view `AggregateKey` in `/src/include/execution/plans/aggregation_plan.h`.
**Hint:** Please only optimize `SeqScan` to `IndexScan` in the 2 scenarios mentioned above (i.e. point lookup and ordered scan).

---

## Task #2 - Aggregation & Join Executors

You will complete your implementation in the following files:

* `src/include/execution/plans/aggregation_plan.h`
* `src/include/execution/executors/aggregation_executor.h`
* `src/execution/aggregation_executor.cpp`
* `src/include/execution/executors/nested_loop_join_executor.h`
* `src/execution/nested_loop_join_executor.cpp`
* `src/include/execution/executors/nested_index_join_executor.h`
* `src/execution/nested_index_join_executor.cpp`

### Aggregation

The `AggregationPlanNode` is used to support queries like the following:

* `EXPLAIN SELECT colA, MIN(colB) FROM __mock_table_1 GROUP BY colA;`
* `EXPLAIN SELECT COUNT(colA), min(colB) FROM __mock_table_1;`
* `EXPLAIN SELECT colA, MIN(colB) FROM __mock_table_1 GROUP BY colA HAVING MAX(colB) > 10;`
* `EXPLAIN SELECT DISTINCT colA, colB FROM __mock_table_1;`

The aggregation executor computes an aggregation function for each group of input. It has exactly one child. The output schema consists of the group-by columns followed by the aggregation columns.

As discussed in class, a common strategy for implementing aggregation is to use a hash table, with the group-by columns as the key. In this project, you may assume that the aggregation hash table fits in memory. This means that you do not need to implement a multi-stage, partition-based strategy, and the hash table does not need to be backed by buffer pool pages.

We provide a `SimpleAggregationHashTable` data structure that exposes an in-memory hash table (`std::unordered_map`) but with an interface designed for computing aggregations. This class also exposes an `SimpleAggregationHashTable::Iterator` type that can be used to iterate through the hash table. You will need to complete the `CombineAggregateValues` function for this class.

The aggregation executor itself will not need to handle the `HAVING` predicate. The planner will plan aggregations with a `HAVING` clause as an `AggregationPlanNode` followed by a `FilterPlanNode`.

**Hint:** In the context of a query plan, aggregations are pipeline breakers. This may influence the way that you use the `AggregationExecutor::Init()` and `AggregationExecutor::Next()` functions in your implementation. Carefully decide whether the build phase of the aggregation should be performed in `AggregationExecutor::Init()` or `AggregationExecutor::Next()`.
**Hint:** You must handle `NULL` values in the input of the aggregation functions. See test cases for expected behavior.
**Hint:** Group-by columns can also have `NULL` values. You may want to consider modifying the way aggregate keys are compared.
**Hint:** When performing aggregation on an empty table, `CountStarAggregate` should return zero and all other aggregate types should return `integer_null`.

### NestedLoopJoin

The DBMS will use `NestedLoopJoinPlanNode` for all join operations, by default.

* `EXPLAIN SELECT * FROM __mock_table_1, __mock_table_3 WHERE colA = colE;`
* `EXPLAIN SELECT * FROM __mock_table_1 INNER JOIN __mock_table_3 ON colA = colE;`
* `EXPLAIN SELECT * FROM __mock_table_1 LEFT OUTER JOIN __mock_table_3 ON colA = colE;`

You will need to implement an inner join and left join for the `NestedLoopJoinExecutor` using the simple nested loop join algorithm from class. The output schema of this operator is all columns from the left table followed by all columns from the right table. For each tuple in the outer table, consider each tuple in the inner table and emit the ones that satisfy the join predicate.

**Hint:** You should use the predicate in the `NestedLoopJoinPlanNode`. See `AbstractExpression::EvaluateJoin`. Note that this returns a `Value`, which could be false, true, or NULL.

### NestedIndexJoin

The DBMS will use `NestedIndexJoinPlanNode` if the query contains a join with an equi-condition and the right side of the join has an index over the condition.

```text
CREATE TABLE t1(v1 int, v2 int);
CREATE TABLE t2(v3 int, v4 int);
CREATE INDEX t2v3 on t2(v3);
EXPLAIN SELECT * FROM t1 INNER JOIN t2 ON v1 = v3;
=== PLANNER ===
Projection { exprs=[#0.0, #0.1, #0.2, #0.3] } | (t1.v1:INTEGER, t1.v2:INTEGER, t2.v3:INTEGER, t2.v4:INTEGER)
  NestedLoopJoin { predicate=#0.0=#1.0 } | (t1.v1:INTEGER, t1.v2:INTEGER, t2.v3:INTEGER, t2.v4:INTEGER)
    SeqScan { table=t1 } | (t1.v1:INTEGER, t1.v2:INTEGER)
    SeqScan { table=t2 } | (t2.v3:INTEGER, t2.v4:INTEGER)
=== OPTIMIZER ===
NestedIndexJoin { type=Inner, key_predicate=#0.0, index=t2v3, index_table=t2 } | (t1.v1:INTEGER, t1.v2:INTEGER, t2.v3:INTEGER, t2.v4:INTEGER)
  SeqScan { table=t1 } | (t1.v1:INTEGER, t1.v2:INTEGER)

```

In the plan phase, the query is planned as a `NestedLoopJoin` of two tables. The optimizer identifies that the right side of the join (`SeqScan t2`) has an index on column `v3`, and the join condition is an equi-condition `v1 = v3`.

The schema of `NestedIndexJoin` is all columns from the left table (child, outer) and then from the right table (index, inner). This executor will have only one child that propagates tuple batches corresponding to the outer table of the join. For each of these tuples, you will need to find the corresponding tuple in the inner table that matches the index key given by utilizing the index in the catalog.

**Hint:** You will want to fetch the tuple from the outer table, construct the index probe key by using `key_predicate`, and then look up the RID in the index to retrieve the corresponding tuple for the inner table.

We will provide all test cases on Gradescope AS-IS. At this point, you should pass SQLLogicTests - #7 to #13.

---

## Task #3 - HashJoin Executor and Optimization

You will complete your implementation in the following files:

* `src/include/storage/page/intermediate_result_page.h`
* `src/include/execution/executors/hash_join_executor.h`
* `src/execution/hash_join_executor.cpp`
* `src/optimizer/nlj_as_hash_join.cpp`

### HashJoin

The DBMS can use `HashJoinPlanNode` if a query contains a join with a conjunction of several equi-conditions between two columns.

You will need to implement the inner join and left join for `HashJoinExecutor` using the hash join algorithm from class. The output schema of this operator is all columns from the left table followed by all columns from the right table. It is possible that the probe hash table may NOT fit entirely in memory (assuming our memory can support hash table of up to 4KB tuples). So your implementation should follow the **Grace Hash Table** algorithm discussed in lecture.

You should design the page layout and implement the read/write methods for the `IntermediateResultPage`. It is recommended to first read Task 4 to decide if you want to use the same implementation for both tasks.

Your implementation should correctly handle hash collisions. Use `GetLeftJoinKey()` and `GetRightJoinKey()` in the `HashJoinPlanNode`.

**Hint:** Take a look at `SimpleAggregationHashTable` for hashing tuples with multiple attributes.
**Hint:** The build side of a hash join is a pipeline breaker.

### Optimizing NestedLoopJoin to HashJoin

Hash joins usually yield better performance than nested loop joins. You should modify the optimizer to transform a `NestedLoopJoinPlanNode` into a `HashJoinPlanNode` when possible (conjunction of equi-conditions connected by `AND`).

```text
bustub> EXPLAIN (o) SELECT * FROM test_1 t1, test_2 t2 WHERE t1.colA = t2.colA AND t1.colB = t2.colC;

```

Resulting plan:

```text
 HashJoin { type=Inner, left_key=[#0.0, #0.1], right_key=[#0.0, #0.2] } 
   SeqScan { table=test_1 }                                             
   SeqScan { table=test_2 } 

```

**Hint:** Check which table the column belongs to using `ColumnValueExpression::GetTupleIdx`.
**Hint:** Extract out keys recursively when dealing with multiple equi-conditions.

At this point, you should pass SQLLogicTests - #14 to #15.

---

## Task #4: External Merge Sort + Limit Executors + Window Functions

You will complete your implementation in the following files:

* `src/include/storage/page/intermediate_result_page.h`
* `src/execution/execution_common.cpp`
* `src/include/execution/executors/external_merge_sort_executor.h`
* `src/execution/external_merge_sort_executor.cpp`
* `src/include/execution/executors/limit_executor.h`
* `src/execution/limit_executor.cpp`
* `src/include/execution/executors/window_function_executor.h`
* `src/execution/window_function_executor.cpp`

### External Merge Sort

BusTub will use a `SortPlanNode` for all `ORDER BY` operators (unless it matches an index).
`EXPLAIN SELECT * FROM __mock_table_1 ORDER BY colA ASC, colB DESC NULLS FIRST;`

You must follow the **external merge sort** algorithm: store intermediate results in temporary pages and merge sort recursively. Assume sort keys are unique for this task (no ties) but support `NULL` values.

You are allowed to use `std::sort` to sort tuples fitting within one sort page, but **NOT** on all tuples. Your `IntermediateResultPage` layout should be compact. Pages must be deleted after the merge sort is done. We only test two-way merge sort.

**Hint:** Use the helper class `TupleComparator` in `execution_common.h`.
**Hint:** Use page guards to handle pinning/unpinning and evictability.

### Limit

The `LimitPlanNode` specifies the number of tuples that query will generate.
`EXPLAIN SELECT * FROM __mock_table_1 LIMIT 10;`
The `LimitExecutor` constrains the number of output tuples from its child executor.

### Window Functions

A window function conceptual model:

1. Split data based on `PARTITION BY`.
2. In each partition, sort by `ORDER BY`.
3. In each partition, iterate over each tuple and compute the function over the frame.

For this task, you do not need to handle window frames. You only need to implement `PARTITION BY` and `ORDER BY` clauses. BusTub ensures all window functions within a query have the same `ORDER BY` clauses.

Apart from aggregation functions, you will need to implement `RANK`.

---

## Additional Information

### System Catalog

`src/include/catalog/catalog.h`. Use `Catalog::GetTable()` and `Catalog::GetIndex()`.

### Index Updates

For `Insert`, `Update`, and `Delete`, modify all indexes for the table. Use `Catalog::GetTableIndexes()`.

### Optimizer Rule Implementation Guide

Optimizer rules construct optimized plans in a bottom-up way. Recursively apply rules to children before applying to the current node.

---

## Instructions

### Testing

```bash
make -j$(nproc) sqllogictest
./bin/bustub-sqllogictest ../test/sql/p3.00-primer.slt --verbose

```

### Formatting

```bash
make format
make check-lint
make check-clang-tidy-p3

```

### Memory Leaks

Use LLVM Address Sanitizer (ASAN) and Leak Sanitizer (LSAN). Configure CMake in debug mode.
