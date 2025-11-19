package edu.uchicago.cs.systems.wasabi;

import java.util.ArrayList;
import edu.uchicago.cs.systems.wasabi.StackSnapshot;
import edu.uchicago.cs.systems.wasabi.ExecutionTrace;

import static org.junit.Assert.*;
import org.junit.Test;

public class TestExecutionTrace {
  
  @Test
  public void testIsSameOpEntry() {
    OpEntry testOpA = new OpEntry(
        "baz(Baz.java:42)",
        OpEntry.RETRY_CALLER_OP,
        0L,
        new StackSnapshot( 
          new ArrayList() {
            {
              add("baz(Baz.java:42)");
              add("bar(Bar.java:42)"); 
              add("foo(Foo.java:42)"); 
            }
          }
        ),
        "IOException"
      );
    OpEntry testOpB = new OpEntry(
        "baz(Baz.java:42)",
        OpEntry.RETRY_CALLER_OP,
        0L,
        new StackSnapshot( 
          new ArrayList() {
            {
              add("baz(Baz.java:42)");
              add("bar(Bar.java:42)"); 
              add("foo(Foo.java:42)"); 
            }
          }
        ),
        "RuntimeException"
      );

    assertTrue(testOpA.isSameOp(testOpA));
    assertFalse(testOpA.isSameOp(testOpB));
  }

  @Test
  public void testHasFrame() {
    OpEntry testOp = new OpEntry(
        "baz(Baz.java:42)",
        OpEntry.RETRY_CALLER_OP,
        0L,
        new StackSnapshot( 
          new ArrayList() {
            {
              add("baz(Baz.java:42)");
              add("bar(Bar.java:42)"); 
              add("foo(Foo.java:42)"); 
            }
          }
        ),
        "Exception"
      );

    assertTrue(testOp.hasFrame("bar(Bar.java:42)"));
    assertFalse(testOp.hasFrame("not-a-frame"));
  }

  @Test
  public void testIsOfType() {
    OpEntry testOp = new OpEntry(
        "foo(Foo.java:42)",
        OpEntry.RETRY_CALLER_OP,
        0L,
        new StackSnapshot( 
          new ArrayList() {
            {
              add("foo(Foo.java:42)"); 
            }
          }
        ),
        "Exception"
      );

    assertTrue(testOp.isOfType(OpEntry.RETRY_CALLER_OP));
    assertFalse(testOp.isOfType(OpEntry.THREAD_SLEEP_OP));
  }

  @Test
  public void testIsNullOrEmpty() {
    ExecutionTrace execTrace = new ExecutionTrace();
    assertTrue(execTrace.isNullOrEmpty());
  }

  @Test
  public void testCheckIfOpIsOfType() {
    ExecutionTrace execTrace = new ExecutionTrace();
    execTrace.addLast(
        new OpEntry(
            "foo(Foo.java:42)",
            OpEntry.RETRY_CALLER_OP,
            0L,
            new StackSnapshot( 
              new ArrayList() {
                {
                  add("foo(Foo.java:42)"); 
                }
              }
            ),
            "Exception"
          )
      );

    assertEquals(execTrace.getSize(), 1);
    assertTrue(execTrace.checkIfOpIsOfType(0, OpEntry.RETRY_CALLER_OP));
    assertFalse(execTrace.checkIfOpIsOfType(1, OpEntry.RETRY_CALLER_OP));
    assertFalse(execTrace.checkIfOpIsOfType(0, OpEntry.THREAD_SLEEP_OP));
  }

  @Test
  public void testCheckIfOpHasFrame() {
    ExecutionTrace execTrace = new ExecutionTrace();
    execTrace.addLast(
        new OpEntry(
            "foo(Foo.java:42)",
            OpEntry.RETRY_CALLER_OP,
            0L,
            new StackSnapshot( 
              new ArrayList() {
                {
                  add("foo(Foo.java:42)"); 
                }
              }
            ),
            "Exception"
          )
      );

    assertEquals(execTrace.getSize(), 1);
    assertTrue(execTrace.checkIfOpHasFrame(0, "foo(Foo.java:42)"));
    assertFalse(execTrace.checkIfOpHasFrame(1, "foo(Foo.java:42)"));
    assertFalse(execTrace.checkIfOpHasFrame(0, "not-a-frame"));
  }
  
  @Test
  public void testCheckIfOpsAreEqual() {
    ExecutionTrace execTrace = new ExecutionTrace();
    execTrace.addLast(
        new OpEntry(
            "foo(Foo.java:42)",
            OpEntry.RETRY_CALLER_OP,
            0L,
            new StackSnapshot( 
              new ArrayList() {
                {
                  add("foo(Foo.java:42)"); 
                }
              }
            ),
            "Exception"
          )
      );
    execTrace.addLast(
        new OpEntry(
            "Thread.sleep(Bar.java:43)",
            OpEntry.THREAD_SLEEP_OP,
            0L,
            new StackSnapshot( 
              new ArrayList() {
                {
                  add("Thread.sleep(Bar.java:43)");
                  add("bar(Bar.java:42)"); 
                }
              }
            ),
            null
          )
      );
    execTrace.addLast(
        new OpEntry(
            "foo(Foo.java:42)",
            OpEntry.RETRY_CALLER_OP,
            0L,
            new StackSnapshot( 
              new ArrayList() {
                {
                  add("foo(Foo.java:42)"); 
                }
              }
            ),
            "Exception"
          )
      );

    assertEquals(execTrace.getSize(), 3);
    assertTrue(execTrace.checkIfOpsAreEqual(0, 2));
    assertFalse(execTrace.checkIfOpsAreEqual(1, 2));
  }

  @Test
  public void testMaxOpCacheSize() {
    int maxOpCacheSize = 50;
    ExecutionTrace execTrace = new ExecutionTrace(maxOpCacheSize);
    execTrace.addLast(
        new OpEntry(
            "foo(Foo.java:42)",
            OpEntry.RETRY_CALLER_OP,
            0L,
            new StackSnapshot( 
              new ArrayList() {
                {
                  add("foo(Foo.java:42)"); 
                }
              }
            ),
            "Exception"
          )
      );
    for (int i = 1; i < maxOpCacheSize; ++i) {
      execTrace.addLast(
          new OpEntry(
              "bar(Bar.java:42)",
              OpEntry.RETRY_CALLER_OP,
              0L,
              new StackSnapshot( 
                new ArrayList() { 
                  {
                    add("bar(Bar.java:42)"); 
                  }
                }
              ),
              "Exception"
            )
        );
    }

    assertEquals(execTrace.getSize(), maxOpCacheSize);
    assertTrue(execTrace.checkIfOpHasFrame(0, "foo(Foo.java:42)"));

    execTrace.addLast(
      new OpEntry(
          "bar(Bar.java:42)",
          OpEntry.RETRY_CALLER_OP,
          0L,
          new StackSnapshot( 
              new ArrayList() {
              {
                add("bar(Bar.java:42)"); 
              }
            }
          ),
          "Exception"
        )
    );
    
    assertEquals(execTrace.getSize(), maxOpCacheSize);
    assertTrue(execTrace.checkIfOpHasFrame(0, "bar(Bar.java:42)"));
  }
}
