// ============================================
// SysMoBench Alloy Invariants for Spinlock
// ============================================
// These invariants are automatically appended to generated Alloy specifications
// to verify correctness properties.

// Invariant 1: Mutual Exclusion
// At most one thread can hold any lock at any time
assert INV_MutualExclusion {
  all s: State, l: Lock |
    lone s.lock_holder[l]
}

// Invariant 2: Lock-Status Consistency
// If a thread holds a lock, it must be in Locked status
assert INV_LockStatusConsistency {
  all s: State, l: Lock, th: Thread |
    th in s.lock_holder[l] implies s.thread_status[th] = Locked
}

// Invariant 3: Status Implies Lock
// If a thread is in Locked status, it must hold some lock
assert INV_StatusImpliesLock {
  all s: State, th: Thread |
    s.thread_status[th] = Locked implies
      some l: Lock | th in s.lock_holder[l]
}

// Invariant 4: No Duplicate Lock Holders
// A lock cannot be held by multiple threads
assert INV_NoDuplicateLockHolders {
  all s: State, l: Lock, th1, th2: Thread |
    (th1 in s.lock_holder[l] and th2 in s.lock_holder[l]) implies th1 = th2
}

// ============================================
// Verification Commands
// ============================================
// Check all invariants with the same scope as the original spec

check INV_MutualExclusion for 10 Time, 2 Thread, 1 Lock, 10 State
check INV_LockStatusConsistency for 10 Time, 2 Thread, 1 Lock, 10 State
check INV_StatusImpliesLock for 10 Time, 2 Thread, 1 Lock, 10 State
check INV_NoDuplicateLockHolders for 10 Time, 2 Thread, 1 Lock, 10 State
