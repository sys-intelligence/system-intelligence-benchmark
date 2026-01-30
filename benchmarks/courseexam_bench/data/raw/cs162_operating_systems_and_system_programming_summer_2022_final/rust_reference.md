# Reference Sheet

## Rust Reference Sheet

/*********************************** Options ***********************************/

```rust
pub enum Option<T> {
    None,
    Some(T),
}
impl<T> Option<T> {
    pub const fn is_some(&self) -> bool;
    pub const fn is_none(&self) -> bool;
    pub const fn as_ref(&self) -> Option<&T>;
    pub fn as_mut(&mut self) -> Option<&mut T>;
    pub fn cloned(self) -> Option<T> where T: Clone;
    pub fn unwrap(self) -> T;
    pub fn map<U, F>(self, f: F) -> Option<U> where F: FnOnce(T) -> U;
    pub fn take(&mut self) -> Option<T>;
}
```

/*********************************** Results ***********************************/

```rust
pub enum Result<T, E> {
    Ok(T),
    Err(E),
}
impl<T, E> Result<T, E> {
    pub const fn is_ok(&self) -> bool;
    pub const fn is_err(&self) -> bool;
    pub fn ok(self) -> Option<T>;
    pub fn err(self) -> Option<E>;
    pub fn unwrap(self) -> T where E: Debug;
    pub fn map<U, F>(self, op: F) -> Result<U, E> where F: FnOnce(T) -> U;
    pub fn map_err<F, O>(self, op: O) -> Result<T, F> where O: FnOnce(E) -> F;
}
```

/*********************************** Collections ***********************************/

```rust
impl<T> Vec<T, Global> {
pub const fn new() -> Vec<T, Global>;
}
impl<T, A> Vec<T, A> where A: Allocator {
    pub fn clear(&mut self);
    pub fn push(&mut self, value: T);
    pub fn pop(&mut self) -> Option<T>;
    pub fn insert(&mut self, index: usize, element: T);
    pub fn len(&self) -> usize;
    pub fn remove(&mut self, index: usize) -> T;
}
impl<K, V> HashMap<K, V, RandomState> {
    pub fn new() -> HashMap<K, V, RandomState>;
    pub fn clear(&mut self);
    pub fn contains_key<Q: ?Sized>(&self, k: &Q) -> bool where K: Borrow<Q>, Q: Hash + Eq;
    pub fn get<Q: ?Sized>(&self, k: &Q) -> Option<&V> where K: Borrow<Q>, Q: Hash + Eq;
    pub fn get_mut<Q: ?Sized>(&mut self, k: &Q) -> Option<&mut V> where K: Borrow<Q>, Q: Hash + Eq;
    pub fn insert(&mut self, k: K, v: V) -> Option<V>;
    pub fn len(&self) -> usize;
}
```

/*********************************** Miscellaneous ***********************************/

```rust
impl<T> Arc<T> {
    pub fn new(data: T) -> Arc<T>;
}
impl<T> Deref for Arc<T> where T: ?Sized { type Target = T; ... }
impl<T> Clone for Arc<T> where T: ?Sized;
impl<T: ?Sized> RwLock<T> {
    pub fn new(value: T) -> RwLock<T> where T: Sized;
    pub async fn read(&self) -> RwLockReadGuard<'_, T>;
    pub async fn write(&self) -> RwLockWriteGuard<'_, T>;
}
impl<T: ?Sized> Deref for RwLockReadGuard<'_, T> { type Target = T; ... }
impl<T: ?Sized> Deref for RwLockWriteGuard<'_, T> { type Target = T; ... }
impl<T: ?Sized> DerefMut for RwLockWriteGuard<'_, T> { ... }
pub fn drop<T>(_x: T);
println!("Hello, {}!", "world");
pub trait Clone {
    fn clone(&self) -> Self;
    fn clone_from(&mut self, source: &Self) { ... }
}
```

## Rust Examples

```rust
//! Examples of Rust syntax.
//! This code compiles, but doesn't do anything useful.
//! Running this code does not produce any panics.
use std::{collections::HashMap, sync::Arc};

use tokio::sync::RwLock;

struct Coordinate {
    x: i32,
    y: i32,
}
enum OperatingSystem {
    Mac,
    Windows,
    Linux,
    Other(String),
}

impl Coordinate {
    fn add(&mut self, other: Self) {
        self.x += other.x;
        self.y += other.y;
    }
}
#[tokio::main]
async fn main() {
    let mut x: i32 = 4;
    x += 1;

    let ptr = &mut x;
    *ptr += 1;

    assert_eq!(x, 6);

    let x = 123;
    let mut pt = Coordinate { x, y: 3 };
    assert_eq!(pt.x, 123);
    pt.add(Coordinate { x: 5, y: pt.y });

    assert_eq!(square(4), 16);

    let mut courses = vec!["161".to_string(), "162".to_string(), "164".to_string()];
    // Iterate by reference
    for course in courses.iter() {
        let tmp: &str = course;
        println!("Course: {}", tmp);
    }
    courses.push(String::from("169"));

    let mut map = HashMap::new();

    let mut first_num = None;

    // Transfer ownership of the entries in `courses`
    for course in courses {
        let num: i32 = course.parse().unwrap();
        if first_num.is_none() {
            first_num = Some(num);
        }
        map.insert(course, num);
    }

    match first_num {
        Some(num) => println!("First num: {}", num),
        None => println!("None"),
    }

    let cs161 = map.get("161").copied().unwrap_or(0);
    assert_eq!(cs161, 161);

    let my_os = OperatingSystem::Other(String::from("Redox"));
    if let OperatingSystem::Other(os) = my_os {
        map.insert(os, 162162);
    } else {
        println!("Someone has a common OS.");
    }

    let my_os = OperatingSystem::Mac;
    let name: &str = match my_os {
        OperatingSystem::Mac => "Mac",
        OperatingSystem::Linux => "Linux",
        _ => "Windows/Other",
    };

    let state = Arc::new(RwLock::new(Coordinate { x: 2, y: 5 }));

    // Multiple readers can immutably access the data at the same time
    let r1 = state.read().await;
    let r2 = state.read().await;

    println!("x = {}, y = {}", r2.x, r2.y);

    // Release the lock by dropping the guards
    drop(r1);
    drop(r2);

    let mut w1 = state.write().await;
    w1.x += 6;
    assert_eq!(w1.x, 8);
    drop(w1);
}


fn square(x: i32) -> i32 {
    x * x
}
```
