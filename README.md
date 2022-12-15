# in-mem-kv-store

A simple thread-safe key-value store written in Rust with no external
dependencies. A single key-value store can hold keys and values of different
types.

The `KeyValueStore` uses the standard library's [`HashMap`](https://doc.rust-lang.org/std/collections/struct.HashMap.html)
as the underlying data structure. For thread-safety, it leverages [`RwLock`](https://doc.rust-lang.org/std/sync/struct.RwLock.html)
and [`Arc`](https://doc.rust-lang.org/std/sync/struct.Arc.html). The `RwLock` ensures
that the key-value store is accessed in a safe / synchronized manner and
the `Arc` allows multiple threads to safely share ownership of the key-value
store.

A `RwLock` was selected over a [`Mutex`](https://doc.rust-lang.org/std/sync/struct.Mutex.html)
because it allows multiple readers to access the key-value store
concurrently, whereas a `Mutex` will only allow one reader at a time.
Using a `RwLock` can lead to better performance, especially for read-heavy
applications. It reduces the number of times the key-value store needs to be
locked and unlocked `get` operations.

## Basic Usage:
```rust
use std::collections::{BTreeMap, HashMap};
use std::str::from_utf8;
use std::thread::sleep;
use std::thread::spawn;
use std::time::Duration;

use in_mem_kv_store::key::Key;
use in_mem_kv_store::value::Value;
use in_mem_kv_store::KeyValueStore;

// Create new key-value store
let mut kvs = KeyValueStore::new();

// Create a ttl for key expiry
let key_ttl = Duration::from_secs(2);

// Create keys with expiration
let bytes_key = Key::from(vec![107, 101, 121]).with_expiry(key_ttl); // b"key"
let number_key = Key::from(42).with_expiry(key_ttl);
let string_slice_key = Key::from("key").with_expiry(key_ttl);

// Create values
let bytes_value = Value::from(vec![240, 159, 145, 141]); // 👍
let number_value = Value::from(42);
let string_slice_value = Value::from("value");

// Add entries
kvs.put(&bytes_key, &bytes_value);
kvs.put(&number_key, &number_value);
kvs.put(&string_slice_key, &string_slice_value);

// Convert raw / original values
let raw_bytes: Vec<u8> = kvs.get(&bytes_key).unwrap().try_into().unwrap();
let str_from_bytes: &str = from_utf8(&raw_bytes).unwrap();
let raw_number: isize = kvs.get(&number_key).unwrap().try_into().unwrap();
let raw_string_slice: &str = kvs.get(&string_slice_key).unwrap().try_into().unwrap();

// Assert raw / original values
assert_eq!(raw_bytes, [240, 159, 145, 141]);
assert_eq!(str_from_bytes, "👍");
assert_eq!(raw_number, 42);
assert_eq!(raw_string_slice, "value");

// Wait until entries expire
sleep(key_ttl);

// Assert entries no longer exist
assert_eq!(kvs.get(&bytes_key), None);
assert_eq!(kvs.get(&number_key), None);
assert_eq!(kvs.get(&string_slice_key), None);

// Re-add entries
kvs.put(&bytes_key, &bytes_value);
kvs.put(&number_key, &number_value);
kvs.put(&string_slice_key, &string_slice_value);

// Remove entries
kvs.delete(&bytes_key);
kvs.delete(&number_key);
kvs.delete(&string_slice_key);

// Assert entries no longer exist
assert_eq!(kvs.get(&bytes_key), None);
assert_eq!(kvs.get(&number_key), None);
assert_eq!(kvs.get(&string_slice_key), None);
```
This library can panic in the event the [`RwLock` becomes poisoned](https://doc.rust-lang.org/std/sync/struct.RwLock.html#poisoning).

A key-value store created with the `new` associated function will, by
default, set the `capacity` of the underlying `HashMap` to zero. This
means that the store will not allocate until a `put` operation is performed.

The capacity is the number of elements the key-value store can hold
without reallocating. It is the lower bound and is guaranteed to be able to
hold at least that amount. The capacity setting can be modified using the
`KeyValueStoreBuilder`.

In general,`get` and `delete` operations on the `KeyValueStore`, have a time
complexity of O(1) on average. In the worst case, the time complexity is
O(n). This can occur when the there is significant lock contention, the
number of elements reaches capacity and forces a resize, or in unlikely
event of hash collisions. For `put` operations, however, the time complexity
is O(capacity).

For this reason, modifying the capacity to a large number using the
`KeyValueStoreBuilder` is _discouraged_ at this time and can have a
significant performance impact due to the way expired keys are removed from
the key-value store.

At this time, expired keys are removed every time an entry is added to the
store. Upon insert, the underlying `HashMap`'s `retain` method is called and
a predicated condition is applied to only retain unexpired entries. The
problem is, the performance of this method is O(capacity) as opposed to
O(n). This is why `put` has an unfavorable time complexity. For example,
you set the capacity to ten million and only have one thousand entries,
adding entries to the key-value store will take much longer than necessary
because it will it internally visit all the `HashMap`s buckets, including
the empty ones as well, upon every insert. An alternative to this approach
could be to implement a process that runs on a background thread
periodically to clean up expired entries, similar to a garbage collector.

In general, the space complexity of the key-value store is O(n), where n is
the number of elements in the store.

## Test
```zsh
cargo test
```

## Bench
```zsh
cargo bench
```
## Docs
```zsh
cargo doc --open
```
[Generate README](https://github.com/livioribeiro/cargo-readme).
```zsh
cargo readme > README.md
```
