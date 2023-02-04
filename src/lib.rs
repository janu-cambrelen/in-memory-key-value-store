//! A thread-safe key-value store, implemented in Rust with zero dependencies,
//! that supports keys and values of different types within the same store.
//!
//! The `KeyValueStore` uses the standard library's [`HashMap`](https://doc.rust-lang.org/std/collections/struct.HashMap.html)
//! as the underlying data structure. For thread-safety, it leverages [`RwLock`](https://doc.rust-lang.org/std/sync/struct.RwLock.html)
//! and [`Arc`](https://doc.rust-lang.org/std/sync/struct.Arc.html). The `RwLock` ensures
//! that the key-value store is accessed in a safe / synchronized manner and
//! the `Arc` allows multiple threads to safely share ownership of the key-value
//! store.
//!
//! A `RwLock` was selected over a [`Mutex`](https://doc.rust-lang.org/std/sync/struct.Mutex.html)
//! because it allows multiple readers to access the key-value store
//! concurrently, whereas a `Mutex` will only allow one reader at a time.
//! Using a `RwLock` can lead to better performance, especially for read-heavy
//! applications. It reduces the number of times the key-value store needs to be
//! locked and unlocked `get` operations.
//!
//! # Basic Usage:
//! ```rust
//! use std::str::from_utf8;
//! use std::thread::sleep;
//! use std::time::Duration;
//!
//! use in_mem_kv_store::key::Key;
//! use in_mem_kv_store::value::Value;
//! use in_mem_kv_store::KeyValueStore;
//!
//! // Create new key-value store
//! let mut kvs = KeyValueStore::new();
//!
//! // Create a ttl for key expiry
//! let key_ttl = Duration::from_secs(2);
//!
//! // Create keys with expiration
//! let bytes_key = Key::from(vec![107, 101, 121]).with_expiry(key_ttl); // b"key"
//! let number_key = Key::from(42).with_expiry(key_ttl);
//! let string_slice_key = Key::from("key").with_expiry(key_ttl);
//!
//! // Create values
//! let bytes_value = Value::from(vec![240, 159, 145, 141]); // 👍
//! let number_value = Value::from(42);
//! let string_slice_value = Value::from("value");
//!
//! // Add entries
//! kvs.put(&bytes_key, &bytes_value);
//! kvs.put(&number_key, &number_value);
//! kvs.put(&string_slice_key, &string_slice_value);
//!
//! // Convert raw / original values
//! let raw_bytes: Vec<u8> = kvs.get(&bytes_key).unwrap().try_into().unwrap();
//! let str_from_bytes: &str = from_utf8(&raw_bytes).unwrap();
//! let raw_number: isize = kvs.get(&number_key).unwrap().try_into().unwrap();
//! let raw_string_slice: &str = kvs.get(&string_slice_key).unwrap().try_into().unwrap();
//!
//! // Assert raw / original values
//! assert_eq!(raw_bytes, [240, 159, 145, 141]);
//! assert_eq!(str_from_bytes, "👍");
//! assert_eq!(raw_number, 42);
//! assert_eq!(raw_string_slice, "value");
//!
//! // Wait until entries expire
//! sleep(key_ttl);
//!
//! // Assert entries no longer exist
//! assert_eq!(kvs.get(&bytes_key), None);
//! assert_eq!(kvs.get(&number_key), None);
//! assert_eq!(kvs.get(&string_slice_key), None);
//!
//! // Add new entries
//! kvs.put(&Key::from(1), &Value::from("v1"));
//! kvs.put(&Key::from(2), &Value::from("v2"));
//! kvs.put(&Key::from(3), &Value::from("v3"));
//!
//! // Assert values
//! assert_eq!(kvs.get(&Key::from(1)), Some(Value::from("v1")));
//! assert_eq!(kvs.get(&Key::from(2)), Some(Value::from("v2")));
//! assert_eq!(kvs.get(&Key::from(3)), Some(Value::from("v3")));
//!
//! // Remove entries
//! kvs.delete(&Key::from(1));
//! kvs.delete(&Key::from(2));
//! kvs.delete(&Key::from(3));
//!
//! // Assert entries no longer exist
//! assert_eq!(kvs.get(&Key::from(1)), None);
//! assert_eq!(kvs.get(&Key::from(2)), None);
//! assert_eq!(kvs.get(&Key::from(3)), None);
//! ```
//! This library can panic in the event the [`RwLock` becomes poisoned](https://doc.rust-lang.org/std/sync/struct.RwLock.html#poisoning).
//!
//! A key-value store created with the `new` associated function will, by
//! default, set the `capacity` of the underlying `HashMap` to zero. This
//! means that the store will not allocate until a `put` operation is performed.
//!
//! The capacity is the number of elements the key-value store can hold
//! without reallocating. It is the lower bound and is guaranteed to be able to
//! hold at least that amount. The capacity setting can be modified using the
//! `KeyValueStoreBuilder`.
//!
//! In general,`get` and `delete` operations on the `KeyValueStore`, have a time
//! complexity of O(1) on average. In the worst case, the time complexity is
//! O(n). This can occur when the there is significant lock contention, the
//! number of elements reaches capacity and forces a resize, or in unlikely
//! event of hash collisions. For `put` operations, however, the time complexity
//! is O(capacity).
//!
//! For this reason, modifying the capacity to a large number using the
//! `KeyValueStoreBuilder` is _discouraged_ at this time and can have a
//! significant performance impact due to the way expired keys are removed from
//! the key-value store.
//!
//! At this time, expired keys are removed every time an entry is added to the
//! store. Upon insert, the underlying `HashMap`'s `retain` method is called and
//! a predicated condition is applied to only retain unexpired entries. The
//! problem is, the performance of this method is O(capacity) as opposed to
//! O(n). This is why `put` has an unfavorable time complexity. For example,
//! you set the capacity to ten million and only have one thousand entries,
//! adding entries to the key-value store will take much longer than necessary
//! because it will it internally visit all the `HashMap`s buckets, including
//! the empty ones as well, upon every insert. An alternative to this approach
//! could be to implement a process that runs on a background thread
//! periodically to clean up expired entries, similar to a garbage collector.
//!
//! In general, the space complexity of the key-value store is O(n), where n is
//! the number of elements in the store.
//!
//! # Test:
//! ```zsh
//! cargo test
//! ```
//! # Bench:
//! ```zsh
//! cargo bench
//! ```
//! # Docs:
//! ```zsh
//! cargo doc --open
//! ```
//! [Generate README](https://github.com/livioribeiro/cargo-readme):
//! ```zsh
//! cargo readme > README.md
//! ```
//! # License:
//! This project is licensed under the MIT License - see the
//! [LICENSE-MIT](LICENSE-MIT) file for details.

#![warn(clippy::all, missing_docs)]

pub mod key;
pub mod value;

use core::clone::Clone;
use key::Key;
use std::collections::HashMap;
use std::sync::{Arc, RwLock};
use std::time::Instant;
use value::Value;

/// The core structure of this library. It is the key-value store that can be
/// used between threads. It supports a number of dynamic types for `Key` and
/// `Value`.
#[derive(Debug, Clone)]
pub struct KeyValueStore {
  store: Arc<RwLock<HashMap<Key, Value>>>,
}

/// A builder for `KeyValueStore`.  It currently only includes the option to set
/// `capacity`.
pub struct KeyValueStoreBuilder {
  capacity: usize,
}

impl KeyValueStoreBuilder {
  /// Sets the `capacity` of a `KeyValueStore`.
  pub fn with_capacity(mut self, capacity: usize) -> Self {
    self.capacity = capacity;
    self
  }
  /// Creates a new `KeyValueStore` from the builder.
  pub fn build(self) -> KeyValueStore {
    KeyValueStore {
      store: Arc::new(RwLock::new(HashMap::with_capacity(self.capacity))),
    }
  }
}

impl Default for KeyValueStoreBuilder {
  fn default() -> Self {
    Self { capacity: 0 }
  }
}

impl KeyValueStore {
  /// Creates an empty `KeyValueStore`.
  ///
  /// The `KeyValueStore` is created with at least a capacity of ten million
  /// before it has to reallocate memory.
  ///
  /// ```rust
  /// use in_mem_kv_store::KeyValueStore;
  ///
  /// let kvs = KeyValueStore::new();
  /// ```
  pub fn new() -> Self {
    Self::default()
  }
  /// Returns a empty `KeyValueStoreBuilder` that enables a custom configuration
  /// for `KeyValueStore`
  ///
  /// ```rust
  /// use in_mem_kv_store::KeyValueStore;
  ///
  /// let kvs = KeyValueStore::builder().with_capacity(10_000_000).build();
  /// ```
  pub fn builder() -> KeyValueStoreBuilder {
    KeyValueStoreBuilder::default()
  }

  /// Gets a value from the key-value store. `None` will be returned if the
  /// value does not exist.
  ///
  /// ```rust
  /// use in_mem_kv_store::key::Key;
  /// use in_mem_kv_store::value::Value;
  /// use in_mem_kv_store::KeyValueStore;
  ///
  /// let mut kvs = KeyValueStore::new();
  ///
  /// let k = Key::from("k1");
  ///
  /// let got = kvs.get(&k);
  ///
  /// assert_eq!(got, None);
  /// ```
  pub fn get(&self, key: &Key) -> Option<Value> {
    if let Some(expiry) = key.get_expiry() {
      let now = Instant::now();
      if expiry < &now {
        return None;
      }
    }

    // REF: https://doc.rust-lang.org/std/sync/struct.RwLock.html#poisoning
    self
      .store
      .read()
      .expect("A panic occurred, the RwLock is poisoned")
      .get(key)
      .map(Clone::clone)
  }

  /// Inserts a value into the key-value store. If a value already exists for a
  /// given key ID, the value will be replaced.
  ///
  /// ```rust
  /// use std::time::Duration;
  /// use std::thread::sleep;
  ///
  /// use in_mem_kv_store::key::Key;
  /// use in_mem_kv_store::value::Value;
  /// use in_mem_kv_store::KeyValueStore;
  ///
  /// let mut kvs = KeyValueStore::new();
  ///
  /// // no expiry
  /// let k = Key::from("k1");
  /// let v = Value::from("v1");
  /// kvs.put(&k, &v);
  /// assert_eq!(kvs.get(&k), Some(v));
  ///
  /// // with expiry
  /// let k_exp = Key::from("k2").with_expiry(Duration::from_secs(2));
  /// let v_exp = Value::from("v2");
  /// kvs.put(&k_exp, &v_exp);
  /// assert_eq!(kvs.get(&k_exp), Some(v_exp));
  /// sleep(Duration::from_secs(2));
  /// assert_eq!(kvs.get(&k_exp), None);
  /// ```
  pub fn put(&mut self, key: &Key, value: &Value) {
    // REF: https://doc.rust-lang.org/std/sync/struct.RwLock.html#poisoning
    let mut w = self
      .store
      .write()
      .expect("A panic occurred, the RwLock is poisoned");

    let now = Instant::now();

    w.retain(|k, _| k.get_expiry().map_or(true, |x| x > now));
    w.insert(key.clone(), value.clone());
  }

  /// Removes a value from the key-value store. If a value already exists
  /// for a given key ID, the value will be replaced.
  ///
  /// ```rust
  /// use in_mem_kv_store::key::Key;
  /// use in_mem_kv_store::value::Value;
  /// use in_mem_kv_store::KeyValueStore;
  ///
  /// let mut kvs = KeyValueStore::new();
  ///
  /// let k = Key::from("k1");
  /// let v = Value::from("v1");
  ///
  /// kvs.put(&k, &v);
  /// assert_eq!(kvs.get(&k), Some(v));
  ///
  /// kvs.delete(&k);
  /// assert_eq!(kvs.get(&k), None);
  /// ```
  pub fn delete(&mut self, key: &Key) {
    // REF: https://doc.rust-lang.org/std/sync/struct.RwLock.html#poisoning
    self
      .store
      .write()
      .expect("A panic occurred, the RwLock is poisoned")
      .remove(key);
  }

  /// Returns the number of elements in the key-value store.
  ///
  /// ```rust
  /// use in_mem_kv_store::key::Key;
  /// use in_mem_kv_store::value::Value;
  /// use in_mem_kv_store::KeyValueStore;
  ///
  /// let mut kvs = KeyValueStore::new();
  ///
  /// let k = Key::from("k1");
  /// let v = Value::from("v1");
  ///
  /// kvs.put(&k, &v);
  /// assert_eq!(kvs.len(), 1);
  /// ```
  // This method is useful for testing, etc.
  pub fn len(&self) -> usize {
    self
      .store
      .read()
      .expect("A panic occurred, the RwLock is poisoned")
      .len()
  }

  /// Returns whether key-value store contains zero elements.
  ///
  /// ```rust
  /// use in_mem_kv_store::key::Key;
  /// use in_mem_kv_store::value::Value;
  /// use in_mem_kv_store::KeyValueStore;
  ///
  /// let mut kvs = KeyValueStore::new();
  ///
  /// assert_eq!(kvs.is_empty(), true);
  /// ```
  // This method is useful for testing, etc.
  pub fn is_empty(&self) -> bool {
    self
      .store
      .read()
      .expect("A panic occurred, the RwLock is poisoned")
      .is_empty()
  }
}

impl Default for KeyValueStore {
  fn default() -> Self {
    KeyValueStoreBuilder::default().with_capacity(0).build()
  }
}

// These tests cover the basic functionality of the `KeyValueStore`
// implementation, including inserting key-value pairs with and without
// expiration times, retrieving values by key, deleting key-value pairs, and
// cleaning up expired values.

// The tests use the sleep method from the thread crate to simulate the passage
// of time, so that the expiration times of the values can be tested.
#[cfg(test)]
mod tests {
  use std::collections::{BTreeMap, HashMap};
  use std::str::from_utf8;
  use std::thread;
  use std::time::Duration;

  use crate::key::Key;
  use crate::value::Value;
  use crate::KeyValueStore;

  #[test]

  fn test_actions() {
    let mut kvs = KeyValueStore::new();

    let k_bytes = Key::from("Bytes");
    let k_number = Key::from("Number");
    let k_char = Key::from("Char");
    let k_string_slice = Key::from("StringSlice");
    let k_string = Key::from("String");
    let k_bool = Key::from("Bool");
    let k_list = Key::from("List");
    let k_hash_map = Key::from("Hash");
    let k_btree_map = Key::from("BTree");

    let v_bytes = Value::from(vec![240, 159, 145, 141]); // 👍
    let v_number = Value::from(42);
    let v_char = Value::from('👍');
    let v_string_slice = Value::from("StringSlice");
    let v_string = Value::from("String".to_string());
    let v_bool = Value::from(true);
    let v_list = Value::from(vec![Value::from(1), Value::from("one")]);
    let v_hash_map = Value::from(HashMap::from([("hash_one".to_string(), Value::from(1))]));
    let v_btree_map = Value::from(BTreeMap::from([("hash_one".to_string(), Value::from(1))]));

    kvs.put(&k_bytes, &v_bytes);
    kvs.put(&k_number, &v_number);
    kvs.put(&k_char, &v_char);
    kvs.put(&k_string_slice, &v_string_slice);
    kvs.put(&k_string, &v_string);
    kvs.put(&k_bool, &v_bool);
    kvs.put(&k_list, &v_list);
    kvs.put(&k_hash_map, &v_hash_map);
    kvs.put(&k_btree_map, &v_btree_map);

    // Assert `Option<Values>`
    assert_eq!(kvs.get(&k_bytes), Some(v_bytes));
    assert_eq!(kvs.get(&k_number), Some(v_number));
    assert_eq!(kvs.get(&k_char), Some(v_char));
    assert_eq!(kvs.get(&k_string_slice), Some(v_string_slice));
    assert_eq!(kvs.get(&k_string), Some(v_string));
    assert_eq!(kvs.get(&k_bool), Some(v_bool));
    assert_eq!(kvs.get(&k_list), Some(v_list));
    assert_eq!(kvs.get(&k_hash_map), Some(v_hash_map));
    assert_eq!(kvs.get(&k_btree_map), Some(v_btree_map));

    kvs.delete(&k_bytes);
    kvs.delete(&k_number);
    kvs.delete(&k_char);
    kvs.delete(&k_string_slice);
    kvs.delete(&k_string);
    kvs.delete(&k_bool);
    kvs.delete(&k_list);
    kvs.delete(&k_hash_map);
    kvs.delete(&k_btree_map);

    // Assert entries no longer exist
    assert_eq!(kvs.get(&k_bytes), None);
    assert_eq!(kvs.get(&k_number), None);
    assert_eq!(kvs.get(&k_char), None);
    assert_eq!(kvs.get(&k_string_slice), None);
    assert_eq!(kvs.get(&k_string), None);
    assert_eq!(kvs.get(&k_bool), None);
    assert_eq!(kvs.get(&k_list), None);
    assert_eq!(kvs.get(&k_hash_map), None);
    assert_eq!(kvs.get(&k_btree_map), None);
  }

  #[test]
  fn test_actions_raw_values() {
    let mut kvs = KeyValueStore::new();

    let k_bytes = Key::from("Bytes");
    let k_number = Key::from("Number");
    let k_char = Key::from("Char");
    let k_string_slice = Key::from("StringSlice");
    let k_string = Key::from("String");
    let k_bool = Key::from("Bool");
    let k_list = Key::from("List");
    let k_hash_map = Key::from("Hash");
    let k_btree_map = Key::from("BTree");

    let v_bytes = Value::from(vec![240, 159, 145, 141]); // 👍
    let v_number = Value::from(42);
    let v_char = Value::from('😀');
    let v_string_slice = Value::from("StringSlice");
    let v_string = Value::from("String".to_string());
    let v_bool = Value::from(true);
    let v_list = Value::from(vec![Value::from(1), Value::from("one")]);
    let v_hash_map = Value::from(HashMap::from([("hash_one".to_string(), Value::from(1))]));
    let v_btree_map = Value::from(BTreeMap::from([("btree_one".to_string(), Value::from(1))]));

    kvs.put(&k_bytes, &v_bytes);
    kvs.put(&k_number, &v_number);
    kvs.put(&k_char, &v_char);
    kvs.put(&k_string_slice, &v_string_slice);
    kvs.put(&k_string, &v_string);
    kvs.put(&k_bool, &v_bool);
    kvs.put(&k_list, &v_list);
    kvs.put(&k_hash_map, &v_hash_map);
    kvs.put(&k_btree_map, &v_btree_map);

    // Convert to raw / original values
    let raw_bytes: Vec<u8> = kvs.get(&k_bytes).unwrap().try_into().unwrap();
    let str_from_bytes: &str = from_utf8(&raw_bytes).unwrap();
    let raw_number: isize = kvs.get(&k_number).unwrap().try_into().unwrap();
    let raw_char: char = kvs.get(&k_char).unwrap().try_into().unwrap();
    let raw_string_slice: &str = kvs.get(&k_string_slice).unwrap().try_into().unwrap();
    let raw_string: String = kvs.get(&k_string).unwrap().try_into().unwrap();
    let raw_bool: bool = kvs.get(&k_bool).unwrap().try_into().unwrap();
    let raw_list: Vec<Value> = kvs.get(&k_list).unwrap().try_into().unwrap();
    let raw_hash_map: HashMap<String, Value> = kvs.get(&k_hash_map).unwrap().try_into().unwrap();
    let raw_btree_map: BTreeMap<String, Value> = kvs.get(&k_btree_map).unwrap().try_into().unwrap();

    // Assert raw / original values
    assert_eq!(raw_bytes, vec![240, 159, 145, 141]); // 👍
    assert_eq!(str_from_bytes, "👍");
    assert_eq!(raw_number, 42);
    assert_eq!(raw_char, '😀');
    assert_eq!(raw_string_slice, "StringSlice");
    assert_eq!(raw_string, "String".to_string());
    assert_eq!(raw_bool, true);
    assert_eq!(raw_list, vec![Value::from(1), Value::from("one")]);
    assert_eq!(
      raw_hash_map,
      HashMap::from([("hash_one".to_string(), Value::from(1))])
    );
    assert_eq!(
      raw_btree_map,
      BTreeMap::from([("btree_one".to_string(), Value::from(1))])
    );

    kvs.delete(&k_bytes);
    kvs.delete(&k_number);
    kvs.delete(&k_char);
    kvs.delete(&k_string_slice);
    kvs.delete(&k_string);
    kvs.delete(&k_bool);
    kvs.delete(&k_list);
    kvs.delete(&k_hash_map);
    kvs.delete(&k_btree_map);

    // Assert entries no longer exist
    assert_eq!(kvs.get(&k_bytes), None);
    assert_eq!(kvs.get(&k_number), None);
    assert_eq!(kvs.get(&k_char), None);
    assert_eq!(kvs.get(&k_string_slice), None);
    assert_eq!(kvs.get(&k_string), None);
    assert_eq!(kvs.get(&k_bool), None);
    assert_eq!(kvs.get(&k_list), None);
    assert_eq!(kvs.get(&k_hash_map), None);
    assert_eq!(kvs.get(&k_btree_map), None);
  }

  #[test]
  fn test_actions_with_expiry() {
    let mut kvs = KeyValueStore::new();
    let ttl = Duration::from_secs(2);

    let k_bytes = Key::from("Bytes").with_expiry(ttl);
    let k_number = Key::from("Number").with_expiry(ttl);
    let k_char = Key::from("Char").with_expiry(ttl);
    let k_string_slice = Key::from("StringSlice").with_expiry(ttl);
    let k_string = Key::from("String").with_expiry(ttl);
    let k_bool = Key::from("Bool").with_expiry(ttl);
    let k_list = Key::from("List").with_expiry(ttl);
    let k_hash_map = Key::from("Hash").with_expiry(ttl);
    let k_btree_map = Key::from("BTree").with_expiry(ttl);

    let v_bytes = Value::from(vec![240, 159, 145, 141]); // 👍
    let v_number = Value::from(42);
    let v_char = Value::from('😀');
    let v_string_slice = Value::from("StringSlice");
    let v_string = Value::from("String".to_string());
    let v_bool = Value::from(true);
    let v_list = Value::from(vec![Value::from(1), Value::from("one")]);
    let v_hash_map = Value::from(HashMap::from([("hash_one".to_string(), Value::from(1))]));
    let v_btree_map = Value::from(BTreeMap::from([("hash_one".to_string(), Value::from(1))]));

    kvs.put(&k_bytes, &v_bytes);
    kvs.put(&k_number, &v_number);
    kvs.put(&k_char, &v_char);
    kvs.put(&k_string_slice, &v_string_slice);
    kvs.put(&k_string, &v_string);
    kvs.put(&k_bool, &v_bool);
    kvs.put(&k_list, &v_list);
    kvs.put(&k_hash_map, &v_hash_map);
    kvs.put(&k_btree_map, &v_btree_map);

    // Assert values exist
    assert_eq!(kvs.get(&k_bytes), Some(v_bytes));
    assert_eq!(kvs.get(&k_number), Some(v_number));
    assert_eq!(kvs.get(&k_char), Some(v_char));
    assert_eq!(kvs.get(&k_string_slice), Some(v_string_slice));
    assert_eq!(kvs.get(&k_string), Some(v_string));
    assert_eq!(kvs.get(&k_bool), Some(v_bool));
    assert_eq!(kvs.get(&k_list), Some(v_list));
    assert_eq!(kvs.get(&k_hash_map), Some(v_hash_map));
    assert_eq!(kvs.get(&k_btree_map), Some(v_btree_map));

    // Wait until entries expire
    thread::sleep(ttl);

    // Assert entries no longer exist
    assert_eq!(kvs.get(&k_bytes), None);
    assert_eq!(kvs.get(&k_number), None);
    assert_eq!(kvs.get(&k_char), None);
    assert_eq!(kvs.get(&k_string_slice), None);
    assert_eq!(kvs.get(&k_string), None);
    assert_eq!(kvs.get(&k_bool), None);
    assert_eq!(kvs.get(&k_list), None);
    assert_eq!(kvs.get(&k_hash_map), None);
    assert_eq!(kvs.get(&k_btree_map), None);
  }

  #[test]
  fn test_keys() {
    let mut kvs = KeyValueStore::new();

    let bytes_key = Key::from(vec![240, 159, 145, 141]); // 👍
    let number_key = Key::from(42);
    let char_key = Key::from('😀');
    let string_slice_key = Key::from("StringSlice");
    let string_key = Key::from("String".to_string());
    let bool_key = Key::from(true);

    kvs.put(&bytes_key, &Value::from(1));
    kvs.put(&number_key, &Value::from(1));
    kvs.put(&char_key, &Value::from(1));
    kvs.put(&string_key, &Value::from(1));
    kvs.put(&string_slice_key, &Value::from(1));
    kvs.put(&bool_key, &Value::from(1));

    // Assert values exist
    assert_eq!(kvs.get(&bytes_key), Some(Value::from(1)));
    assert_eq!(kvs.get(&number_key), Some(Value::from(1)));
    assert_eq!(kvs.get(&char_key), Some(Value::from(1)));
    assert_eq!(kvs.get(&string_key), Some(Value::from(1)));
    assert_eq!(kvs.get(&string_slice_key), Some(Value::from(1)));
    assert_eq!(kvs.get(&bool_key), Some(Value::from(1)));

    // Convert to raw / original keys
    let raw_bytes: Vec<u8> = bytes_key.try_into().unwrap();
    let str_from_bytes: &str = from_utf8(&raw_bytes).unwrap();
    let raw_number: isize = number_key.try_into().unwrap();
    let raw_char: char = char_key.try_into().unwrap();
    let raw_string_slice: &str = string_slice_key.try_into().unwrap();
    let raw_string: String = string_key.try_into().unwrap();
    let raw_bool: bool = bool_key.try_into().unwrap();

    // Assert raw / original keys
    assert_eq!(raw_bytes, vec![240, 159, 145, 141]); // 👍
    assert_eq!(str_from_bytes, "👍");
    assert_eq!(raw_number, 42);
    assert_eq!(raw_char, '😀');
    assert_eq!(raw_string_slice, "StringSlice");
    assert_eq!(raw_string, "String".to_string());
    assert_eq!(raw_bool, true);
  }

  #[test]
  fn test_multiple_threads() {
    // The target number of values to be written and read by the threads. The actual
    // number of values may be less than this number if the number of values is not
    // evenly divisible by the number of threads.
    let target_num_values = 10_000;

    // Create a new key-value store with a capacity of `target_num_values`.
    let kvs = KeyValueStore::builder()
      .with_capacity(target_num_values)
      .build();

    // The number of threads allocated to writers and readers is determined by
    // the number of available CPUs. The number of CPUs is divided by two and
    // rounded down to the nearest even number. The number of CPUs is then
    // divided by two to evenly distribute the threads between writers and
    // readers.
    let cpu_allocation = (std::thread::available_parallelism().unwrap().get() & !1) / 2;

    // If the number of CPUs is less than two, abort this test case.
    if cpu_allocation < 2 {
      return;
    }

    // The number of values to be written and read by each thread.
    let values_allocation = target_num_values / cpu_allocation;

    // Spawn writer threads to write values to the store.
    let writers: Vec<_> = (0..cpu_allocation)
      .map(|i| {
        let mut kvs_clone = kvs.clone();

        thread::Builder::new()
          .name(format!("Writer #{}", i))
          .spawn(move || {
            let start = values_allocation * i;
            let finish = values_allocation * (i + 1);

            for num in start..finish {
              kvs_clone.put(
                &Key::from(num as isize),
                &Value::from(format!("Value # {}", num)),
              );
            }
          })
          .expect("could not spawn writer thread")
      })
      .collect();

    // Spawn reader threads to read values from the store, after some writes have
    // occurred.
    let readers: Vec<_> = (0..cpu_allocation)
      .map(|i| {
        let kvs_clone = kvs.clone();

        thread::Builder::new()
          .name(format!("Reader #{}", i))
          .spawn(move || {
            // The delay is to ensure that the writer threads have time to write.
            thread::sleep(Duration::from_millis(25));

            let start = values_allocation * i;
            let finish = values_allocation * (i + 1);

            for num in start..finish {
              if let None = kvs_clone.get(&Key::from(num as isize)) {
                // The delay should be sufficient for this test.  If the delay is not long
                // enough, the test will fail.
                panic!("no value returned")
              }
            }
          })
          .expect("could not spawn reader thread")
      })
      .collect();

    for writer in writers {
      writer.join().expect("could not join writer threads");
    }

    for reader in readers {
      reader.join().expect("could not join reader threads");
    }

    // Assert that the number of values in the store is equal to the number of
    // values allocated to / processed by the threads.
    assert_eq!(kvs.len(), cpu_allocation * values_allocation);
  }
}
