//! Contains the `Value` structure which is used as a value within
//! the key-value store.
use core::hash::Hash;
use std::collections::{BTreeMap, HashMap};

/// `Map` is an enum of the of the types used for structured values within the
/// key-value store. It supports both `HashMap` and `BTreeMap`. Keys must be of
/// type `String` and values can be any of the `ValueKind` variants.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Map<String: Hash + Eq, Value> {
  /// The `HashMap` variant of the `Map`.
  Hash(HashMap<String, Value>),
  /// The `BTreeMap` variant of the `Map`.
  BTree(BTreeMap<String, Value>),
}

/// `ValueKind` is an enumeration of the available value types in the key-value
/// store.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValueKind {
  /// Represents a bytes value.
  Bytes(Vec<u8>),
  /// Represents a signed number value.
  Number(isize),
  /// Represents a unicode scalar value.
  Char(char),
  /// Represents a static string slice value.
  StringSlice(&'static str),
  /// Represents a string value.
  String(String),
  /// Represents a boolean value.
  Bool(bool),
  /// Represents a repeated value.
  List(Vec<Value>),
  /// Represents a structured value in the form of HashMap or BTreeMap.
  Map(Map<String, Value>),
}

/// Represents a value in the key-value store.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Value(ValueKind);

impl From<Vec<u8>> for Value {
  fn from(v: Vec<u8>) -> Self {
    Self(ValueKind::Bytes(v))
  }
}

impl From<isize> for Value {
  fn from(v: isize) -> Self {
    Self(ValueKind::Number(v))
  }
}

impl From<char> for Value {
  fn from(v: char) -> Self {
    Self(ValueKind::Char(v))
  }
}

impl From<&'static str> for Value {
  fn from(v: &'static str) -> Self {
    Self(ValueKind::StringSlice(v))
  }
}

impl From<String> for Value {
  fn from(v: String) -> Self {
    Self(ValueKind::String(v))
  }
}

impl From<bool> for Value {
  fn from(v: bool) -> Self {
    Self(ValueKind::Bool(v))
  }
}

impl From<Vec<Self>> for Value {
  fn from(v: Vec<Self>) -> Self {
    Self(ValueKind::List(v))
  }
}

impl From<HashMap<String, Self>> for Value {
  fn from(v: HashMap<String, Self>) -> Self {
    Self(ValueKind::Map(Map::Hash(v)))
  }
}

impl From<BTreeMap<String, Self>> for Value {
  fn from(v: BTreeMap<String, Self>) -> Self {
    Self(ValueKind::Map(Map::BTree(v)))
  }
}

impl TryFrom<Value> for Vec<u8> {
  type Error = String;

  fn try_from(v: Value) -> Result<Self, Self::Error> {
    if let ValueKind::Bytes(r) = v.0 {
      return Ok(r);
    }

    Err(format!("Incorrect type for value: {:?}", v))
  }
}

impl TryFrom<Value> for isize {
  type Error = String;

  fn try_from(v: Value) -> Result<Self, Self::Error> {
    if let ValueKind::Number(r) = v.0 {
      return Ok(r);
    }

    Err(format!("Incorrect type for value: {:?}", v))
  }
}

impl TryFrom<Value> for char {
  type Error = String;

  fn try_from(v: Value) -> Result<Self, Self::Error> {
    if let ValueKind::Char(r) = v.0 {
      return Ok(r);
    }

    Err(format!("Incorrect type for value: {:?}", v))
  }
}

impl TryFrom<Value> for &'static str {
  type Error = String;

  fn try_from(v: Value) -> Result<Self, Self::Error> {
    if let ValueKind::StringSlice(r) = v.0 {
      return Ok(r);
    }

    Err(format!("Incorrect type for value: {:?}", v))
  }
}

impl TryFrom<Value> for String {
  type Error = String;

  fn try_from(v: Value) -> Result<Self, Self::Error> {
    if let ValueKind::String(r) = v.0 {
      return Ok(r);
    }

    Err(format!("Incorrect type for value: {:?}", v))
  }
}

impl TryFrom<Value> for Vec<Value> {
  type Error = String;

  fn try_from(v: Value) -> Result<Self, Self::Error> {
    if let ValueKind::List(r) = v.0 {
      return Ok(r);
    }

    Err(format!("Incorrect type for value: {:?}", v))
  }
}

impl TryFrom<Value> for HashMap<String, Value> {
  type Error = String;

  fn try_from(v: Value) -> Result<Self, Self::Error> {
    if let ValueKind::Map(Map::Hash(r)) = v.0 {
      return Ok(r);
    }

    Err(format!("Incorrect type for value: {:?}", v))
  }
}

impl TryFrom<Value> for BTreeMap<String, Value> {
  type Error = String;

  fn try_from(v: Value) -> Result<Self, Self::Error> {
    if let ValueKind::Map(Map::BTree(r)) = v.0 {
      return Ok(r);
    }

    Err(format!("Incorrect type for value: {:?}", v))
  }
}

impl TryFrom<Value> for bool {
  type Error = String;

  fn try_from(v: Value) -> Result<Self, Self::Error> {
    if let ValueKind::Bool(r) = v.0 {
      return Ok(r);
    }

    Err(format!("Incorrect type for value: {:?}", v))
  }
}
