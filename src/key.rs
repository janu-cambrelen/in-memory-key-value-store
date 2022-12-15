//! Contains the `Key` structure which is used as the key in
//! the key-value store.
use std::{
  hash::Hash,
  time::{Duration, Instant},
};

/// `KeyKind` is an enumeration of the available key ID types in the key-value
/// store.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum KeyKind {
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
}

/// Represents a key in the key-value store. Its `id` can be any of the
/// `KeyKind` variants. The key can be set with optional expiration time using
/// the `with_expiry` method, which accepts a `Duration` value.
#[derive(Debug, Clone, Eq)]
pub struct Key {
  id: KeyKind,
  expires_at: Option<Instant>,
}

impl Key {
  /// Returns the optional value containing the `Instant` value.
  pub fn get_expiry(&self) -> &Option<Instant> {
    &self.expires_at
  }
  /// Accepts a `Duration` value "x" and sets the key expiry to "x" from now.
  pub fn with_expiry(mut self, duration: Duration) -> Self {
    let expiry = Instant::now().checked_add(duration);
    self.expires_at = expiry;
    self
  }
}

impl PartialEq for Key {
  fn eq(&self, other: &Self) -> bool {
    self.id == other.id
  }
}

impl Hash for Key {
  fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
    self.id.hash(state);
  }
}

impl From<Vec<u8>> for Key {
  fn from(k: Vec<u8>) -> Self {
    Self {
      id: KeyKind::Bytes(k),
      expires_at: None,
    }
  }
}

impl From<isize> for Key {
  fn from(k: isize) -> Self {
    Self {
      id: KeyKind::Number(k),
      expires_at: None,
    }
  }
}

impl From<char> for Key {
  fn from(k: char) -> Self {
    Self {
      id: KeyKind::Char(k),
      expires_at: None,
    }
  }
}

impl From<&'static str> for Key {
  fn from(k: &'static str) -> Self {
    Self {
      id: KeyKind::StringSlice(k),
      expires_at: None,
    }
  }
}
impl From<String> for Key {
  fn from(k: String) -> Self {
    Self {
      id: KeyKind::String(k),
      expires_at: None,
    }
  }
}

impl From<bool> for Key {
  fn from(k: bool) -> Self {
    Self {
      id: KeyKind::Bool(k),
      expires_at: None,
    }
  }
}

impl TryFrom<Key> for Vec<u8> {
  type Error = String;

  fn try_from(k: Key) -> Result<Self, Self::Error> {
    if let KeyKind::Bytes(r) = k.id {
      return Ok(r);
    }

    Err(format!("Incorrect type for key: {:?}", k))
  }
}

impl TryFrom<Key> for isize {
  type Error = String;

  fn try_from(k: Key) -> Result<Self, Self::Error> {
    if let KeyKind::Number(r) = k.id {
      return Ok(r);
    }

    Err(format!("Incorrect type for key: {:?}", k))
  }
}

impl TryFrom<Key> for char {
  type Error = String;

  fn try_from(k: Key) -> Result<Self, Self::Error> {
    if let KeyKind::Char(r) = k.id {
      return Ok(r);
    }

    Err(format!("Incorrect type for key: {:?}", k))
  }
}

impl TryFrom<Key> for &'static str {
  type Error = String;

  fn try_from(k: Key) -> Result<Self, Self::Error> {
    if let KeyKind::StringSlice(r) = k.id {
      return Ok(r);
    }

    Err(format!("Incorrect type for key: {:?}", k))
  }
}

impl TryFrom<Key> for String {
  type Error = String;

  fn try_from(k: Key) -> Result<Self, Self::Error> {
    if let KeyKind::String(r) = k.id {
      return Ok(r);
    }

    Err(format!("Incorrect type for key: {:?}", k))
  }
}

impl TryFrom<Key> for bool {
  type Error = String;

  fn try_from(k: Key) -> Result<Self, Self::Error> {
    if let KeyKind::Bool(r) = k.id {
      return Ok(r);
    }

    Err(format!("Incorrect type for key: {:?}", k))
  }
}
