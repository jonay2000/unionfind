use std::collections::{BTreeMap, HashMap};
use std::error::Error;
use std::hash::Hash;
use std::ops::{Deref, DerefMut};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum AddError {
    #[error("union find can't support more keys")]
    Full,
    #[error("this key was already in the mapping, and thus cannot be added. consider using `set` or `set_or_add`")]
    AlreadyIn,

    #[error("this mapping implementation requires keys to be consecutive. You tried to add a key that did not directly follow the previous key.")]
    NotInOrder,
}

pub trait ParentMapping<K>: Mapping<K, K> + Sized {
    type Err: Error;

    /// should identity map every item in items
    fn identity_map<I: IntoIterator<Item = K>>(items: I) -> Result<Self, Self::Err>;
}

pub trait RankMapping<K>: Mapping<K, usize> + Sized {
    type Err: Error;

    /// should create a map with every key mapped to zero
    fn zero_map<I: IntoIterator<Item = K>>(items: I) -> Result<Self, Self::Err>;
}

impl<T, K: Clone> ParentMapping<K> for T
where
    T: IdentityMapping<K>,
    K: Clone,
{
    type Err = AddError;

    fn identity_map<I: IntoIterator<Item = K>>(items: I) -> Result<Self, Self::Err> {
        let mut map = Self::empty();
        for i in items {
            map.add_identity(i)?
        }

        Ok(map)
    }
}

impl<T, K> RankMapping<K> for T
where
    T: GrowableMapping<K, usize>,
{
    type Err = AddError;

    fn zero_map<I: IntoIterator<Item = K>>(items: I) -> Result<Self, Self::Err> {
        let mut map = Self::empty();
        for i in items {
            map.add(i, 0)?
        }

        Ok(map)
    }
}

/// A mapping is functionally equivalent to a hashmap.
/// The trait is even implemented for hashmaps. However,
/// in some cases, it's efficient to use an array instead,
/// since in a union find, keys are often integers, generated in-order.
pub trait Mapping<K, V> {
    /// gets an element from the mapping. Returns none
    /// if the key is not found in the mapping.
    fn get(&self, key: &K) -> Option<&V>;

    /// Returns true if the mapping contains a certain element
    fn contains_key(&self, key: &K) -> bool {
        self.get(key).is_some()
    }

    /// Set a key to a certain value. The key must be present in the
    /// mapping, and callers must check this with get first. The implementation
    /// may panic when a key cannot be found.
    fn set(&mut self, key: K, value: V);
}

pub trait IdentityMapping<K>: GrowableMapping<K, K>
where
    K: Clone,
{
    /// Add an item mapped to itself.
    fn add_identity(&mut self, key: K) -> Result<(), AddError> {
        self.add(key.clone(), key)
    }
}

pub trait GrowableMapping<K, V>: Mapping<K, V> {
    /// Returns an empty mapping, which can be grown
    fn empty() -> Self;

    /// Tries to set the value of the element if the element is
    /// already in the set (false is returned). If not, the key is
    /// added to the mapping and true is returned.
    fn set_or_add(&mut self, key: K, value: V) -> Result<bool, AddError> {
        if self.contains_key(&key) {
            self.set(key, value);
            Ok(false)
        } else {
            self.add(key, value)?;
            Ok(true)
        }
    }

    /// Similar to [`set`], but adds a key to a mapping.
    /// Adding may fail due to the implementation being considered full, or
    /// the key already being in the set. Note that implementations *must* return
    /// the correct errors to be usable in a union find.
    fn add(&mut self, key: K, value: V) -> Result<(), AddError>;

    /// Gets the number of items currently in the mapping.
    fn len(&self) -> usize;
}

impl<K: Hash + Eq, V> Mapping<K, V> for HashMap<K, V> {
    fn get(&self, key: &K) -> Option<&V> {
        HashMap::get(self, key)
    }

    fn set(&mut self, key: K, value: V) {
        if self.insert(key, value).is_none() {
            panic!("can't set value of element which is not yet in mapping")
        }
    }
}

impl<K: Hash + Eq, V> GrowableMapping<K, V> for HashMap<K, V> {
    fn empty() -> Self {
        HashMap::new()
    }

    fn add(&mut self, key: K, value: V) -> Result<(), AddError> {
        if self.insert(key, value).is_some() {
            return Err(AddError::AlreadyIn);
        }
        Ok(())
    }

    fn len(&self) -> usize {
        HashMap::len(self)
    }
}

impl<K: Ord, V> Mapping<K, V> for BTreeMap<K, V> {
    fn get(&self, key: &K) -> Option<&V> {
        BTreeMap::get(self, key)
    }

    fn set(&mut self, key: K, value: V) {
        if self.insert(key, value).is_none() {
            panic!("can't set value of element which is not yet in mapping")
        }
    }
}

impl<K: Ord, V> GrowableMapping<K, V> for BTreeMap<K, V> {
    fn empty() -> Self {
        BTreeMap::new()
    }

    fn add(&mut self, key: K, value: V) -> Result<(), AddError> {
        if self.insert(key, value).is_some() {
            return Err(AddError::AlreadyIn);
        }
        Ok(())
    }

    fn len(&self) -> usize {
        BTreeMap::len(self)
    }
}

impl<V, const N: usize> Mapping<usize, V> for [V; N] {
    fn get(&self, key: &usize) -> Option<&V> {
        if *key < self.len() {
            Some(&self[*key])
        } else {
            None
        }
    }

    fn set(&mut self, key: usize, value: V) {
        if key < self.len() {
            self[key] = value;
        } else {
            panic!("can't set value of element which is not yet in mapping");
        }
    }
}

impl<V> Mapping<usize, V> for [V] {
    fn get(&self, key: &usize) -> Option<&V> {
        if *key < self.len() {
            Some(&self[*key])
        } else {
            None
        }
    }

    fn set(&mut self, key: usize, value: V) {
        if key < self.len() {
            self[key] = value;
        } else {
            panic!("can't set value of element which is not yet in mapping");
        }
    }
}

impl<V> Mapping<usize, V> for Vec<V> {
    fn get(&self, key: &usize) -> Option<&V> {
        if *key < self.len() {
            Some(&self[*key])
        } else {
            None
        }
    }

    fn set(&mut self, key: usize, value: V) {
        if key < self.len() {
            self[key] = value;
        } else {
            panic!("can't set value of element which is not yet in mapping");
        }
    }
}

impl<V> GrowableMapping<usize, V> for Vec<V> {
    fn empty() -> Self {
        Vec::new()
    }

    fn add(&mut self, key: usize, value: V) -> Result<(), AddError> {
        if key != self.len() {
            self.push(value);
            Ok(())
        } else {
            Err(AddError::NotInOrder)
        }
    }

    fn len(&self) -> usize {
        Vec::len(self)
    }
}

/// A wrapper for types that normally implement [`GrowableMapping`], but which
/// you want to force never to grow.
struct FixedSize<M>(M);

impl<M> Deref for FixedSize<M> {
    type Target = M;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<M> DerefMut for FixedSize<M> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<K, V, M> Mapping<K, V> for FixedSize<M>
where
    M: Mapping<K, V>,
{
    fn get(&self, key: &K) -> Option<&V> {
        self.0.get(key)
    }

    fn set(&mut self, key: K, value: V) {
        self.0.set(key, value);
    }
}
