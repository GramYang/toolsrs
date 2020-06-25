use ahash::RandomState;
use std::hash::{Hash, BuildHasher};
use std::fmt;
use std::borrow::Borrow;
use crate::chm::{HashMap, ConHashMap};
use crate::chm::t::Map;

/// A read-only view into a `ConHashMap`. Allows to obtain raw references to the stored values.
pub struct ReadOnlyView<K, V, S = RandomState> {
    map: ConHashMap<K, V, S>,
}

impl<K: Eq + Hash + Clone, V: Clone, S: Clone> Clone for ReadOnlyView<K, V, S> {
    fn clone(&self) -> Self {
        Self {
            map: self.map.clone(),
        }
    }
}

impl<K: Eq + Hash + fmt::Debug, V: fmt::Debug, S: BuildHasher + Clone> fmt::Debug
for ReadOnlyView<K, V, S>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.map.fmt(f)
    }
}

impl<K, V, S> ReadOnlyView<K, V, S> {
    #[inline]
    pub(crate) fn new(map: ConHashMap<K, V, S>) -> Self {
        Self { map }
    }

    /// Consumes this `ReadOnlyView`, returning the underlying `ConHashMap`.
    #[inline]
    pub fn into_inner(self) -> ConHashMap<K, V, S> {
        self.map
    }
}

impl<'a, K: 'a + Eq + Hash, V: 'a, S: BuildHasher + Clone> ReadOnlyView<K, V, S> {
    /// Returns the number of elements in the map.
    #[inline]
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Returns `true` if the map contains no elements.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Returns the number of elements the map can hold without reallocating.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.map.capacity()
    }

    /// Returns `true` if the map contains a value for the specified key.
    #[inline]
    pub fn contains_key<Q>(&'a self, key: &Q) -> bool
        where
            K: Borrow<Q>,
            Q: Hash + Eq + ?Sized,
    {
        let hash = self.map.hash_usize(&key);
        let idx = self.map.determine_shard(hash);

        let shard = unsafe { self.map._get_read_shard(idx) };
        shard.contains_key(key)
    }

    /// Returns a reference to the value corresponding to the key.
    #[inline]
    pub fn get<Q>(&'a self, key: &Q) -> Option<&'a V>
        where
            K: Borrow<Q>,
            Q: Hash + Eq + ?Sized,
    {
        let hash = self.map.hash_usize(&key);
        let idx = self.map.determine_shard(hash);

        let shard = unsafe { self.map._get_read_shard(idx) };
        shard.get(key).map(|v| v.get())
    }

    /// Returns the key-value pair corresponding to the supplied key.
    #[inline]
    pub fn get_key_value<Q>(&'a self, key: &Q) -> Option<(&'a K, &'a V)>
        where
            K: Borrow<Q>,
            Q: Hash + Eq + ?Sized,
    {
        let hash = self.map.hash_usize(&key);
        let idx = self.map.determine_shard(hash);

        let shard = unsafe { self.map._get_read_shard(idx) };
        shard.get_key_value(key).map(|(k, v)| (k, v.get()))
    }

    #[inline]
    fn shard_read_iter(&'a self) -> impl Iterator<Item = &'a HashMap<K, V, S>> + 'a {
        (0..self.map._shard_count())
            .map(move |shard_i| unsafe { self.map._get_read_shard(shard_i) })
    }

    /// An iterator visiting all key-value pairs in arbitrary order. The iterator element type is `(&'a K, &'a V)`.
    #[inline]
    pub fn iter(&'a self) -> impl Iterator<Item = (&'a K, &'a V)> + 'a {
        self.shard_read_iter()
            .flat_map(|shard| shard.iter())
            .map(|(k, v)| (k, v.get()))
    }

    /// An iterator visiting all keys in arbitrary order. The iterator element type is `&'a K`.
    #[inline]
    pub fn keys(&'a self) -> impl Iterator<Item = &'a K> + 'a {
        self.shard_read_iter().flat_map(|shard| shard.keys())
    }

    /// An iterator visiting all values in arbitrary order. The iterator element type is `&'a V`.
    #[inline]
    pub fn values(&'a self) -> impl Iterator<Item = &'a V> + 'a {
        self.shard_read_iter()
            .flat_map(|shard| shard.values())
            .map(|v| v.get())
    }
}

#[cfg(test)]
mod tests {
    use crate::chm::ConHashMap;

    fn construct_sample_map() -> ConHashMap<i32, String> {
        let map = ConHashMap::new();
        map.insert(1, "one".to_string());
        map.insert(10, "ten".to_string());
        map.insert(27, "twenty seven".to_string());
        map.insert(45, "forty five".to_string());
        map
    }

    #[test]
    fn test_properties() {
        let map = construct_sample_map();
        let view = map.clone().into_read_only();

        assert_eq!(view.is_empty(), map.is_empty());
        assert_eq!(view.len(), map.len());
        assert_eq!(view.capacity(), map.capacity());

        let new_map = view.into_inner();

        assert_eq!(new_map.is_empty(), map.is_empty());
        assert_eq!(new_map.len(), map.len());
        assert_eq!(new_map.capacity(), map.capacity());
    }

    #[test]
    fn test_get() {
        let map = construct_sample_map();
        let view = map.clone().into_read_only();

        for key in map.iter().map(|entry| *entry.key()) {
            assert!(view.contains_key(&key));

            let map_entry = map.get(&key).unwrap();
            assert_eq!(view.get(&key).unwrap(), map_entry.value());

            let key_value: (&i32, &String) = view.get_key_value(&key).unwrap();
            assert_eq!(key_value.0, map_entry.key());
            assert_eq!(key_value.1, map_entry.value());
        }
    }

    #[test]
    fn test_iters() {
        let map = construct_sample_map();
        let view = map.clone().into_read_only();

        let mut visited_items = Vec::new();
        for (key, value) in view.iter() {
            map.contains_key(key);

            let map_entry = map.get(&key).unwrap();
            assert_eq!(key, map_entry.key());
            assert_eq!(value, map_entry.value());

            visited_items.push((key, value));
        }

        let mut visited_keys = Vec::new();
        for key in view.keys() {
            map.contains_key(key);

            let map_entry = map.get(&key).unwrap();
            assert_eq!(key, map_entry.key());
            assert_eq!(view.get(key).unwrap(), map_entry.value());

            visited_keys.push(key);
        }

        let mut visited_values = Vec::new();
        for value in view.values() {
            visited_values.push(value);
        }

        for entry in map.iter() {
            let key = entry.key();
            let value = entry.value();

            assert!(visited_keys.contains(&key));
            assert!(visited_values.contains(&value));
            assert!(visited_items.contains(&(key, value)));
        }
    }
}