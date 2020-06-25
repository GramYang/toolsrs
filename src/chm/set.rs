use ahash::RandomState;
use std::hash::{Hash, BuildHasher};
use std::fmt;
use std::borrow::Borrow;
use crate::chm::iter_set::{Iter, OwningIter};
use std::iter::FromIterator;
use crate::chm::setref::one::Ref;
use crate::chm::ConHashMap;

///ConHashSet是一个ConHashMap的封装，其值为()，其使用的方法和类型是set的。
pub struct ConHashSet<K, S = RandomState> {
    inner: ConHashMap<K, (), S>,
}

impl<K: Eq + Hash + fmt::Debug, S: BuildHasher + Clone> fmt::Debug for ConHashSet<K, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.inner, f)
    }
}

impl<K: Eq + Hash + Clone, S: Clone> Clone for ConHashSet<K, S> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }

    fn clone_from(&mut self, source: &Self) {
        self.inner.clone_from(&source.inner)
    }
}

impl<K, S> Default for ConHashSet<K, S>
    where
        K: Eq + Hash,
        S: Default + BuildHasher + Clone,
{
    #[inline]
    fn default() -> Self {
        Self::with_hasher(Default::default())
    }
}

impl<'a, K: 'a + Eq + Hash> ConHashSet<K, RandomState> {
    /// 创建一个新的0容量ConHashSet
    #[inline]
    pub fn new() -> Self {
        Self::with_hasher(RandomState::default())
    }


    /// 创建一个新的指定容量ConHashSet
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_and_hasher(capacity, RandomState::default())
    }
}

impl<'a, K: 'a + Eq + Hash, S: BuildHasher + Clone> ConHashSet<K, S> {
    /// 创建一个新的0容量ConHashSet，指定hasher
    #[inline]
    pub fn with_hasher(hasher: S) -> Self {
        Self::with_capacity_and_hasher(0, hasher)
    }

    /// 创建一个新的指定容量ConHashSet，指定hasher
    #[inline]
    pub fn with_capacity_and_hasher(capacity: usize, hasher: S) -> Self {
        Self {
            inner: ConHashMap::with_capacity_and_hasher(capacity, hasher),
        }
    }

    /// 将一个item输出其hash值
    #[inline]
    pub fn hash_usize<T: Hash>(&self, item: &T) -> usize {
        self.inner.hash_usize(item)
    }

    /// set中插入key，如果插入成功返回true
    #[inline]
    pub fn insert(&self, key: K) -> bool {
        self.inner.insert(key, ()).is_none()
    }

    /// map中移除一个entry，如果map中存在此entry则返回key
    #[inline]
    pub fn remove<Q>(&self, key: &Q) -> Option<K>
        where
            K: Borrow<Q>,
            Q: Hash + Eq + ?Sized,
    {
        self.inner.remove(key).map(|(k, _)| k)
    }

    /// set中移除一个entry，如果该entry存在并且f返回true则返回key
    #[inline]
    pub fn remove_if<Q>(&self, key: &Q, f: impl FnOnce(&K) -> bool) -> Option<K>
        where
            K: Borrow<Q>,
            Q: Hash + Eq + ?Sized,
    {
        // TODO: Don't create another closure around f
        self.inner.remove_if(key, |k, _| f(k)).map(|(k, _)| k)
    }

    /// map创建一个迭代器产生不可变引用
    #[inline]
    pub fn iter(&'a self) -> Iter<'a, K, S, ConHashMap<K, (), S>> {
        let iter = self.inner.iter();
        Iter::new(iter)
    }

    /// 返回set中一个entry的引用
    #[inline]
    pub fn get<Q>(&'a self, key: &Q) -> Option<Ref<'a, K, S>>
        where
            K: Borrow<Q>,
            Q: Hash + Eq + ?Sized,
    {
        self.inner.get(key).map(Ref::new)
    }

    /// 移除空闲容量
    #[inline]
    pub fn shrink_to_fit(&self) {
        self.inner.shrink_to_fit()
    }

    /// f返回true的元素保留，f返回false的元素删除
    #[inline]
    pub fn retain(&self, mut f: impl FnMut(&K) -> bool) {
        // TODO: Don't create another closure
        self.inner.retain(|k, _| f(k))
    }

    /// 获取set中存储key的总数
    #[inline]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// 判空
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// 清空set
    #[inline]
    pub fn clear(&self) {
        self.inner.clear()
    }

    /// 返回当前容量
    #[inline]
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    /// 判断set是否包含key
    #[inline]
    pub fn contains<Q>(&self, key: &Q) -> bool
        where
            K: Borrow<Q>,
            Q: Hash + Eq + ?Sized,
    {
        self.inner.contains_key(key)
    }
}

impl<'a, K: Eq + Hash, S: BuildHasher + Clone> IntoIterator for ConHashSet<K, S> {
    type Item = K;
    type IntoIter = OwningIter<K, S>;

    fn into_iter(self) -> Self::IntoIter {
        OwningIter::new(self.inner.into_iter())
    }
}

impl<K: Eq + Hash, S: BuildHasher + Clone> Extend<K> for ConHashSet<K, S> {
    fn extend<T: IntoIterator<Item = K>>(&mut self, iter: T) {
        let iter = iter.into_iter().map(|k| (k, ()));
        self.inner.extend(iter)
    }
}

impl<K: Eq + Hash> FromIterator<K> for ConHashSet<K, RandomState> {
    fn from_iter<I: IntoIterator<Item = K>>(iter: I) -> Self {
        let mut set = ConHashSet::new();
        set.extend(iter);
        set
    }
}

#[cfg(test)]
mod tests {
    use crate::chm::set::ConHashSet;

    #[test]
    fn test_basic() {
        let set = ConHashSet::new();
        set.insert(0);
        assert_eq!(set.get(&0).as_deref(), Some(&0));
    }

    #[test]
    fn test_default() {
        let set: ConHashSet<u32> = ConHashSet::default();
        set.insert(0);
        assert_eq!(set.get(&0).as_deref(), Some(&0));
    }

    #[test]
    fn test_multiple_hashes() {
        let set = ConHashSet::<u32>::default();
        for i in 0..100 {
            assert!(set.insert(i));
        }
        for i in 0..100 {
            assert!(!set.insert(i));
        }
        for i in 0..100 {
            assert_eq!(Some(i), set.remove(&i));
        }
        for i in 0..100 {
            assert_eq!(None, set.remove(&i));
        }
    }
}