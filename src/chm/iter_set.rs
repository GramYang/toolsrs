use std::hash::{Hash, BuildHasher};
use crate::chm::t::Map;
use crate::chm::setref::multiple::RefMulti;

pub struct OwningIter<K, S> {
    inner: crate::chm::iter::OwningIter<K, (), S>,
}

impl<K: Eq + Hash, S: BuildHasher + Clone> OwningIter<K, S> {
    pub(crate) fn new(inner: crate::chm::iter::OwningIter<K, (), S>) -> Self {
        Self { inner }
    }
}

impl<K: Eq + Hash, S: BuildHasher + Clone> Iterator for OwningIter<K, S> {
    type Item = K;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(k, _)| k)
    }
}

unsafe impl<K, S> Send for OwningIter<K, S>
    where
        K: Eq + Hash + Send,
        S: BuildHasher + Clone + Send,
{
}

unsafe impl<K, S> Sync for OwningIter<K, S>
    where
        K: Eq + Hash + Sync,
        S: BuildHasher + Clone + Sync,
{
}

pub struct Iter<'a, K, S, M> {
    inner: crate::chm::iter::Iter<'a, K, (), S, M>,
}

unsafe impl<'a, 'i, K, S, M> Send for Iter<'i, K, S, M>
    where
        K: 'a + Eq + Hash + Send,
        S: 'a + BuildHasher + Clone,
        M: Map<'a, K, (), S>,
{
}

unsafe impl<'a, 'i, K, S, M> Sync for Iter<'i, K, S, M>
    where
        K: 'a + Eq + Hash + Sync,
        S: 'a + BuildHasher + Clone,
        M: Map<'a, K, (), S>,
{
}

impl<'a, K: 'a+Eq + Hash, S: 'a + BuildHasher + Clone, M: Map<'a, K, (), S>> Iter<'a, K, S, M> {
    pub(crate) fn new(inner: crate::chm::iter::Iter<'a, K, (), S, M>) -> Self {
        Self { inner }
    }
}

impl<'a, K: 'a+Eq + Hash, S: 'a + BuildHasher + Clone, M: Map<'a, K, (), S>> Iterator
for Iter<'a, K, S, M>
{
    type Item = RefMulti<'a, K, S>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(RefMulti::new)
    }
}