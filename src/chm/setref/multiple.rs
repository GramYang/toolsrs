use ahash::RandomState;
use crate::chm::mapref;
use std::hash::{Hash, BuildHasher};
use std::ops::Deref;

pub struct RefMulti<'a, K, S = RandomState> {
    inner: mapref::multiple::RefMulti<'a, K, (), S>,
}

impl<'a, K: Eq + Hash, S: BuildHasher> RefMulti<'a, K, S> {
    #[inline(always)]
    pub(crate) fn new(inner: mapref::multiple::RefMulti<'a, K, (), S>) -> Self {
        Self { inner }
    }
    #[inline(always)]
    pub fn key(&self) -> &K {
        self.inner.key()
    }
}

impl<'a, K: Eq + Hash, S: BuildHasher> Deref for RefMulti<'a, K, S> {
    type Target = K;
    #[inline(always)]
    fn deref(&self) -> &K {
        self.key()
    }
}