pub mod iter;
pub mod iter_set;
pub mod lock;
pub mod mapref;
pub mod setref;
mod read_only;
mod set;
mod t;
mod util;

use ahash::RandomState;
use std::hash::{Hash, BuildHasher, Hasher};
use std::borrow::Borrow;
use std::fmt::Debug;
use std::ops::{Shl, Shr, BitOr, Sub, BitAnd};
use std::iter::FromIterator;
use crate::chm::iter::{OwningIter, Iter, IterMut};
use crate::chm::util::SharedValue;
pub use crate::chm::read_only::ReadOnlyView;
use crate::chm::mapref::one::{Ref, RefMut};
use crate::chm::mapref::entry::{Entry, OccupiedEntry, VacantEntry};
use crate::chm::mapref::multiple::RefMulti;
use crate::chm::t::Map;
use crate::chm::lock::{RwLockWriteGuard, RwLockReadGuard, RwLock};

pub type HashMap<K,V,S> = std::collections::HashMap<K,SharedValue<V>,S>;

#[inline]
fn shard_amount() -> usize {
    (num_cpus::get() * 4).next_power_of_two()
}

#[inline]
fn ncb(shard_amount: usize) -> usize {
    shard_amount.trailing_zeros() as usize
}

/// 基于（抄袭）DashMap，替换RwLock<HashMap<K, V, S>>
pub struct ConHashMap<K,V,S=RandomState>{
    shift:usize,
    shards:Box<[RwLock<HashMap<K,V,S>>]>,
    hasher:S,
}

impl<K:Eq+Hash+Clone,V:Clone,S:Clone> Clone for ConHashMap<K,V,S>{
    fn clone(&self)->Self{
        let mut inner_shards=Vec::new();
        for shard in self.shards.iter(){
            let shard=shard.read();
            inner_shards.push(RwLock::new((*shard).clone()));
        }
        Self{
            shift:self.shift,
            shards:inner_shards.into_boxed_slice(),
            hasher:self.hasher.clone(),
        }
    }
}

impl<K,V,S> Default for ConHashMap<K,V,S>
where
    K:Eq+Hash, S:Default+BuildHasher+Clone,
{
    #[inline]
    fn default() ->Self{
        Self::with_hasher(Default::default())
    }
}

impl<'a,K:'a+Eq+Hash,V:'a> ConHashMap<K,V,RandomState>{
    ///创建一个0容量的ConHashMap
    #[inline]
    pub fn new()->Self{
        ConHashMap::with_hasher(RandomState::default())
    }

    ///指定容量创建ConHashMap
    #[inline]
    pub fn with_capacity(capacity:usize)->Self{
        ConHashMap::with_capacity_and_hasher(capacity, RandomState::default())
    }
}

impl<'a,K:'a+Eq+Hash,V:'a,S:BuildHasher+Clone> ConHashMap<K,V,S>{
    ///用ReadOnlyView包裹ConHashMap
    #[inline]
    pub fn into_read_only(self) ->ReadOnlyView<K,V,S>{
        ReadOnlyView::new(self)
    }

    ///创建一个新ConHashMap，容量为0，指定hasher
    #[inline]
    pub fn with_hasher(hasher:S)->Self{
        Self::with_capacity_and_hasher(0, hasher)
    }

    ///创建一个新ConHashMap，指定初始容量和hasher
    #[inline]
    pub fn with_capacity_and_hasher(mut capacity:usize,hasher:S)->Self{
        let shard_amount=shard_amount();
        let shift=util::ptr_size_bits()-ncb(shard_amount);
        if capacity!=0{
            capacity=(capacity+(shard_amount-1))&!(shard_amount-1);
        }
        let cps=capacity/shard_amount;
        let shards=(0..shard_amount).map(|_| RwLock::new(HashMap::with_capacity_and_hasher
            (cps,hasher.clone()))).collect();
        Self{
            shift,
            shards,
            hasher,
        }
    }

    ///返回item的hash值
    #[inline]
    pub fn hash_usize<T: Hash>(&self, item: &T) -> usize {
        let mut hasher = self.hasher.build_hasher();
        item.hash(&mut hasher);
        hasher.finish() as usize
    }

    #[allow(dead_code)]
    #[inline]
    pub(crate) fn shards(&self) -> &[RwLock<HashMap<K, V, S>>] {
        &self.shards
    }

    #[inline]
    pub(crate) fn determine_shard(&self, hash: usize) -> usize {
        // Leave the high 7 bits for the HashBrown SIMD tag.
        (hash << 7) >> self.shift
    }

    ///返回ConHashMap的hasher引用
    #[inline]
    pub fn hasher(&self) -> &S {
        &self.hasher
    }

    ///插入键值对，成功则返回插入值
    #[inline]
    pub fn insert(&self, key: K, value: V) -> Option<V> {
        self._insert(key, value)
    }

    ///移除键值对，成功则返回键值对
    #[inline]
    pub fn remove<Q>(&self, key: &Q) -> Option<(K, V)>
        where
            K: Borrow<Q>,
            Q: Hash + Eq + ?Sized,
    {
        self._remove(key)
    }

    ///移除键值对，成功则返回键值对，并且f返回true
    #[inline]
    pub fn remove_if<Q>(&self, key: &Q, f: impl FnOnce(&K, &V) -> bool) -> Option<(K, V)>
        where
            K: Borrow<Q>,
            Q: Hash + Eq + ?Sized,
    {
        self._remove_if(key, f)
    }

    ///创建迭代器产生不可变引用
    #[inline]
    pub fn iter(&'a self) -> Iter<'a, K, V, S, ConHashMap<K, V, S>> {
        self._iter()
    }

    ///创建迭代器产生可变引用
    #[inline]
    pub fn iter_mut(&'a self) -> IterMut<'a, K, V, S, ConHashMap<K, V, S>> {
        self._iter_mut()
    }

    ///返回一个entry的不可变引用
    #[inline]
    pub fn get<Q>(&'a self, key: &Q) -> Option<Ref<'a, K, V, S>>
        where
            K: Borrow<Q>,
            Q: Hash + Eq + ?Sized,
    {
        self._get(key)
    }

    ///返回一个entry的可变引用
    #[inline]
    pub fn get_mut<Q>(&'a self, key: &Q) -> Option<RefMut<'a, K, V, S>>
        where
            K: Borrow<Q>,
            Q: Hash + Eq + ?Sized,
    {
        self._get_mut(key)
    }

    ///移除空闲容量
    #[inline]
    pub fn shrink_to_fit(&self) {
        self._shrink_to_fit();
    }

    ///保留f返回true的元素，移除f返回false的元素
    #[inline]
    pub fn retain(&self, f: impl FnMut(&K, &mut V) -> bool) {
        self._retain(f);
    }

    ///返回键值对总数
    #[inline]
    pub fn len(&self) -> usize {
        self._len()
    }

    ///判空
    #[inline]
    pub fn is_empty(&self) -> bool {
        self._is_empty()
    }

    ///清空
    #[inline]
    pub fn clear(&self) {
        self._clear();
    }

    ///返回当前容量
    #[inline]
    pub fn capacity(&self) -> usize {
        self._capacity()
    }

    ///使用f修改key对应的value
    #[inline]
    pub fn alter<Q>(&self, key: &Q, f: impl FnOnce(&K, V) -> V)
        where
            K: Borrow<Q>,
            Q: Hash + Eq + ?Sized,
    {
        self._alter(key, f);
    }

    ///使用f修改所有value
    #[inline]
    pub fn alter_all(&self, f: impl FnMut(&K, V) -> V) {
        self._alter_all(f);
    }

    ///判断map内是否包含指定key
    #[inline]
    pub fn contains_key<Q>(&self, key: &Q) -> bool
        where
            K: Borrow<Q>,
            Q: Hash + Eq + ?Sized,
    {
        self._contains_key(key)
    }

    ///返回Entry
    #[inline]
    pub fn entry(&'a self, key: K) -> Entry<'a, K, V, S> {
        self._entry(key)
    }
}

impl<'a,K:'a+Eq+Hash,V:'a,S:'a+BuildHasher+Clone> Map<'a,K,V,S> for ConHashMap<K,V,S>{
    #[inline]
    fn _shard_count(&self) -> usize {
        self.shards.len()
    }

    #[inline]
    unsafe fn _get_read_shard(&'a self, i: usize) -> &'a HashMap<K, V, S> {
        debug_assert!(i < self.shards.len());
        self.shards.get_unchecked(i).get()
    }

    #[inline]
    unsafe fn _yield_read_shard(&'a self, i: usize) -> RwLockReadGuard<'a, HashMap<K, V, S>> {
        debug_assert!(i < self.shards.len());
        self.shards.get_unchecked(i).read()
    }

    #[inline]
    unsafe fn _yield_write_shard(&'a self, i: usize) -> RwLockWriteGuard<'a, HashMap<K, V, S>> {
        debug_assert!(i < self.shards.len());
        self.shards.get_unchecked(i).write()
    }

    #[inline]
    fn _insert(&self, key: K, value: V) -> Option<V> {
        let hash = self.hash_usize(&key);
        let idx = self.determine_shard(hash);
        let mut shard = unsafe { self._yield_write_shard(idx) };
        shard
            .insert(key, SharedValue::new(value))
            .map(|v| v.into_inner())
    }

    #[inline]
    fn _remove<Q>(&self, key: &Q) -> Option<(K, V)>
        where
            K: Borrow<Q>,
            Q: Hash + Eq + ?Sized,
    {
        let hash = self.hash_usize(&key);
        let idx = self.determine_shard(hash);
        let mut shard = unsafe { self._yield_write_shard(idx) };
        shard.remove_entry(key).map(|(k, v)| (k, v.into_inner()))
    }

    #[inline]
    fn _remove_if<Q>(&self, key: &Q, f: impl FnOnce(&K, &V) -> bool) -> Option<(K, V)>
        where
            K: Borrow<Q>,
            Q: Hash + Eq + ?Sized,
    {
        let hash = self.hash_usize(&key);
        let idx = self.determine_shard(hash);
        let mut shard = unsafe { self._yield_write_shard(idx) };
        if let Some((k, v)) = shard.get_key_value(key) {
            if f(k, v.get()) {
                shard.remove_entry(key).map(|(k, v)| (k, v.into_inner()))
            } else {
                None
            }
        } else {
            None
        }
    }

    #[inline]
    fn _iter(&'a self) -> Iter<'a, K, V, S, ConHashMap<K, V, S>> {
        Iter::new(self)
    }

    #[inline]
    fn _iter_mut(&'a self) -> IterMut<'a, K, V, S, ConHashMap<K, V, S>> {
        IterMut::new(self)
    }

    #[inline]
    fn _get<Q>(&'a self, key: &Q) -> Option<Ref<'a, K, V, S>>
        where
            K: Borrow<Q>,
            Q: Hash + Eq + ?Sized,
    {
        let hash = self.hash_usize(&key);
        let idx = self.determine_shard(hash);
        let shard = unsafe { self._yield_read_shard(idx) };
        if let Some((kptr, vptr)) = shard.get_key_value(key) {
            unsafe {
                let kptr = util::change_lifetime_const(kptr);
                let vptr = util::change_lifetime_const(vptr);
                Some(Ref::new(shard, kptr, vptr.get()))
            }
        } else {
            None
        }
    }

    #[inline]
    fn _get_mut<Q>(&'a self, key: &Q) -> Option<RefMut<'a, K, V, S>>
        where
            K: Borrow<Q>,
            Q: Hash + Eq + ?Sized,
    {
        let hash = self.hash_usize(&key);
        let idx = self.determine_shard(hash);
        let shard = unsafe { self._yield_write_shard(idx) };
        if let Some((kptr, vptr)) = shard.get_key_value(key) {
            unsafe {
                let kptr = util::change_lifetime_const(kptr);
                let vptr = &mut *vptr.as_ptr();
                Some(RefMut::new(shard, kptr, vptr))
            }
        } else {
            None
        }
    }

    #[inline]
    fn _shrink_to_fit(&self) {
        self.shards.iter().for_each(|s| s.write().shrink_to_fit());
    }

    #[inline]
    fn _retain(&self, mut f: impl FnMut(&K, &mut V) -> bool) {
        self.shards
            .iter()
            .for_each(|s| s.write().retain(|k, v| f(k, v.get_mut())));
    }

    #[inline]
    fn _len(&self) -> usize {
        self.shards.iter().map(|s| s.read().len()).sum()
    }

    #[inline]
    fn _capacity(&self) -> usize {
        self.shards.iter().map(|s| s.read().capacity()).sum()
    }

    #[inline]
    fn _alter<Q>(&self, key: &Q, f: impl FnOnce(&K, V) -> V)
        where
            K: Borrow<Q>,
            Q: Hash + Eq + ?Sized,
    {
        if let Some(mut r) = self.get_mut(key) {
            util::map_in_place_2(r.pair_mut(), f);
        }
    }

    #[inline]
    fn _alter_all(&self, mut f: impl FnMut(&K, V) -> V) {
        self.shards.iter().for_each(|s| {
            s.write()
                .iter_mut()
                .for_each(|(k, v)| util::map_in_place_2((k, v.get_mut()), &mut f));
        });
    }

    #[inline]
    fn _entry(&'a self, key: K) -> Entry<'a, K, V, S> {
        let hash = self.hash_usize(&key);
        let idx = self.determine_shard(hash);
        let shard = unsafe { self._yield_write_shard(idx) };
        if let Some((kptr, vptr)) = shard.get_key_value(&key) {
            unsafe {
                let kptr = util::change_lifetime_const(kptr);
                let vptr = &mut *vptr.as_ptr();
                Entry::Occupied(OccupiedEntry::new(shard, Some(key), (kptr, vptr)))
            }
        } else {
            Entry::Vacant(VacantEntry::new(shard, key))
        }
    }

    #[inline]
    fn _hasher(&self) -> S {
        self.hasher.clone()
    }
}

impl<K:Eq+Hash+Debug,V:Debug,S:BuildHasher+Clone> Debug for ConHashMap<K,V,S>{
    fn fmt(&self, f:&mut std::fmt::Formatter<'_>)->std::fmt::Result{
        let mut pmap=f.debug_map();
        for r in self{
            let (k,v)= r.pair();
            pmap.entry(k,v);
        }
        pmap.finish()
    }
}

impl<'a, K: 'a + Eq + Hash, V: 'a, S: BuildHasher + Clone> Shl<(K, V)> for &'a ConHashMap<K, V, S> {
    type Output = Option<V>;

    #[inline]
    fn shl(self, pair: (K, V)) -> Self::Output {
        self.insert(pair.0, pair.1)
    }
}

impl<'a, K: 'a + Eq + Hash, V: 'a, S: BuildHasher + Clone, Q> Shr<&Q> for &'a ConHashMap<K, V, S>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
{
    type Output = Ref<'a, K, V, S>;

    #[inline]
    fn shr(self, key: &Q) -> Self::Output {
        self.get(key).unwrap()
    }
}

impl<'a, K: 'a + Eq + Hash, V: 'a, S: BuildHasher + Clone, Q> BitOr<&Q> for &'a ConHashMap<K, V, S>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
{
    type Output = RefMut<'a, K, V, S>;

    #[inline]
    fn bitor(self, key: &Q) -> Self::Output {
        self.get_mut(key).unwrap()
    }
}

impl<'a, K: 'a + Eq + Hash, V: 'a, S: BuildHasher + Clone, Q> Sub<&Q> for &'a ConHashMap<K, V, S>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
{
    type Output = Option<(K, V)>;

    #[inline]
    fn sub(self, key: &Q) -> Self::Output {
        self.remove(key)
    }
}

impl<'a, K: 'a + Eq + Hash, V: 'a, S: BuildHasher + Clone, Q> BitAnd<&Q> for &'a ConHashMap<K, V, S>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
{
    type Output = bool;

    #[inline]
    fn bitand(self, key: &Q) -> Self::Output {
        self.contains_key(key)
    }
}

impl<'a, K: Eq + Hash, V, S: BuildHasher + Clone> IntoIterator for ConHashMap<K, V, S> {
    type Item = (K, V);
    type IntoIter = OwningIter<K, V, S>;

    fn into_iter(self) -> Self::IntoIter {
        OwningIter::new(self)
    }
}

impl<'a, K: Eq + Hash, V, S: BuildHasher + Clone> IntoIterator for &'a ConHashMap<K, V, S> {
    type Item = RefMulti<'a, K, V, S>;
    type IntoIter = Iter<'a, K, V, S, ConHashMap<K, V, S>>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<K: Eq + Hash, V, S: BuildHasher + Clone> Extend<(K, V)> for ConHashMap<K, V, S> {
    fn extend<I: IntoIterator<Item = (K, V)>>(&mut self, intoiter: I) {
        for pair in intoiter.into_iter() {
            self.insert(pair.0, pair.1);
        }
    }
}

impl<K: Eq + Hash, V> FromIterator<(K, V)> for ConHashMap<K, V, RandomState> {
    fn from_iter<I: IntoIterator<Item = (K, V)>>(intoiter: I) -> Self {
        let mut map = ConHashMap::new();
        map.extend(intoiter);
        map
    }
}

#[cfg(test)]
mod tests {
    use crate::chm::ConHashMap;
    use ahash::RandomState;

    #[test]
    fn test_basic() {
        let dm = ConHashMap::new();
        dm.insert(0, 0);
        assert_eq!(dm.get(&0).unwrap().value(), &0);
    }

    #[test]
    fn test_default() {
        let dm: ConHashMap<u32, u32> = ConHashMap::default();
        dm.insert(0, 0);
        assert_eq!(dm.get(&0).unwrap().value(), &0);
    }

    #[test]
    fn test_multiple_hashes() {
        let dm: ConHashMap<u32, u32> = ConHashMap::default();
        for i in 0..100 {
            dm.insert(0, i);
            dm.insert(i, i);
        }
        for i in 1..100 {
            let r = dm.get(&i).unwrap();
            assert_eq!(i, *r.value());
            assert_eq!(i, *r.key());
        }
        let r = dm.get(&0).unwrap();
        assert_eq!(99, *r.value());
    }

    #[test]
    fn test_more_complex_values() {
        #[derive(Hash, PartialEq, Debug, Clone)]
        struct T0 {
            s: String,
            u: u8,
        }
        let dm = ConHashMap::new();
        let range = 0..10;
        for i in range {
            let t = T0 {
                s: i.to_string(),
                u: i as u8,
            };
            dm.insert(i, t.clone());
            assert_eq!(&t, dm.get(&i).unwrap().value());
        }
    }

    #[test]
    fn test_different_hashers_randomstate() {
        let dm_hm_default: ConHashMap<u32, u32, RandomState> =
            ConHashMap::with_hasher(RandomState::new());
        for i in 0..10 {
            dm_hm_default.insert(i, i);
            assert_eq!(i, *dm_hm_default.get(&i).unwrap().value());
        }
    }
}