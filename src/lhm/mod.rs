use std::collections::{hash_map, HashMap};
use std::hash::{Hash, Hasher, BuildHasher};
use std::{mem, ptr, marker, iter, fmt};
use std::borrow::Borrow;
use std::ops::{IndexMut, Index};
use std::cmp::Ordering;

mod heapsize;
mod test;

struct KeyRef<K> { k: *const K }

struct Node<K, V> {
    next: *mut Node<K, V>,
    prev: *mut Node<K, V>,
    key: K,
    value: V,
}

/// A linked hash map.
pub struct LinkedHashMap<K, V, S = hash_map::RandomState> {
    map: HashMap<KeyRef<K>, *mut Node<K, V>, S>,
    head: *mut Node<K, V>,
    free: *mut Node<K, V>,
}

impl<K: Hash> Hash for KeyRef<K> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        unsafe { (*self.k).hash(state) }
    }
}

impl<K: PartialEq> PartialEq for KeyRef<K> {
    fn eq(&self, other: &Self) -> bool {
        unsafe{ (*self.k).eq(&*other.k) }
    }
}

impl<K: Eq> Eq for KeyRef<K> {}

// This type exists only to support borrowing `KeyRef`s, which cannot be borrowed to `Q` directly
// due to conflicting implementations of `Borrow`. The layout of `&Qey<Q>` must be identical to
// `&Q` in order to support transmuting in the `Qey::from_ref` method.
#[derive(Hash, PartialEq, Eq)]
struct Qey<Q: ?Sized>(Q);

impl<Q: ?Sized> Qey<Q> {
    fn from_ref(q: &Q) -> &Self { unsafe { mem::transmute(q) } }
}

//配合hashmap的get，其key值可以是指定key的borrow返回值
impl<K, Q: ?Sized> Borrow<Qey<Q>> for KeyRef<K> where K: Borrow<Q> {
    fn borrow(&self) -> &Qey<Q> {
        Qey::from_ref(unsafe { (*self.k).borrow() })
    }
}

impl<K, V> Node<K, V> {
    fn new(k: K, v: V) -> Self {
        Node {
            key: k,
            value: v,
            next: ptr::null_mut(),
            prev: ptr::null_mut(),
        }
    }
}

unsafe fn drop_empty_node<K, V>(the_box: *mut Node<K, V>) {
    // Prevent compiler from trying to drop the un-initialized key and values in the node.
    let Node { key, value, .. } = *Box::from_raw(the_box);
    mem::forget(key);
    mem::forget(value);
}

impl<K: Hash + Eq, V> LinkedHashMap<K, V> {
    /// 创建一个新的linked hash map。
    pub fn new() -> Self { Self::with_map(HashMap::new()) }

    /// Creates an empty linked hash map with the given initial capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_map(HashMap::with_capacity(capacity))
    }
}

impl<K, V, S> LinkedHashMap<K, V, S> {
    //链表删除该node
    #[inline]
    fn detach(&mut self, node: *mut Node<K, V>) {
        unsafe {
            (*(*node).prev).next = (*node).next;
            (*(*node).next).prev = (*node).prev;
        }
    }

    //将该node添加到head后面
    #[inline]
    fn attach(&mut self, node: *mut Node<K, V>) {
        unsafe {
            (*node).next = (*self.head).next;
            (*node).prev = self.head;
            (*self.head).next = node;
            (*(*node).next).prev = node;
        }
    }

    // Caller must check `!self.head.is_null()`
    unsafe fn drop_entries(&mut self) {
        let mut cur = (*self.head).next;
        while cur != self.head {
            let next = (*cur).next;
            Box::from_raw(cur);
            cur = next;
        }
    }

    fn clear_free_list(&mut self) {
        unsafe {
            let mut free = self.free;
            while ! free.is_null() {
                let next_free = (*free).next;
                drop_empty_node(free);
                free = next_free;
            }
            self.free = ptr::null_mut();
        }
    }

    //先初始化head
    fn ensure_guard_node(&mut self) {
        if self.head.is_null() {
            //初始化head，包括其next和prev
            unsafe {
                let node_layout = std::alloc::Layout::new::<Node<K, V>>();
                self.head =  std::alloc::alloc(node_layout) as *mut Node<K, V>;
                (*self.head).next = self.head;
                (*self.head).prev = self.head;
            }
        }
    }
}

impl<K: Hash + Eq, V, S: BuildHasher> LinkedHashMap<K, V, S> {
    fn with_map(map: HashMap<KeyRef<K>, *mut Node<K, V>, S>) -> Self {
        LinkedHashMap {
            map,
            head: ptr::null_mut(),
            free: ptr::null_mut(),
        }
    }

    /// Creates an empty linked hash map with the given initial hash builder.
    pub fn with_hasher(hash_builder: S) -> Self {
        Self::with_map(HashMap::with_hasher(hash_builder))
    }

    /// Creates an empty linked hash map with the given initial capacity and hash builder.
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self {
        Self::with_map(HashMap::with_capacity_and_hasher(capacity, hash_builder))
    }

    /// Reserves capacity for at least `additional` more elements to be inserted into the map. The
    /// map may reserve more space to avoid frequent allocations.
    ///
    /// # Panics
    ///
    /// Panics if the new allocation size overflows `usize.`
    pub fn reserve(&mut self, additional: usize) { self.map.reserve(additional); }

    /// Shrinks the capacity of the map as much as possible. It will drop down as much as possible
    /// while maintaining the internal rules and possibly leaving some space in accordance with the
    /// resize policy.
    pub fn shrink_to_fit(&mut self) {
        self.map.shrink_to_fit();
        self.clear_free_list();
    }

    /// 根据key返回entry，entry包含Node的可变引用，self的裸指针
    pub fn entry(&mut self, k: K) -> Entry<K, V, S> {
        let self_ptr: *mut Self = self;

        if let Some(entry) = self.map.get_mut(&KeyRef{k: &k}) {
            return Entry::Occupied(OccupiedEntry {
                entry: *entry,
                map: self_ptr,
                marker: marker::PhantomData,
            });
        }

        Entry::Vacant(VacantEntry {
            key: k,
            map: self,
        })
    }

    /// 返回一个迭代器访问所有的entry，以插入顺序，迭代器的元素类型为OccupiedEntry<K, V, S>，允许移除和替换entry
    pub fn entries(&mut self) -> Entries<K, V, S> {
        //返回head的prev节点
        let head = if ! self.head.is_null() {
            unsafe { (*self.head).prev }
        } else {
            ptr::null_mut()
        };
        Entries {
            map: self,
            head: head,
            remaining: self.len(),
            marker: marker::PhantomData,
        }
    }

    /// 插入一个键值对，如果键存在，返回旧值
    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        //初始化head
        self.ensure_guard_node();
        //从map中取值，返回插入键值对Node裸指针和旧值
        let (node, old_val) = match self.map.get(&KeyRef{k: &k}) {
            Some(node) => {
                let old_val = unsafe { ptr::replace(&mut (**node).value, v) };
                (*node, Some(old_val))
            }
            None => {
                let node = if self.free.is_null() {
                    //用Box存入堆，再返回裸指针
                    Box::into_raw(Box::new(Node::new(k, v)))
                } else {
                    //free的头写入键值对Node裸指针，在堆上，然后返回这个头
                    unsafe {
                        let free = self.free;
                        self.free = (*free).next;
                        ptr::write(free, Node::new(k, v));
                        free
                    }
                };
                (node, None)
            }
        };
        match old_val {
            Some(_) => {
                //将该node从原链表删除，添加到head后面
                self.detach(node);
                self.attach(node);
            }
            None => {
                //存入map，node添加到head后面
                let keyref = unsafe { &(*node).key };
                self.map.insert(KeyRef{k: keyref}, node);
                self.attach(node);
            }
        }
        old_val
    }

    /// Checks if the map contains the given key.
    pub fn contains_key<Q: ?Sized>(&self, k: &Q) -> bool where K: Borrow<Q>, Q: Eq + Hash {
        self.map.contains_key(Qey::from_ref(k))
    }

    /// 根据key取值
    pub fn get<Q: ?Sized>(&self, k: &Q) -> Option<&V> where K: Borrow<Q>, Q: Eq + Hash {
        self.map.get(Qey::from_ref(k)).map(|e| unsafe { &(**e).value })
    }

    /// 根据key获取对应值的可变引用
    pub fn get_mut<Q: ?Sized>(&mut self, k: &Q) -> Option<&mut V> where K: Borrow<Q>, Q: Eq + Hash {
        self.map.get(Qey::from_ref(k)).map(|e| unsafe { &mut (**e).value })
    }

    /// 根据key返回对应值的可变引用，如果找到值，则将其移动到链表head后部。该函数可以用来实现LRU缓存。
    pub fn get_refresh<Q: ?Sized>(&mut self, k: &Q) -> Option<&mut V> where K: Borrow<Q>, Q: Eq + Hash {
        let (value, node_ptr_opt) = match self.map.get(Qey::from_ref(k)) {
            None => (None, None),
            Some(node) => {
                (Some(unsafe { &mut (**node).value }), Some(*node))
            }
        };
        if let Some(node_ptr) = node_ptr_opt {
            self.detach(node_ptr);
            self.attach(node_ptr);
        }
        value
    }

    /// 移除并返回key对应的值
    pub fn remove<Q: ?Sized>(&mut self, k: &Q) -> Option<V> where K: Borrow<Q>, Q: Eq + Hash {
        let removed = self.map.remove(Qey::from_ref(k));
        removed.map(|node| {
            self.detach(node);
            unsafe {
                //添加到free前
                (*node).next = self.free;
                self.free = node;
                // drop the key and return the value
                drop(ptr::read(&(*node).key));
                ptr::read(&(*node).value)
            }
        })
    }

    /// 返回map当前的键值对数最大值
    pub fn capacity(&self) -> usize {
        self.map.capacity()
    }

    /// 移除第一个entry并返回，可以用来实现LRU缓存
    #[inline]
    pub fn pop_front(&mut self) -> Option<(K, V)> {
        if self.is_empty() {
            return None
        }
        let lru = unsafe { (*self.head).prev };
        self.detach(lru);
        self.map
            .remove(&KeyRef{k: unsafe { &(*lru).key }})
            .map(|e| {
                let e = *unsafe { Box::from_raw(e) };
                (e.key, e.value)
            })
    }

    /// 获取第一个entry，不删除
    #[inline]
    pub fn front(&self) -> Option<(&K, &V)> {
        if self.is_empty() {
            return None
        }
        let lru = unsafe { (*self.head).prev };
        self.map
            .get(&KeyRef{k: unsafe { &(*lru).key }})
            .map(|e| unsafe { (&(**e).key, &(**e).value) })
    }

    /// 移除最后一个entry并返回
    #[inline]
    pub fn pop_back(&mut self) -> Option<(K, V)> {
        if self.is_empty() {
            return None
        }
        let mru = unsafe { (*self.head).next };
        self.detach(mru);
        self.map
            .remove(&KeyRef{k: unsafe { &(*mru).key }})
            .map(|e| {
                let e = *unsafe { Box::from_raw(e) };
                (e.key, e.value)
            })
    }

    /// 获取最后一个entry，不删除
    #[inline]
    pub fn back(&mut self) -> Option<(&K, &V)> {
        if self.is_empty() {
            return None
        }
        let mru = unsafe { (*self.head).next };
        self.map
            .get(&KeyRef{k: unsafe { &(*mru).key }})
            .map(|e| unsafe { (&(**e).key, &(**e).value) })
    }

    /// Returns the number of key-value pairs in the map.
    pub fn len(&self) -> usize { self.map.len() }

    /// Returns whether the map is currently empty.
    pub fn is_empty(&self) -> bool { self.len() == 0 }

    /// Returns a reference to the map's hasher.
    pub fn hasher(&self) -> &S {
        self.map.hasher()
    }

    /// Clears the map of all key-value pairs.
    pub fn clear(&mut self) {
        self.map.clear();
        // update the guard node if present
        if ! self.head.is_null() {
            unsafe {
                self.drop_entries();
                (*self.head).prev = self.head;
                (*self.head).next = self.head;
            }
        }
    }

    /// Returns a double-ended iterator visiting all key-value pairs in order of insertion.
    /// Iterator element type is `(&'a K, &'a V)`
    pub fn iter(&self) -> Iter<K, V> {
        let head = if self.head.is_null() {
            ptr::null_mut()
        } else {
            unsafe { (*self.head).prev }
        };
        Iter {
            head: head,
            tail: self.head,
            remaining: self.len(),
            marker: marker::PhantomData,
        }
    }

    /// Returns a double-ended iterator visiting all key-value pairs in order of insertion.
    /// Iterator element type is `(&'a K, &'a mut V)`
    pub fn iter_mut(&mut self) -> IterMut<K, V> {
        let head = if self.head.is_null() {
            ptr::null_mut()
        } else {
            unsafe { (*self.head).prev }
        };
        IterMut {
            head: head,
            tail: self.head,
            remaining: self.len(),
            marker: marker::PhantomData,
        }
    }

    /// Returns a double-ended iterator visiting all key in order of insertion.
    pub fn keys(&self) -> Keys<K, V> {
        Keys { inner: self.iter() }
    }

    /// Returns a double-ended iterator visiting all values in order of insertion.
    pub fn values(&self) -> Values<K, V> {
        Values { inner: self.iter() }
    }
}

//下标寻址，调用get
impl<'a, K, V, S, Q: ?Sized> Index<&'a Q> for LinkedHashMap<K, V, S>
    where K: Hash + Eq + Borrow<Q>, S: BuildHasher, Q: Eq + Hash
{
    type Output = V;

    fn index(&self, index: &'a Q) -> &V {
        self.get(index).expect("no entry found for key")
    }
}

//下标寻址和修改，调用get_mut
impl<'a, K, V, S, Q: ?Sized> IndexMut<&'a Q> for LinkedHashMap<K, V, S>
    where K: Hash + Eq + Borrow<Q>, S: BuildHasher, Q: Eq + Hash
{
    fn index_mut(&mut self, index: &'a Q) -> &mut V {
        self.get_mut(index).expect("no entry found for key")
    }
}

impl<K: Hash + Eq + Clone, V: Clone, S: BuildHasher + Clone> Clone for LinkedHashMap<K, V, S> {
    fn clone(&self) -> Self {
        let mut map = Self::with_hasher(self.map.hasher().clone());
        map.extend(self.iter().map(|(k, v)| (k.clone(), v.clone())));
        map
    }
}

impl<K: Hash + Eq, V, S: BuildHasher + Default> Default for LinkedHashMap<K, V, S> {
    fn default() -> Self { Self::with_hasher(S::default()) }
}

impl<K: Hash + Eq, V, S: BuildHasher> Extend<(K, V)> for LinkedHashMap<K, V, S> {
    fn extend<I: IntoIterator<Item=(K, V)>>(&mut self, iter: I) {
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

impl<'a, K, V, S> Extend<(&'a K, &'a V)> for LinkedHashMap<K, V, S>
    where K: 'a + Hash + Eq + Copy, V: 'a + Copy, S: BuildHasher,
{
    fn extend<I: IntoIterator<Item = (&'a K, &'a V)>>(&mut self, iter: I) {
        for (&k, &v) in iter {
            self.insert(k, v);
        }
    }
}

impl<K: Hash + Eq, V, S: BuildHasher + Default> iter::FromIterator<(K, V)> for LinkedHashMap<K, V, S> {
    fn from_iter<I: IntoIterator<Item=(K, V)>>(iter: I) -> Self {
        let iter = iter.into_iter();
        let mut map = Self::with_capacity_and_hasher(iter.size_hint().0, S::default());
        map.extend(iter);
        map
    }
}

impl<A: fmt::Debug + Hash + Eq, B: fmt::Debug, S: BuildHasher> fmt::Debug for LinkedHashMap<A, B, S> {
    /// Returns a string that lists the key-value pairs in insertion order.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_map().entries(self).finish()
    }
}

impl<K: Hash + Eq, V: PartialEq, S: BuildHasher> PartialEq for LinkedHashMap<K, V, S> {
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.iter().eq(other)
    }
}

impl<K: Hash + Eq, V: Eq, S: BuildHasher> Eq for LinkedHashMap<K, V, S> {}

impl<K: Hash + Eq + PartialOrd, V: PartialOrd, S: BuildHasher> PartialOrd for LinkedHashMap<K, V, S> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.iter().partial_cmp(other)
    }

    fn lt(&self, other: &Self) -> bool {
        self.iter().lt(other)
    }

    fn le(&self, other: &Self) -> bool {
        self.iter().le(other)
    }

    fn ge(&self, other: &Self) -> bool {
        self.iter().ge(other)
    }

    fn gt(&self, other: &Self) -> bool {
        self.iter().gt(other)
    }
}

impl<K: Hash + Eq + Ord, V: Ord, S: BuildHasher> Ord for LinkedHashMap<K, V, S> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter().cmp(other)
    }
}

impl<K: Hash + Eq, V: Hash, S: BuildHasher> Hash for LinkedHashMap<K, V, S> {
    fn hash<H: Hasher>(&self, h: &mut H) { for e in self.iter() { e.hash(h); } }
}

unsafe impl<K: Send, V: Send, S: Send> Send for LinkedHashMap<K, V, S> {}

unsafe impl<K: Sync, V: Sync, S: Sync> Sync for LinkedHashMap<K, V, S> {}

impl<K, V, S> Drop for LinkedHashMap<K, V, S> {
    fn drop(&mut self) {
        if !self.head.is_null() {
            unsafe {
                self.drop_entries();
                drop_empty_node(self.head);
            }
        }
        self.clear_free_list();
    }
}

/// An insertion-order iterator over a `LinkedHashMap`'s entries, with immutable references to the
/// values.
pub struct Iter<'a, K: 'a, V: 'a> {
    head: *const Node<K, V>,
    tail: *const Node<K, V>,
    remaining: usize,
    marker: marker::PhantomData<(&'a K, &'a V)>,
}

/// An insertion-order iterator over a `LinkedHashMap`'s entries, with mutable references to the
/// values.
pub struct IterMut<'a, K: 'a, V: 'a> {
    head: *mut Node<K, V>,
    tail: *mut Node<K, V>,
    remaining: usize,
    marker: marker::PhantomData<(&'a K, &'a mut V)>,
}

/// A consuming insertion-order iterator over a `LinkedHashMap`'s entries.
pub struct IntoIter<K, V> {
    head: *mut Node<K, V>,
    tail: *mut Node<K, V>,
    remaining: usize,
    marker: marker::PhantomData<(K, V)>,
}

/// An insertion-order iterator over a `LinkedHashMap`'s entries represented as
/// an `OccupiedEntry`.
pub struct Entries<'a, K: 'a, V: 'a, S: 'a = hash_map::RandomState> {
    map: *mut LinkedHashMap<K, V, S>,
    head: *mut Node<K, V>,
    remaining: usize,
    marker: marker::PhantomData<(&'a K, &'a mut V, &'a S)>,
}

unsafe impl<'a, K, V> Send for Iter<'a, K, V> where K: Send, V: Send {}

unsafe impl<'a, K, V> Send for IterMut<'a, K, V> where K: Send, V: Send {}

unsafe impl<K, V> Send for IntoIter<K, V> where K: Send, V: Send {}

unsafe impl<'a, K, V, S> Send for Entries<'a, K, V, S> where K: Send, V: Send, S: Send {}

unsafe impl<'a, K, V> Sync for Iter<'a, K, V> where K: Sync, V: Sync {}

unsafe impl<'a, K, V> Sync for IterMut<'a, K, V> where K: Sync, V: Sync {}

unsafe impl<K, V> Sync for IntoIter<K, V> where K: Sync, V: Sync {}

unsafe impl<'a, K, V, S> Sync for Entries<'a, K, V, S> where K: Sync, V: Sync, S: Sync {}

impl<'a, K, V> Clone for Iter<'a, K, V> {
    fn clone(&self) -> Self { Iter { ..*self } }
}

impl<K, V> Clone for IntoIter<K, V> where K: Clone, V: Clone {
    fn clone(&self) -> Self {
        if self.remaining == 0 {
            return IntoIter { ..*self }
        }

        fn clone_node<K, V>(e: *mut Node<K, V>) -> *mut Node<K, V>
            where K: Clone, V: Clone,
        {
            Box::into_raw(Box::new(Node::new(
                unsafe { (*e).key.clone() }, unsafe { (*e).value.clone() }
            )))
        }

        let mut cur = self.head;
        let head = clone_node(cur);
        let mut tail = head;
        for _ in 1..self.remaining {
            unsafe {
                (*tail).prev = clone_node((*cur).prev);
                (*(*tail).prev).next = tail;
                tail = (*tail).prev;
                cur = (*cur).prev;
            }
        }

        IntoIter {
            head: head,
            tail: tail,
            remaining: self.remaining,
            marker: marker::PhantomData,
        }
    }
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        if self.head == self.tail {
            None
        } else {
            self.remaining -= 1;
            unsafe {
                let r = Some((&(*self.head).key, &(*self.head).value));
                self.head = (*self.head).prev;
                r
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<(&'a K, &'a mut V)> {
        if self.head == self.tail {
            None
        } else {
            self.remaining -= 1;
            unsafe {
                let r = Some((&(*self.head).key, &mut (*self.head).value));
                self.head = (*self.head).prev;
                r
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<(K, V)> {
        if self.remaining == 0 {
            return None
        }
        self.remaining -= 1;
        unsafe {
            let prev = (*self.head).prev;
            let e = *Box::from_raw(self.head);
            self.head = prev;
            Some((e.key, e.value))
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

impl<'a, K, V, S: BuildHasher> Iterator for Entries<'a, K, V, S> {
    type Item = OccupiedEntry<'a, K, V, S>;

    fn next(&mut self) -> Option<OccupiedEntry<'a, K, V, S>> {
        if self.remaining == 0 {
            None
        } else {
            self.remaining -= 1;
            unsafe {
                let r = Some(OccupiedEntry {
                    map: self.map,
                    entry: self.head,
                    marker: marker::PhantomData,
                });

                self.head = (*self.head).prev;
                r
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

impl<'a, K, V> DoubleEndedIterator for Iter<'a, K, V> {
    fn next_back(&mut self) -> Option<(&'a K, &'a V)> {
        if self.head == self.tail {
            None
        } else {
            self.remaining -= 1;
            unsafe {
                self.tail = (*self.tail).next;
                Some((&(*self.tail).key, &(*self.tail).value))
            }
        }
    }
}

impl<'a, K, V> DoubleEndedIterator for IterMut<'a, K, V> {
    fn next_back(&mut self) -> Option<(&'a K, &'a mut V)> {
        if self.head == self.tail {
            None
        } else {
            self.remaining -= 1;
            unsafe {
                self.tail = (*self.tail).next;
                Some((&(*self.tail).key, &mut (*self.tail).value))
            }
        }
    }
}

impl<K, V> DoubleEndedIterator for IntoIter<K, V> {
    fn next_back(&mut self) -> Option<(K, V)> {
        if self.remaining == 0 {
            return None
        }
        self.remaining -= 1;
        unsafe {
            let next = (*self.tail).next;
            let e = *Box::from_raw(self.tail);
            self.tail = next;
            Some((e.key, e.value))
        }
    }
}

impl<'a, K, V> ExactSizeIterator for Iter<'a, K, V> {
    fn len(&self) -> usize { self.remaining }
}

impl<'a, K, V> ExactSizeIterator for IterMut<'a, K, V> {
    fn len(&self) -> usize { self.remaining }
}

impl<K, V> ExactSizeIterator for IntoIter<K, V> {
    fn len(&self) -> usize { self.remaining }
}

impl<K, V> Drop for IntoIter<K, V> {
    fn drop(&mut self) {
        for _ in 0..self.remaining {
            unsafe {
                let next = (*self.tail).next;
                Box::from_raw(self.tail);
                self.tail = next;
            }
        }
    }
}

/// An insertion-order iterator over a `LinkedHashMap`'s keys.
pub struct Keys<'a, K: 'a, V: 'a> {
    inner: Iter<'a, K, V>,
}

impl<'a, K, V> Clone for Keys<'a, K, V> {
    fn clone(&self) -> Self { Keys { inner: self.inner.clone() } }
}

impl<'a, K, V> Iterator for Keys<'a, K, V> {
    type Item = &'a K;

    #[inline] fn next(&mut self) -> Option<&'a K> { self.inner.next().map(|e| e.0) }
    #[inline] fn size_hint(&self) -> (usize, Option<usize>) { self.inner.size_hint() }
}

impl<'a, K, V> DoubleEndedIterator for Keys<'a, K, V> {
    #[inline] fn next_back(&mut self) -> Option<&'a K> { self.inner.next_back().map(|e| e.0) }
}

impl<'a, K, V> ExactSizeIterator for Keys<'a, K, V> {
    fn len(&self) -> usize { self.inner.len() }
}

/// An insertion-order iterator over a `LinkedHashMap`'s values.
pub struct Values<'a, K: 'a, V: 'a> {
    inner: Iter<'a, K, V>,
}

impl<'a, K, V> Clone for Values<'a, K, V> {
    fn clone(&self) -> Self { Values { inner: self.inner.clone() } }
}

impl<'a, K, V> Iterator for Values<'a, K, V> {
    type Item = &'a V;

    #[inline] fn next(&mut self) -> Option<&'a V> { self.inner.next().map(|e| e.1) }
    #[inline] fn size_hint(&self) -> (usize, Option<usize>) { self.inner.size_hint() }
}

impl<'a, K, V> DoubleEndedIterator for Values<'a, K, V> {
    #[inline] fn next_back(&mut self) -> Option<&'a V> { self.inner.next_back().map(|e| e.1) }
}

impl<'a, K, V> ExactSizeIterator for Values<'a, K, V> {
    fn len(&self) -> usize { self.inner.len() }
}

impl<'a, K: Hash + Eq, V, S: BuildHasher> IntoIterator for &'a LinkedHashMap<K, V, S> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;
    fn into_iter(self) -> Iter<'a, K, V> { self.iter() }
}

impl<'a, K: Hash + Eq, V, S: BuildHasher> IntoIterator for &'a mut LinkedHashMap<K, V, S> {
    type Item = (&'a K, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;
    fn into_iter(self) -> IterMut<'a, K, V> { self.iter_mut() }
}

impl<K: Hash + Eq, V, S: BuildHasher> IntoIterator for LinkedHashMap<K, V, S> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;
    fn into_iter(mut self) -> IntoIter<K, V> {
        let (head, tail) = if !self.head.is_null() {
            unsafe { ((*self.head).prev, (*self.head).next) }
        } else {
            (ptr::null_mut(), ptr::null_mut())
        };
        let len = self.len();

        if !self.head.is_null() {
            unsafe { drop_empty_node(self.head) }
        }
        self.clear_free_list();
        // drop the HashMap but not the LinkedHashMap
        unsafe { ptr::drop_in_place(&mut self.map); }
        mem::forget(self);

        IntoIter {
            head: head,
            tail: tail,
            remaining: len,
            marker: marker::PhantomData,
        }
    }
}

/// A view into a single location in a map, which may be vacant or occupied.
pub enum Entry<'a, K: 'a, V: 'a, S: 'a = hash_map::RandomState> {
    /// An occupied Entry.
    Occupied(OccupiedEntry<'a, K, V, S>),
    /// A vacant Entry.
    Vacant(VacantEntry<'a, K, V, S>),
}

/// A view into a single occupied location in a `LinkedHashMap`.
pub struct OccupiedEntry<'a, K: 'a, V: 'a, S: 'a = hash_map::RandomState> {
    entry: *mut Node<K, V>,
    map: *mut LinkedHashMap<K, V, S>,
    marker: marker::PhantomData<&'a K>,
}

/// A view into a single empty location in a `LinkedHashMap`.
pub struct VacantEntry<'a, K: 'a, V: 'a, S: 'a = hash_map::RandomState> {
    key: K,
    map: &'a mut LinkedHashMap<K, V, S>,
}

impl<'a, K: Hash + Eq, V, S: BuildHasher> Entry<'a, K, V, S> {
    /// Returns the entry key
    pub fn key(&self) -> &K {
        match *self {
            Entry::Occupied(ref e) => e.key(),
            Entry::Vacant(ref e) => e.key(),
        }
    }

    /// Ensures a value is in the entry by inserting the default if empty, and returns
    /// a mutable reference to the value in the entry.
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default),
        }
    }

    /// Ensures a value is in the entry by inserting the result of the default function if empty,
    /// and returns a mutable reference to the value in the entry.
    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default()),
        }
    }
}

impl<'a, K: Hash + Eq, V, S: BuildHasher> OccupiedEntry<'a, K, V, S> {
    /// Gets a reference to the entry key
    pub fn key(&self) -> &K {
        unsafe { &(*self.entry).key }
    }

    /// Gets a reference to the value in the entry.
    pub fn get(&self) -> &V {
        unsafe { &(*self.entry).value }
    }

    /// Gets a mutable reference to the value in the entry.
    pub fn get_mut(&mut self) -> &mut V {
        unsafe { &mut (*self.entry).value }
    }

    /// Converts the OccupiedEntry into a mutable reference to the value in the entry
    /// with a lifetime bound to the map itself
    pub fn into_mut(self) -> &'a mut V {
        unsafe { &mut (*self.entry).value }
    }

    /// Sets the value of the entry, and returns the entry's old value
    pub fn insert(&mut self, value: V) -> V {
        unsafe {
            (*self.map).ensure_guard_node();

            let old_val = mem::replace(&mut (*self.entry).value, value);
            let node_ptr: *mut Node<K, V> = self.entry;

            // Existing node, just update LRU position
            (*self.map).detach(node_ptr);
            (*self.map).attach(node_ptr);

            old_val
        }
    }

    /// Takes the value out of the entry, and returns it
    pub fn remove(self) -> V {
        unsafe { (*self.map).remove(&(*self.entry).key) }.unwrap()
    }
}

impl<'a, K: 'a + Hash + Eq, V: 'a, S: BuildHasher> VacantEntry<'a, K, V, S> {
    /// Gets a reference to the entry key
    pub fn key(&self) -> &K {
        &self.key
    }

    /// Sets the value of the entry with the VacantEntry's key,
    /// and returns a mutable reference to it
    pub fn insert(self, value: V) -> &'a mut V {
        self.map.ensure_guard_node();

        let node = if self.map.free.is_null() {
            Box::into_raw(Box::new(Node::new(self.key, value)))
        } else {
            // use a recycled box
            unsafe {
                let free = self.map.free;
                self.map.free = (*free).next;
                ptr::write(free, Node::new(self.key, value));
                free
            }
        };

        let keyref = unsafe { &(*node).key };

        self.map.attach(node);

        let ret = self.map.map.entry(KeyRef{k: keyref}).or_insert(node);
        unsafe { &mut (**ret).value }
    }
}
#[cfg(all(feature = "nightly", test))]
mod bench {
    extern crate test;

    use super::LinkedHashMap;

    #[bench]
    fn not_recycled_cycling(b: &mut test::Bencher) {
        let mut hash_map = LinkedHashMap::with_capacity(1000);
        for i in 0usize..1000 {
            hash_map.insert(i, i);
        }
        b.iter(|| {
            for i in 0usize..1000 {
                hash_map.remove(&i);
            }
            hash_map.clear_free_list();
            for i in 0usize..1000 {
                hash_map.insert(i, i);
            }
        })
    }

    #[bench]
    fn recycled_cycling(b: &mut test::Bencher) {
        let mut hash_map = LinkedHashMap::with_capacity(1000);
        for i in 0usize..1000 {
            hash_map.insert(i, i);
        }
        b.iter(|| {
            for i in 0usize..1000 {
                hash_map.remove(&i);
            }
            for i in 0usize..1000 {
                hash_map.insert(i, i);
            }
        })
    }
}

