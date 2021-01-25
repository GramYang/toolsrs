use std::fmt::{Debug,Formatter,Result};
use std::cmp::Ordering;
use std::iter::{FromIterator};
use std::ops::{Index,IndexMut};
use std::hash::{Hash,Hasher};
use std::slice;
use std::mem;
use std::ptr;

macro_rules! item { ($i:item) => {$i}}

macro_rules! addr { ($e:expr) => { $e } }

macro_rules! iterator_impl {
    ($name:ident,
     iter = $iter:ident,
     mutability = $($mut_:tt)*) => {
        impl<'a, T> $name<'a, T> {
            #[cfg(target_pointer_width="32")]
            unsafe fn new() -> $name<'a, T> {
                $name {
                    remaining: 0,
                    length: 0,
                    stack: [IntoIterator::into_iter((& $($mut_)*[])),
                            IntoIterator::into_iter((& $($mut_)*[])),
                            IntoIterator::into_iter((& $($mut_)*[])),
                            IntoIterator::into_iter((& $($mut_)*[])),

                            IntoIterator::into_iter((& $($mut_)*[])),
                            IntoIterator::into_iter((& $($mut_)*[])),
                            IntoIterator::into_iter((& $($mut_)*[])),
                            IntoIterator::into_iter((& $($mut_)*[])),
                            ]
                }
            }

            #[cfg(target_pointer_width="64")]
            unsafe fn new() -> $name<'a, T> {
                $name {
                    remaining: 0,
                    length: 0,
                    stack: [IntoIterator::into_iter((& $($mut_)*[])),
                            IntoIterator::into_iter((& $($mut_)*[])),
                            IntoIterator::into_iter((& $($mut_)*[])),
                            IntoIterator::into_iter((& $($mut_)*[])),

                            IntoIterator::into_iter((& $($mut_)*[])),
                            IntoIterator::into_iter((& $($mut_)*[])),
                            IntoIterator::into_iter((& $($mut_)*[])),
                            IntoIterator::into_iter((& $($mut_)*[])),

                            IntoIterator::into_iter((& $($mut_)*[])),
                            IntoIterator::into_iter((& $($mut_)*[])),
                            IntoIterator::into_iter((& $($mut_)*[])),
                            IntoIterator::into_iter((& $($mut_)*[])),

                            IntoIterator::into_iter((& $($mut_)*[])),
                            IntoIterator::into_iter((& $($mut_)*[])),
                            IntoIterator::into_iter((& $($mut_)*[])),
                            IntoIterator::into_iter((& $($mut_)*[])),
                            ]
                }
            }
        }

        item!(impl<'a, T> Iterator for $name<'a, T> {
                type Item = (usize, &'a $($mut_)* T);
                fn next(&mut self) -> Option<(usize, &'a $($mut_)* T)> {
                    let start_ptr = self.stack.as_mut_ptr();

                    unsafe {
                        let mut write_ptr = start_ptr.offset(self.length as isize);
                        while write_ptr != start_ptr {
                            match (*write_ptr.offset(-1)).next() {
                                None => write_ptr = write_ptr.offset(-1),
                                Some(child) => {
                                    addr!(match *child {
                                            TrieNode::Internal(ref $($mut_)* node) => {
                                                *write_ptr = node.children.$iter();
                                                write_ptr = write_ptr.offset(1);
                                            }
                                            TrieNode::External(key, ref $($mut_)* value) => {
                                                self.remaining -= 1;
                                                self.length = (write_ptr as usize
                                                               - start_ptr as usize) /
                                                    mem::size_of_val(&*write_ptr);

                                                return Some((key, value));
                                            }
                                            TrieNode::Nothing => {}
                                        })
                                }
                            }
                        }
                    }
                    return None;
                }

                #[inline]
                fn size_hint(&self) -> (usize, Option<usize>) {
                    (self.remaining, Some(self.remaining))
                }
            });

        impl<'a, T> ExactSizeIterator for $name<'a, T> {
            fn len(&self) -> usize { self.remaining }
        }
    }
}

macro_rules! bound {
    ($iterator_name:ident,
     self = $this:expr,
     key = $key:expr,
     is_upper = $upper:expr,

     iter = $iter:ident,

     mutability = $($mut_:tt)*) => {
        {
            let this = $this;
            let mut node = unsafe {
                mem::transmute::<_, usize>(&this.root) as *mut InternalNode<T>
            };

            let key = $key;

            let mut it = unsafe {$iterator_name::new()};
            it.remaining = this.length;

            addr!(loop {
                    let children = unsafe {addr!(& $($mut_)* (*node).children)};
                    // it.length is the current depth in the iterator and the
                    // current depth through the `usize` key we've traversed.
                    let child_id = chunk(key, it.length);
                    let (slice_idx, ret) = match children[child_id] {
                        TrieNode::Internal(ref $($mut_)* n) => {
                            node = unsafe {
                                mem::transmute::<_, usize>(&**n)
                                    as *mut InternalNode<T>
                            };
                            (child_id + 1, false)
                        }
                        TrieNode::External(stored, _) => {
                            (if stored < key || ($upper && stored == key) {
                                child_id + 1
                            } else {
                                child_id
                            }, true)
                        }
                        TrieNode::Nothing => {
                            (child_id + 1, true)
                        }
                    };
                    it.stack[it.length] = children[slice_idx..].$iter();
                    it.length += 1;
                    if ret { break }
                });

            it
        }
    }
}

iterator_impl! { Iter, iter = iter, mutability = }
iterator_impl! { IterMut, iter = iter_mut, mutability = mut }

#[cfg(target_pointer_width = "32")]
pub const USIZE_BITS: usize = 32;

#[cfg(target_pointer_width = "64")]
pub const USIZE_BITS: usize = 64;
const SHIFT: usize = 4;
const SIZE: usize = 1 << SHIFT;
const MASK: usize = SIZE - 1;
const MAX_DEPTH: usize = USIZE_BITS / SHIFT;

#[derive(Clone)]
pub struct Map<T> {
    pub root: InternalNode<T>,
    pub length: usize
}

pub struct InternalNode<T> {
    pub count: usize,
    pub children: [TrieNode<T>; SIZE]
}

#[derive(Clone)]
pub enum TrieNode<T> {
    Internal(Box<InternalNode<T>>),
    External(usize, T),
    Nothing
}

/*****************************Map<T>实现***************************************/

impl<T: PartialEq> PartialEq for Map<T> {
    fn eq(&self, other: &Map<T>) -> bool {
        self.len() == other.len() &&
            self.iter().zip(other.iter()).all(|(a, b)| a == b)
    }
}

impl<T: Eq> Eq for Map<T> {}

impl<T: PartialOrd> PartialOrd for Map<T> {
    #[inline]
    fn partial_cmp(&self, other: &Map<T>) -> Option<Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<T: Ord> Ord for Map<T> {
    #[inline]
    fn cmp(&self, other: &Map<T>) -> Ordering {
        self.iter().cmp(other.iter())
    }
}

impl<T: Debug> Debug for Map<T> {
    fn fmt(&self, f: &mut Formatter) -> Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<T> Default for Map<T> {
    #[inline]
    fn default() -> Map<T> { Map::new() }
}

impl<T> FromIterator<(usize, T)> for Map<T> {
    fn from_iter<I: IntoIterator<Item=(usize, T)>>(iter: I) -> Map<T> {
        let mut map = Map::new();
        map.extend(iter);
        map
    }
}

impl<T> Extend<(usize, T)> for Map<T> {
    fn extend<I: IntoIterator<Item=(usize, T)>>(&mut self, iter: I) {
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

impl<T: Hash> Hash for Map<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        for elt in self.iter() {
            elt.hash(state);
        }
    }
}

impl<'a, T> Index<&'a usize> for Map<T> {
    type Output = T;
    #[inline]
    fn index(&self, i: &'a usize) -> &T {
        self.get(i).expect("key not present")
    }
}

impl<'a, T> IndexMut<&'a usize> for Map<T> {
    #[inline]
    fn index_mut(&mut self, i: &'a usize) -> &mut T {
        self.get_mut(i).expect("key not present")
    }
}

impl<T> Map<T>{
    #[inline]
    pub fn new() -> Map<T> {
        Map{root: InternalNode::new(), length: 0}
    }

    #[inline]
    pub fn each_reverse<'a, F>(&'a self, mut f: F) -> bool
        where F: FnMut(&usize, &'a T) -> bool {
        self.root.each_reverse(&mut f)
    }

    pub fn keys(&self) -> Keys<T> { Keys(self.iter()) }

    pub fn values(&self) -> Values<T> { Values(self.iter()) }

    pub fn iter(&self) -> Iter<T> {
        let mut iter = unsafe {Iter::new()};
        iter.stack[0] = self.root.children.iter();
        iter.length = 1;
        iter.remaining = self.length;

        iter
    }

    pub fn iter_mut(&mut self) -> IterMut<T> {
        let mut iter = unsafe {IterMut::new()};
        iter.stack[0] = self.root.children.iter_mut();
        iter.length = 1;
        iter.remaining = self.length;

        iter
    }

    #[inline]
    pub fn len(&self) -> usize { self.length }

    #[inline]
    pub fn is_empty(&self) -> bool { self.len() == 0 }

    #[inline]
    pub fn clear(&mut self) {
        self.root = InternalNode::new();
        self.length = 0;
    }

    #[inline]
    pub fn get(&self, key: &usize) -> Option<&T> {
        let mut node = &self.root;
        let mut idx = 0;
        loop {
            match node.children[chunk(*key, idx)] {
                TrieNode::Internal(ref x) => node = &**x,
                TrieNode::External(stored, ref value) => {
                    if stored == *key {
                        return Some(value)
                    } else {
                        return None
                    }
                }
                TrieNode::Nothing => return None
            }
            idx += 1;
        }
    }

    #[inline]
    pub fn contains_key(&self, key: &usize) -> bool {
        self.get(key).is_some()
    }

    #[inline]
    pub fn get_mut(&mut self, key: &usize) -> Option<&mut T> {
        find_mut(&mut self.root.children[chunk(*key, 0)], *key, 1)
    }

    pub fn insert(&mut self, key: usize, value: T) -> Option<T> {
        let (_, old_val) = insert(&mut self.root.count,
                                  &mut self.root.children[chunk(key, 0)],
                                  key, value, 1);
        if old_val.is_none() { self.length += 1 }
        old_val
    }

    pub fn remove(&mut self, key: &usize) -> Option<T> {
        let ret = remove(&mut self.root.count,
                         &mut self.root.children[chunk(*key, 0)],
                         *key, 1);
        if ret.is_some() { self.length -= 1 }
        ret
    }

    #[inline]
    fn bound(&self, key: usize, upper: bool) -> Range<T> {
        Range(bound!(Iter, self = self,
               key = key, is_upper = upper,
               iter = iter,
               mutability = ))
    }

    pub fn lower_bound(&self, key: usize) -> Range<T> {
        self.bound(key, false)
    }

    pub fn upper_bound(&self, key: usize) -> Range<T> {
        self.bound(key, true)
    }

    #[inline]
    fn bound_mut(&mut self, key: usize, upper: bool) -> RangeMut<T> {
        RangeMut(bound!(IterMut, self = self,
               key = key, is_upper = upper,
               iter = iter_mut,
               mutability = mut))
    }

    pub fn lower_bound_mut(&mut self, key: usize) -> RangeMut<T> {
        self.bound_mut(key, false)
    }

    pub fn upper_bound_mut(&mut self, key: usize) -> RangeMut<T> {
        self.bound_mut(key, true)
    }

    #[inline]
    pub fn entry(&mut self, key: usize) -> Entry<T> {
        let mut search_stack = SearchStack::new(self, key);
        let first_node = &mut search_stack.map.root.children[chunk(key, 0)] as *mut _;
        search_stack.push(first_node);
        let search_successful: bool;
        loop {
            match unsafe { next_child(search_stack.peek(), key, search_stack.length) } {
                (Some(child), _) => search_stack.push(child),
                (None, success) => {
                    search_successful = success;
                    break;
                }
            }
        }
        if search_successful {
            Entry::Occupied(OccupiedEntry { search_stack: search_stack })
        } else {
            Entry::Vacant(VacantEntry { search_stack: search_stack })
        }
    }
}


/**********************************InternalNode<T>实现*****************************************/

impl<T:Clone> Clone for InternalNode<T> {
    #[inline]
    fn clone(&self) -> InternalNode<T> {
        let ch = &self.children;
        InternalNode {
            count: self.count,
            children: [ch[0].clone(), ch[1].clone(), ch[2].clone(), ch[3].clone(),
                ch[4].clone(), ch[5].clone(), ch[6].clone(), ch[7].clone(),
                ch[8].clone(), ch[9].clone(), ch[10].clone(), ch[11].clone(),
                ch[12].clone(), ch[13].clone(), ch[14].clone(), ch[15].clone()]}
    }
}

impl<T> InternalNode<T> {
    #[inline]
    fn new() -> InternalNode<T> {
        InternalNode{count: 0,
            children: [TrieNode::Nothing, TrieNode::Nothing, TrieNode::Nothing, TrieNode::Nothing,
                TrieNode::Nothing, TrieNode::Nothing, TrieNode::Nothing, TrieNode::Nothing,
                TrieNode::Nothing, TrieNode::Nothing, TrieNode::Nothing, TrieNode::Nothing,
                TrieNode::Nothing, TrieNode::Nothing, TrieNode::Nothing, TrieNode::Nothing]}
    }

    fn each_reverse<'a, F>(&'a self, f: &mut F) -> bool
        where F: FnMut(&usize, &'a T) -> bool {
        for elt in self.children.iter().rev() {
            match *elt {
                TrieNode::Internal(ref x) => if !x.each_reverse(f) { return false },
                TrieNode::External(k, ref v) => if !f(&k, v) { return false },
                TrieNode::Nothing => ()
            }
        }
        true
    }
}

/*************************************其他实现*****************************************/

pub struct Iter<'a, T:'a> {
    stack: [slice::Iter<'a, TrieNode<T>>; MAX_DEPTH],
    length: usize,
    remaining: usize,
}

impl<'a, T> Clone for Iter<'a, T> {
    #[cfg(target_pointer_width="32")]
    fn clone(&self) -> Iter<'a, T> {
        Iter {
            stack: [self.stack[0].clone(), self.stack[1].clone(),
                self.stack[2].clone(), self.stack[3].clone(),
                self.stack[4].clone(), self.stack[5].clone(),
                self.stack[6].clone(), self.stack[7].clone()], ..*self }
    }

    #[cfg(target_pointer_width="64")]
    fn clone(&self) -> Iter<'a, T> {
        Iter {
            stack: [self.stack[0].clone(), self.stack[1].clone(),
                self.stack[2].clone(), self.stack[3].clone(),
                self.stack[4].clone(), self.stack[5].clone(),
                self.stack[6].clone(), self.stack[7].clone(),
                self.stack[8].clone(), self.stack[9].clone(),
                self.stack[10].clone(), self.stack[11].clone(),
                self.stack[12].clone(), self.stack[13].clone(),
                self.stack[14].clone(), self.stack[15].clone()], ..*self }
    }
}

pub struct IterMut<'a, T:'a> {
    stack: [slice::IterMut<'a, TrieNode<T>>; MAX_DEPTH],
    length: usize,
    remaining: usize,
}

pub struct Keys<'a, T: 'a>(Iter<'a, T>);

impl<'a, T> Clone for Keys<'a, T> {
    fn clone(&self) -> Keys<'a, T> { Keys(self.0.clone()) }
}

impl<'a, T> Iterator for Keys<'a, T> {
    type Item = usize;
    fn next(&mut self) -> Option<usize> { self.0.next().map(|e| e.0) }
    fn size_hint(&self) -> (usize, Option<usize>) { self.0.size_hint() }
}

impl<'a, T> ExactSizeIterator for Keys<'a, T> {}

pub struct Values<'a, T: 'a>(Iter<'a, T>);

impl<'a, T> Clone for Values<'a, T> {
    fn clone(&self) -> Values<'a, T> { Values(self.0.clone()) }
}

impl<'a, T> Iterator for Values<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<&'a T> { self.0.next().map(|e| e.1) }
    fn size_hint(&self) -> (usize, Option<usize>) { self.0.size_hint() }
}

impl<'a, T> ExactSizeIterator for Values<'a, T> {}

pub struct Range<'a, T: 'a>(Iter<'a, T>);

impl<'a, T> Clone for Range<'a, T> {
    fn clone(&self) -> Range<'a, T> { Range(self.0.clone()) }
}

impl<'a, T> Iterator for Range<'a, T> {
    type Item = (usize, &'a T);
    fn next(&mut self) -> Option<(usize, &'a T)> { self.0.next() }
    fn size_hint(&self) -> (usize, Option<usize>) { (0, Some(self.0.remaining)) }
}

pub struct RangeMut<'a, T: 'a>(IterMut<'a, T>);

impl<'a, T> Iterator for RangeMut<'a, T> {
    type Item = (usize, &'a mut T);
    fn next(&mut self) -> Option<(usize, &'a mut T)> { self.0.next() }
    fn size_hint(&self) -> (usize, Option<usize>) { (0, Some(self.0.remaining)) }
}

impl<'a, T> IntoIterator for &'a Map<T> {
    type Item = (usize, &'a T);
    type IntoIter = Iter<'a, T>;
    fn into_iter(self) -> Iter<'a, T> { self.iter() }
}

impl<'a, T> IntoIterator for &'a mut Map<T> {
    type Item = (usize, &'a mut T);
    type IntoIter = IterMut<'a, T>;
    fn into_iter(self) -> IterMut<'a, T> { self.iter_mut() }
}

pub enum Entry<'a, T: 'a> {
    /// An occupied entry.
    Occupied(OccupiedEntry<'a, T>),
    /// A vacant entry.
    Vacant(VacantEntry<'a, T>)
}

impl<'a, T> Entry<'a, T> {
    /// Ensures a value is in the entry by inserting the default if empty, and returns
    /// a mutable reference to the value in the entry.
    pub fn or_insert(self, default: T) -> &'a mut T {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default),
        }
    }

    pub fn or_insert_with<F: FnOnce() -> T>(self, default: F) -> &'a mut T {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default()),
        }
    }
}

pub struct OccupiedEntry<'a, T: 'a> {
    search_stack: SearchStack<'a, T>
}

pub struct VacantEntry<'a, T: 'a> {
    search_stack: SearchStack<'a, T>
}

impl<'a, T> OccupiedEntry<'a, T> {
    #[inline]
    pub fn get(&self) -> &T {
        match *self.search_stack.peek_ref() {
            TrieNode::External(_, ref value) => value,
            _ => unreachable!()
        }
    }

    #[inline]
    pub fn get_mut(&mut self) -> &mut T {
        match *self.search_stack.peek_ref() {
            TrieNode::External(_, ref mut value) => value,
            _ => unreachable!()
        }
    }

    #[inline]
    pub fn into_mut(self) -> &'a mut T {
        match *self.search_stack.peek_ref() {
            TrieNode::External(_, ref mut value) => value,
            _ => unreachable!()
        }
    }

    #[inline]
    pub fn insert(&mut self, value: T) -> T {
        match *self.search_stack.peek_ref() {
            TrieNode::External(_, ref mut stored_value) => {
                mem::replace(stored_value, value)
            }
            _ => unreachable!()
        }
    }

    /// Takes the value out of the entry, and returns it.
    #[inline]
    pub fn remove(self) -> T {
        let mut search_stack = self.search_stack;

        let leaf_node = mem::replace(search_stack.pop_ref(), TrieNode::Nothing);

        let value = match leaf_node {
            TrieNode::External(_, value) => value,
            _ => unreachable!()
        };

        while !search_stack.is_empty() {
            let ancestor = search_stack.pop_ref();
            match *ancestor {
                TrieNode::Internal(ref mut internal) => {
                    // If stopping deletion, update the child count and break.
                    if internal.count != 1 {
                        internal.count -= 1;
                        break;
                    }
                }
                // Invalid SearchStack, non-internal ancestor node.
                _ => unreachable!()
            }
            *ancestor = TrieNode::Nothing;
        }

        search_stack.map.length -= 1;

        value
    }
}

impl<'a, T> VacantEntry<'a, T> {
    /// Set the vacant entry to the given value.
    pub fn insert(self, value: T) -> &'a mut T {
        let search_stack = self.search_stack;
        let old_length = search_stack.length;
        let key = search_stack.key;

        search_stack.map.length += 1;

        if old_length == 1 {
            let mut temp = search_stack.map.root.count;
            let (value_ref, _) = insert(&mut temp, search_stack.get_ref(0), key, value, 1);
            search_stack.map.root.count = temp;
            value_ref
        }
        else {
            match *search_stack.get_ref(old_length - 2) {
                TrieNode::Internal(ref mut parent) => {
                    let parent = &mut **parent;
                    let (value_ref, _) = insert(&mut parent.count,
                                                &mut parent.children[chunk(key, old_length - 1)],
                                                key, value, old_length);
                    value_ref
                }
                _ => unreachable!()
            }
        }
    }
}

struct SearchStack<'a, T: 'a> {
    map: &'a mut Map<T>,
    length: usize,
    key: usize,
    items: [*mut TrieNode<T>; MAX_DEPTH]
}

impl<'a, T> SearchStack<'a, T> {
    /// Creates a new search-stack with empty entries.
    fn new(map: &'a mut Map<T>, key: usize) -> SearchStack<'a, T> {
        SearchStack {
            map: map,
            length: 0,
            key: key,
            items: [ptr::null_mut(); MAX_DEPTH]
        }
    }

    fn push(&mut self, node: *mut TrieNode<T>) {
        self.length += 1;
        self.items[self.length - 1] = node;
    }

    fn peek(&self) -> *mut TrieNode<T> {
        self.items[self.length - 1]
    }

    fn peek_ref(&self) -> &'a mut TrieNode<T> {
        let item = self.items[self.length - 1];
        unsafe { &mut *item }
    }

    fn pop_ref(&mut self) -> &'a mut TrieNode<T> {
        self.length -= 1;
        unsafe {
            &mut *self.items[self.length]
        }
    }

    fn is_empty(&self) -> bool {
        self.length == 0
    }

    fn get_ref(&self, idx: usize) -> &'a mut TrieNode<T> {
        assert!(idx < self.length);
        unsafe {
            &mut *self.items[idx]
        }
    }
}

#[inline]
fn chunk(n: usize, idx: usize) -> usize {
    let sh = USIZE_BITS - (SHIFT * (idx + 1));
    (n >> sh) & MASK
}

fn find_mut<T>(child: &mut TrieNode<T>, key: usize, idx: usize) -> Option<&mut T> {
    match *child {
        TrieNode::External(stored, ref mut value) if stored == key => Some(value),
        TrieNode::External(..) => None,
        TrieNode::Internal(ref mut x) => find_mut(&mut x.children[chunk(key, idx)], key, idx + 1),
        TrieNode::Nothing => None
    }
}

fn insert<'a, T>(count: &mut usize, start_node: &'a mut TrieNode<T>, key: usize, value: T, idx: usize)
                 -> (&'a mut T, Option<T>) {
    // We branch twice to avoid having to do the `replace` when we
    // don't need to; this is much faster, especially for keys that
    // have long shared prefixes.

    let mut hack = false;
    match *start_node {
        TrieNode::Nothing => {
            *count += 1;
            *start_node = TrieNode::External(key, value);
            match *start_node {
                TrieNode::External(_, ref mut value_ref) => return (value_ref, None),
                _ => unreachable!()
            }
        }
        TrieNode::Internal(ref mut x) => {
            let x = &mut **x;
            return insert(&mut x.count, &mut x.children[chunk(key, idx)], key, value, idx + 1);
        }
        TrieNode::External(stored_key, _) if stored_key == key => {
            hack = true;
        }
        _ => {}
    }

    if !hack {
        // Conflict, an external node with differing keys.
        // We replace the old node by an internal one, then re-insert the two values beneath it.
        match mem::replace(start_node, TrieNode::Internal(Box::new(InternalNode::new()))) {
            TrieNode::External(stored_key, stored_value) => {
                match *start_node {
                    TrieNode::Internal(ref mut new_node) => {
                        let new_node = &mut **new_node;
                        // Re-insert the old value.
                        insert(&mut new_node.count,
                               &mut new_node.children[chunk(stored_key, idx)],
                               stored_key, stored_value, idx + 1);

                        // Insert the new value, and return a reference to it directly.
                        return insert(&mut new_node.count,
                                      &mut new_node.children[chunk(key, idx)],
                                      key, value, idx + 1);
                    }
                    // Value that was just copied disappeared.
                    _ => unreachable!()
                }
            }
            // Logic error in previous match.
            _ => unreachable!(),
        }
    }

    if let TrieNode::External(_, ref mut stored_value) = *start_node {
        // Swap in the new value and return the old.
        let old_value = mem::replace(stored_value, value);
        return (stored_value, Some(old_value));
    }

    unreachable!();
}

fn remove<T>(count: &mut usize, child: &mut TrieNode<T>, key: usize,
             idx: usize) -> Option<T> {
    let (ret, this) = match *child {
        TrieNode::External(stored, _) if stored == key => {
            match mem::replace(child, TrieNode::Nothing) {
                TrieNode::External(_, value) => (Some(value), true),
                _ => unreachable!()
            }
        }
        TrieNode::External(..) => (None, false),
        TrieNode::Internal(ref mut x) => {
            let x = &mut **x;
            let ret = remove(&mut x.count, &mut x.children[chunk(key, idx)],
                             key, idx + 1);
            (ret, x.count == 0)
        }
        TrieNode::Nothing => (None, false)
    };

    if this {
        *child = TrieNode::Nothing;
        *count -= 1;
    }
    return ret;
}

#[inline]
unsafe fn next_child<T>(node: *mut TrieNode<T>, key: usize, idx: usize)
                        -> (Option<*mut TrieNode<T>>, bool) {
    match *node {
        TrieNode::Internal(ref mut node_internal) => {
            (Some(&mut node_internal.children[chunk(key, idx)] as *mut _), false)
        },
        TrieNode::External(stored_key, _) if stored_key == key => (None, true),
        TrieNode::External(..) | TrieNode::Nothing => (None, false)
    }
}

