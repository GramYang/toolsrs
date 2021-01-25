#[cfg(test)]
mod test {
    use std::usize;
    use std::hash::{Hash, Hasher};
    use std::collections::hash_map::DefaultHasher;
    use crate::trie::map::{Map,InternalNode,TrieNode,Entry::*};

    fn check_integrity<T>(trie: &InternalNode<T>) {
        assert!(trie.count != 0);

        let mut sum = 0;

        for x in trie.children.iter() {
            match *x {
                TrieNode::Nothing => (),
                TrieNode::Internal(ref y) => {
                    check_integrity(&**y);
                    sum += 1
                }
                TrieNode::External(_, _) => { sum += 1 }
            }
        }

        assert_eq!(sum, trie.count);
    }

    #[test]
    fn test_find_mut() {
        let mut m = Map::new();
        assert!(m.insert(1, 12).is_none());
        assert!(m.insert(2, 8).is_none());
        assert!(m.insert(5, 14).is_none());
        let new = 100;
        match m.get_mut(&5) {
            None => panic!(), Some(x) => *x = new
        }
        assert_eq!(m.get(&5), Some(&new));
    }

    #[test]
    fn test_find_mut_missing() {
        let mut m = Map::new();
        assert!(m.get_mut(&0).is_none());
        assert!(m.insert(1, 12).is_none());
        assert!(m.get_mut(&0).is_none());
        assert!(m.insert(2, 8).is_none());
        assert!(m.get_mut(&0).is_none());
    }

    #[test]
    fn test_step() {
        let mut trie = Map::new();
        let n = 300;

        for x in (1..n).step_by(2) {
            assert!(trie.insert(x, x + 1).is_none());
            assert!(trie.contains_key(&x));
            check_integrity(&trie.root);
        }

        for x in (0..n).step_by(2) {
            assert!(!trie.contains_key(&x));
            assert!(trie.insert(x, x + 1).is_none());
            check_integrity(&trie.root);
        }

        for x in 0..n {
            assert!(trie.contains_key(&x));
            assert!(!trie.insert(x, x + 1).is_none());
            check_integrity(&trie.root);
        }

        for x in (1..n).step_by(2) {
            assert!(trie.remove(&x).is_some());
            assert!(!trie.contains_key(&x));
            check_integrity(&trie.root);
        }

        for x in (0..n).step_by(2) {
            assert!(trie.contains_key(&x));
            assert!(!trie.insert(x, x + 1).is_none());
            check_integrity(&trie.root);
        }
    }

    #[test]
    fn test_each_reverse() {
        let mut m = Map::new();

        assert!(m.insert(3, 6).is_none());
        assert!(m.insert(0, 0).is_none());
        assert!(m.insert(4, 8).is_none());
        assert!(m.insert(2, 4).is_none());
        assert!(m.insert(1, 2).is_none());

        let mut n = 5;
        let mut vec: Vec<&i32> = vec![];
        m.each_reverse(|k, v| {
            n -= 1;
            assert_eq!(*k, n);
            vec.push(v);
            true
        });
        assert_eq!(vec, [&8, &6, &4, &2, &0]);
    }

    #[test]
    fn test_each_reverse_break() {
        let mut m = Map::new();

        for x in (usize::MAX - 10000..usize::MAX).rev() {
            m.insert(x, x / 2);
        }

        let mut n = usize::MAX - 1;
        m.each_reverse(|k, v| {
            if n == usize::MAX - 5000 { false } else {
                assert!(n > usize::MAX - 5000);

                assert_eq!(*k, n);
                assert_eq!(*v, n / 2);
                n -= 1;
                true
            }
        });
    }

    #[test]
    fn test_insert() {
        let mut m = Map::new();
        assert_eq!(m.insert(1, 2), None);
        assert_eq!(m.insert(1, 3), Some(2));
        assert_eq!(m.insert(1, 4), Some(3));
    }

    #[test]
    fn test_remove() {
        let mut m = Map::new();
        m.insert(1, 2);
        assert_eq!(m.remove(&1), Some(2));
        assert_eq!(m.remove(&1), None);
    }

    #[test]
    fn test_from_iter() {
        let xs = [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6)];

        let map: Map<i32> = xs.iter().cloned().collect();

        for &(k, v) in xs.iter() {
            assert_eq!(map.get(&k), Some(&v));
        }
    }

    #[test]
    fn test_keys() {
        let vec = [(1, 'a'), (2, 'b'), (3, 'c')];
        let map: Map<_> = vec.iter().cloned().collect();
        let keys: Vec<_> = map.keys().collect();
        assert_eq!(keys.len(), 3);
        assert!(keys.contains(&1));
        assert!(keys.contains(&2));
        assert!(keys.contains(&3));
    }

    #[test]
    fn test_values() {
        let vec = [(1, 'a'), (2, 'b'), (3, 'c')];
        let map: Map<_> = vec.iter().cloned().collect();
        let values: Vec<_> = map.values().cloned().collect();
        assert_eq!(values.len(), 3);
        assert!(values.contains(&'a'));
        assert!(values.contains(&'b'));
        assert!(values.contains(&'c'));
    }

    #[test]
    fn test_iteration() {
        let empty_map : Map<usize> = Map::new();
        assert_eq!(empty_map.iter().next(), None);

        let first = usize::MAX - 10000;
        let last = usize::MAX;

        let mut map = Map::new();
        for x in (first..last).rev() {
            map.insert(x, x / 2);
        }

        let mut i = 0;
        for (k, &v) in map.iter() {
            assert_eq!(k, first + i);
            assert_eq!(v, k / 2);
            i += 1;
        }
        assert_eq!(i, last - first);
    }

    #[test]
    fn test_mut_iter() {
        let mut empty_map : Map<usize> = Map::new();
        assert!(empty_map.iter_mut().next().is_none());

        let first = usize::MAX - 10000;
        let last = usize::MAX;

        let mut map = Map::new();
        for x in (first..last).rev() {
            map.insert(x, x / 2);
        }

        let mut i = 0;
        for (k, v) in map.iter_mut() {
            assert_eq!(k, first + i);
            *v -= k / 2;
            i += 1;
        }
        assert_eq!(i, last - first);

        assert!(map.iter().all(|(_, &v)| v == 0));
    }

    #[test]
    fn test_bound() {
        let empty_map : Map<usize> = Map::new();
        assert_eq!(empty_map.lower_bound(0).next(), None);
        assert_eq!(empty_map.upper_bound(0).next(), None);

        let last = 999;
        let step = 3;
        let value = 42;

        let mut map : Map<usize> = Map::new();
        for x in (0..last).step_by(step) {
            assert!(x % step == 0);
            map.insert(x, value);
        }

        for i in 0..last - step {
            let mut lb = map.lower_bound(i);
            let mut ub = map.upper_bound(i);
            let next_key = i - i % step + step;
            let next_pair = (next_key, &value);
            if i % step == 0 {
                assert_eq!(lb.next(), Some((i, &value)));
            } else {
                assert_eq!(lb.next(), Some(next_pair));
            }
            assert_eq!(ub.next(), Some(next_pair));
        }

        let mut lb = map.lower_bound(last - step);
        assert_eq!(lb.next(), Some((last - step, &value)));
        let mut ub = map.upper_bound(last - step);
        assert_eq!(ub.next(), None);

        for i in last - step + 1..last {
            let mut lb = map.lower_bound(i);
            assert_eq!(lb.next(), None);
            let mut ub = map.upper_bound(i);
            assert_eq!(ub.next(), None);
        }
    }

    #[test]
    fn test_mut_bound() {
        let empty_map : Map<usize> = Map::new();
        assert_eq!(empty_map.lower_bound(0).next(), None);
        assert_eq!(empty_map.upper_bound(0).next(), None);

        let mut m_lower = Map::new();
        let mut m_upper = Map::new();
        for i in 0..100 {
            m_lower.insert(2 * i, 4 * i);
            m_upper.insert(2 * i, 4 * i);
        }

        for i in 0..199 {
            let mut lb_it = m_lower.lower_bound_mut(i);
            let (k, v) = lb_it.next().unwrap();
            let lb = i + i % 2;
            assert_eq!(lb, k);
            *v -= k;
        }

        for i in 0..198 {
            let mut ub_it = m_upper.upper_bound_mut(i);
            let (k, v) = ub_it.next().unwrap();
            let ub = i + 2 - i % 2;
            assert_eq!(ub, k);
            *v -= k;
        }

        assert!(m_lower.lower_bound_mut(199).next().is_none());
        assert!(m_upper.upper_bound_mut(198).next().is_none());

        assert!(m_lower.iter().all(|(_, &x)| x == 0));
        assert!(m_upper.iter().all(|(_, &x)| x == 0));
    }

    #[test]
    fn test_clone() {
        let mut a = Map::new();

        a.insert(1, 'a');
        a.insert(2, 'b');
        a.insert(3, 'c');

        assert!(a.clone() == a);
    }

    #[test]
    fn test_eq() {
        let mut a = Map::new();
        let mut b = Map::new();

        assert!(a == b);
        assert!(a.insert(0, 5).is_none());
        assert!(a != b);
        assert!(b.insert(0, 4).is_none());
        assert!(a != b);
        assert!(a.insert(5, 19).is_none());
        assert!(a != b);
        assert!(!b.insert(0, 5).is_none());
        assert!(a != b);
        assert!(b.insert(5, 19).is_none());
        assert!(a == b);
    }

    #[test]
    fn test_lt() {
        let mut a = Map::new();
        let mut b = Map::new();

        assert!(!(a < b) && !(b < a));
        assert!(b.insert(2, 5).is_none());
        assert!(a < b);
        assert!(a.insert(2, 7).is_none());
        assert!(!(a < b) && b < a);
        assert!(b.insert(1, 0).is_none());
        assert!(b < a);
        assert!(a.insert(0, 6).is_none());
        assert!(a < b);
        assert!(a.insert(6, 2).is_none());
        assert!(a < b && !(b < a));
    }

    #[test]
    fn test_ord() {
        let mut a = Map::new();
        let mut b = Map::new();

        assert!(a <= b && a >= b);
        assert!(a.insert(1, 1).is_none());
        assert!(a > b && a >= b);
        assert!(b < a && b <= a);
        assert!(b.insert(2, 2).is_none());
        assert!(b > a && b >= a);
        assert!(a < b && a <= b);
    }

    #[test]
    fn test_hash() {
        fn hash<T: Hash>(t: &T) -> u64 {
            let mut s = DefaultHasher::new();
            t.hash(&mut s);
            s.finish()
        }

        let mut x = Map::new();
        let mut y = Map::new();

        assert!(hash(&x) == hash(&y));
        x.insert(1, 'a');
        x.insert(2, 'b');
        x.insert(3, 'c');

        y.insert(3, 'c');
        y.insert(2, 'b');
        y.insert(1, 'a');

        assert!(hash(&x) == hash(&y));
    }

    #[test]
    fn test_debug() {
        let mut map = Map::new();
        let empty: Map<char> = Map::new();

        map.insert(1, 'a');
        map.insert(2, 'b');

        assert_eq!(format!("{:?}", map), "{1: 'a', 2: 'b'}");
        assert_eq!(format!("{:?}", empty), "{}");
    }

    #[test]
    fn test_index() {
        let mut map = Map::new();

        map.insert(1, 2);
        map.insert(2, 1);
        map.insert(3, 4);

        assert_eq!(map[&2], 1);
    }

    #[test]
    #[should_panic]
    fn test_index_nonexistent() {
        let mut map = Map::new();

        map.insert(1, 2);
        map.insert(2, 1);
        map.insert(3, 4);

        map[&4];
    }

    // Number of items to insert into the map during entry tests.
    // The tests rely on it being even.
    const SQUARES_UPPER_LIM: usize = 128;

    /// Make a map storing i^2 for i in [0, 128)
    fn squares_map() -> Map<usize> {
        let mut map = Map::new();
        for i in 0..SQUARES_UPPER_LIM {
            map.insert(i, i * i);
        }
        map
    }

    #[test]
    fn test_entry_get() {
        let mut map = squares_map();

        for i in 0..SQUARES_UPPER_LIM {
            match map.entry(i) {
                Occupied(slot) => assert_eq!(slot.get(), &(i * i)),
                Vacant(_) => panic!("Key not found.")
            }
        }
        check_integrity(&map.root);
    }

    #[test]
    fn test_entry_get_mut() {
        let mut map = squares_map();

        // Change the entries to cubes.
        for i in 0..SQUARES_UPPER_LIM {
            match map.entry(i) {
                Occupied(mut e) => {
                    *e.get_mut() = i * i * i;
                }
                Vacant(_) => panic!("Key not found.")
            }
            assert_eq!(map.get(&i).unwrap(), &(i * i * i));
        }

        check_integrity(&map.root);
    }

    #[test]
    fn test_entry_into_mut() {
        let mut map = Map::new();
        map.insert(3, 6);

        let value_ref = match map.entry(3) {
            Occupied(e) => e.into_mut(),
            Vacant(_) => panic!("Entry not found.")
        };

        assert_eq!(*value_ref, 6);
    }

    #[test]
    fn test_entry_take() {
        let mut map = squares_map();
        assert_eq!(map.len(), SQUARES_UPPER_LIM);

        // Remove every odd key, checking that the correct value is returned.
        for i in (1..SQUARES_UPPER_LIM).step_by(2) {
            match map.entry(i) {
                Occupied(e) => assert_eq!(e.remove(), i * i),
                Vacant(_) => panic!("Key not found.")
            }
        }

        check_integrity(&map.root);

        // Check that the values for even keys remain unmodified.
        for i in (0..SQUARES_UPPER_LIM).step_by(2) {
            assert_eq!(map.get(&i).unwrap(), &(i * i));
        }

        assert_eq!(map.len(), SQUARES_UPPER_LIM / 2);
    }

    #[test]
    fn test_occupied_entry_set() {
        let mut map = squares_map();

        // Change all the entries to cubes.
        for i in 0..SQUARES_UPPER_LIM {
            match map.entry(i) {
                Occupied(mut e) => assert_eq!(e.insert(i * i * i), i * i),
                Vacant(_) => panic!("Key not found.")
            }
            assert_eq!(map.get(&i).unwrap(), &(i * i * i));
        }
        check_integrity(&map.root);
    }

    #[test]
    fn test_vacant_entry_set() {
        let mut map = Map::new();

        for i in 0..SQUARES_UPPER_LIM {
            match map.entry(i) {
                Vacant(e) => {
                    // Insert i^2.
                    let inserted_val = e.insert(i * i);
                    assert_eq!(*inserted_val, i * i);

                    // Update it to i^3 using the returned mutable reference.
                    *inserted_val = i * i * i;
                },
                _ => panic!("Non-existent key found.")
            }
            assert_eq!(map.get(&i).unwrap(), &(i * i * i));
        }

        check_integrity(&map.root);
        assert_eq!(map.len(), SQUARES_UPPER_LIM);
    }

    #[test]
    fn test_single_key() {
        let mut map = Map::new();
        map.insert(1, 2);

        match map.entry(1) {
            Occupied(e) => { e.remove(); },
            _ => ()
        }
    }
}