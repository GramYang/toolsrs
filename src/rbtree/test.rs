#[cfg(test)]
mod test{
    use crate::rbtree::rbtree::RbTree;

    #[test]
    fn test_insert(){
        let mut m = RbTree::new();
        assert_eq!(m.len(), 0);
        m.insert(1, 2);
        assert_eq!(m.len(), 1);
        m.insert(2, 4);
        assert_eq!(m.len(), 2);
        assert_eq!(*m.get(&1).unwrap(), 2);
        assert_eq!(*m.get(&2).unwrap(), 4);
    }
}