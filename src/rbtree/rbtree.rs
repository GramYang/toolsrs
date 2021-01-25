// 参考https://github.com/tickbh/rbtree-rs
use std::ptr;
use std::cmp::Ordering;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum Color{
    Red,Black
}

pub struct RbTree<K:Ord,V>{
    root:NodePtr<K,V>,
    len:usize,
}

struct NodePtr<K:Ord,V>(*mut RbTreeNode<K,V>);

struct RbTreeNode<K:Ord,V>{
    color:Color,
    left:NodePtr<K,V>,
    right:NodePtr<K,V>,
    parent:NodePtr<K,V>,
    key:K,
    value:V,
}

/*********************RbTree实现*****************************/

impl<K:Ord,V>RbTree<K,V>{
    pub fn new()->RbTree<K,V>{
        RbTree{
            root:NodePtr::null(),
            len:0,
        }
    }

    #[inline]
    pub fn len(&self)->usize{
        self.len
    }

    #[inline]
    pub fn insert(&mut self,k:K,v:V){
        self.len+=1;
        let mut node=NodePtr::new(k,v);
        let mut y=NodePtr::null();
        let mut x=self.root;
        while !x.is_null(){
            y=x;
            match node.cmp(&&mut x){
                Ordering::Less=>{
                    x=x.left();
                }
                _=>{
                    x=x.right();
                }
            };
        }
        node.set_parent(y);
        if y.is_null() {
            self.root = node;
        } else {
            match node.cmp(&&mut y) {
                Ordering::Less => {
                    y.set_left(node);
                }
                _ => {
                    y.set_right(node);
                }
            };
        }

        node.set_red_color();
        unsafe {
            self.insert_fixup(node);
        }
    }

    #[inline]
    unsafe fn insert_fixup(&mut self, mut node: NodePtr<K, V>) {
        let mut parent;
        let mut gparent;

        while node.parent().is_red_color() {
            parent = node.parent();
            gparent = parent.parent();
            //若“父节点”是“祖父节点的左孩子”
            if parent == gparent.left() {
                // Case 1条件：叔叔节点是红色
                let mut uncle = gparent.right();
                if !uncle.is_null() && uncle.is_red_color() {
                    uncle.set_black_color();
                    parent.set_black_color();
                    gparent.set_red_color();
                    node = gparent;
                    continue;
                }

                // Case 2条件：叔叔是黑色，且当前节点是右孩子
                if parent.right() == node {
                    self.left_rotate(parent);
                    let temp = parent;
                    parent = node;
                    node = temp;
                }

                // Case 3条件：叔叔是黑色，且当前节点是左孩子。
                parent.set_black_color();
                gparent.set_red_color();
                self.right_rotate(gparent);
            } else {
                // Case 1条件：叔叔节点是红色
                let mut uncle = gparent.left();
                if !uncle.is_null() && uncle.is_red_color() {
                    uncle.set_black_color();
                    parent.set_black_color();
                    gparent.set_red_color();
                    node = gparent;
                    continue;
                }

                // Case 2条件：叔叔是黑色，且当前节点是右孩子
                if parent.left() == node {
                    self.right_rotate(parent);
                    let temp = parent;
                    parent = node;
                    node = temp;
                }

                // Case 3条件：叔叔是黑色，且当前节点是左孩子。
                parent.set_black_color();
                gparent.set_red_color();
                self.left_rotate(gparent);
            }
        }
        self.root.set_black_color();
    }

    /*
     * 对红黑树的节点(x)进行左旋转
     *
     * 左旋示意图(对节点x进行左旋)：
     *      px                              px
     *     /                               /
     *    x                               y
     *   /  \      --(左旋)-->           / \                #
     *  lx   y                          x  ry
     *     /   \                       /  \
     *    ly   ry                     lx  ly
     *
     *
     */
    #[inline]
    unsafe fn left_rotate(&mut self, mut node: NodePtr<K, V>) {
        let mut temp = node.right();
        node.set_right(temp.left());

        if !temp.left().is_null() {
            temp.left().set_parent(node.clone());
        }

        temp.set_parent(node.parent());
        if node == self.root {
            self.root = temp.clone();
        } else if node == node.parent().left() {
            node.parent().set_left(temp.clone());
        } else {
            node.parent().set_right(temp.clone());
        }

        temp.set_left(node.clone());
        node.set_parent(temp.clone());
    }

    /*
     * 对红黑树的节点(y)进行右旋转
     *
     * 右旋示意图(对节点y进行左旋)：
     *            py                               py
     *           /                                /
     *          y                                x
     *         /  \      --(右旋)-->            /  \                     #
     *        x   ry                           lx   y
     *       / \                                   / \                   #
     *      lx  rx                                rx  ry
     *
     */
    #[inline]
    unsafe fn right_rotate(&mut self, mut node: NodePtr<K, V>) {
        let mut temp = node.left();
        node.set_left(temp.right());

        if !temp.right().is_null() {
            temp.right().set_parent(node.clone());
        }

        temp.set_parent(node.parent());
        if node == self.root {
            self.root = temp.clone();
        } else if node == node.parent().right() {
            node.parent().set_right(temp.clone());
        } else {
            node.parent().set_left(temp.clone());
        }

        temp.set_right(node.clone());
        node.set_parent(temp.clone());
    }

    #[inline]
    pub fn get(&self, k: &K) -> Option<&V> {
        let node = self.find_node(k);
        if node.is_null() {
            return None;
        }

        unsafe { Some(&(*node.0).value) }
    }

    #[inline]
    fn find_node(&self, k: &K) -> NodePtr<K, V> {
        if self.root.is_null() {
            return NodePtr::null();
        }
        let mut temp = &self.root;
        unsafe {
            loop {
                let next = match k.cmp(&(*temp.0).key) {
                    Ordering::Less => &mut (*temp.0).left,
                    Ordering::Greater => &mut (*temp.0).right,
                    Ordering::Equal => return *temp,
                };
                if next.is_null() {
                    break;
                }
                temp = next;
            }
        }
        NodePtr::null()
    }
}

/*********************NodePtr实现*****************************/

impl<K:Ord,V>NodePtr<K,V>{
    fn new(k: K, v: V) -> NodePtr<K, V> {
        let node = RbTreeNode {
            color: Color::Black,
            left: NodePtr::null(),
            right: NodePtr::null(),
            parent: NodePtr::null(),
            key: k,
            value: v,
        };
        NodePtr(Box::into_raw(Box::new(node)))
    }

    #[inline]
    fn null()->NodePtr<K,V>{
        NodePtr(ptr::null_mut())
    }

    #[inline]
    fn is_null(&self)->bool{
        self.0.is_null()
    }

    #[inline]
    fn left(&self) -> NodePtr<K, V> {
        if self.is_null() {
            return NodePtr::null();
        }
        unsafe { (*self.0).left.clone() }
    }

    #[inline]
    fn right(&self) -> NodePtr<K, V> {
        if self.is_null() {
            return NodePtr::null();
        }
        unsafe { (*self.0).right.clone() }
    }

    #[inline]
    fn set_parent(&mut self, parent: NodePtr<K, V>) {
        if self.is_null() {
            return;
        }
        unsafe { (*self.0).parent = parent }
    }

    #[inline]
    fn set_left(&mut self, left: NodePtr<K, V>) {
        if self.is_null() {
            return;
        }
        unsafe { (*self.0).left = left }
    }

    #[inline]
    fn set_right(&mut self, right: NodePtr<K, V>) {
        if self.is_null() {
            return;
        }
        unsafe { (*self.0).right = right }
    }

    #[inline]
    fn parent(&self) -> NodePtr<K, V> {
        if self.is_null() {
            return NodePtr::null();
        }
        unsafe { (*self.0).parent.clone() }
    }

    #[inline]
    fn set_red_color(&mut self) {
        self.set_color(Color::Red);
    }

    #[inline]
    fn set_black_color(&mut self) {
        self.set_color(Color::Black);
    }

    #[inline]
    fn is_red_color(&self) -> bool {
        if self.is_null() {
            return false;
        }
        unsafe { (*self.0).color == Color::Red }
    }

    #[inline]
    fn is_black_color(&self) -> bool {
        if self.is_null() {
            return true;
        }
        unsafe { (*self.0).color == Color::Black }
    }

    #[inline]
    fn set_color(&mut self, color: Color) {
        if self.is_null() {
            return;
        }
        unsafe {
            (*self.0).color = color;
        }
    }

    #[inline]
    fn is_left_child(&self) -> bool {
        self.parent().left() == *self
    }

    #[inline]
    fn is_right_child(&self) -> bool {
        self.parent().right() == *self
    }

}

//实现了Copy，NodePtr就可以用等号而不报错move
impl<K:Ord,V>Copy for NodePtr<K,V>{}

//你实现了Copy就必须也实现Clone
impl<K:Ord,V>Clone for NodePtr<K,V>{
    fn clone(&self)->NodePtr<K,V>{
        NodePtr(self.0)
    }
}

//Ord和PartialOrd和PartialEq和Eq要一起实现
impl<K:Ord,V>Ord for NodePtr<K,V>{
    fn cmp(&self,other:&NodePtr<K,V>)->Ordering{
        unsafe {(*self.0).key.cmp(&(*other.0).key)}
    }
}

impl<K: Ord, V> PartialOrd for NodePtr<K, V> {
    fn partial_cmp(&self, other: &NodePtr<K, V>) -> Option<Ordering> {
        unsafe { Some((*self.0).key.cmp(&(*other.0).key)) }
    }
}

impl<K: Ord, V> PartialEq for NodePtr<K, V> {
    fn eq(&self, other: &NodePtr<K, V>) -> bool {
        self.0 == other.0
    }
}

impl<K: Ord, V> Eq for NodePtr<K, V> {}