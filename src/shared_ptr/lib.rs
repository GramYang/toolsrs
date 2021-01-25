use std::sync::atomic::{AtomicI32,Ordering};
use std::ptr;
use std::ops::{Deref,DerefMut};

pub struct RefCount {
    ref_count: AtomicI32,
    wref_count: AtomicI32,
}

impl RefCount {
    //生成RefCount实例，用Box入堆，再返回其可变指针
    #[inline]
    pub fn new() -> *mut RefCount {
        let r: Box<RefCount> = Box::new(RefCount {
            ref_count: AtomicI32::new(1),
            wref_count: AtomicI32::new(1),
        });
        let p: *mut RefCount = Box::into_raw(r);
        return p;
    }

    //还是释放
    #[inline]
    pub fn destroy(ptr: *mut RefCount) {
        unsafe {
            drop(Box::from_raw(ptr));
        }
    }

    #[inline]
    pub fn get_ref(&self) -> i32 {
        return self.ref_count.load(Ordering::SeqCst);
    }

    #[inline]
    pub fn get_wref(&self) -> i32 {
        return self.wref_count.load(Ordering::SeqCst);
    }

    #[inline]
    pub fn inc_ref(&self) {
        //文档https://doc.rust-lang.org/std/sync/atomic/struct.AtomicI32.html#method.fetch_add
        self.ref_count.fetch_add(1, Ordering::SeqCst);
    }

    //文档https://doc.rust-lang.org/std/sync/atomic/struct.AtomicI32.html#method.compare_and_swap
    #[inline]
    pub fn inc_ref_nz(&self) -> bool {
        let mut now = self.get_ref();
        while now != 0 {
            let old = self
                .ref_count
                .compare_and_swap(now, now + 1, Ordering::SeqCst);
            if old == now {
                return true;
            }
            now = old;
        }
        return false;
    }

    #[inline]
    pub fn inc_wref(&self) {
        self.wref_count.fetch_add(1, Ordering::SeqCst);
    }

    #[inline]
    pub fn dec_ref(&self) -> bool {
        let r = self.ref_count.fetch_add(-1, Ordering::SeqCst);
        return r == 1;
    }

    #[inline]
    pub fn dec_wref(&self) -> bool {
        let r = self.wref_count.fetch_add(-1, Ordering::SeqCst);
        return r == 1;
    }
}

pub struct SharedPtr<T: ?Sized> {
    ptr: *mut T,//包裹值的裸指针
    ref_count: *mut RefCount,//相关引用信息包的裸指针
}

impl<T: ?Sized> SharedPtr<T> {
    #[inline]
    pub fn new(b: Box<T>) -> SharedPtr<T> {
        let p: *mut T = Box::into_raw(b);
        SharedPtr::from_raw(p)
    }

    #[inline]
    pub fn from_raw(p: *mut T) -> SharedPtr<T> {
        if p.is_null() {
            return SharedPtr {
                ptr: p,
                ref_count: ptr::null_mut(),
            };
        }
        let ref_ptr: *mut RefCount = RefCount::new();
        SharedPtr {
            ptr: p,
            ref_count: ref_ptr,
        }
    }

    #[inline]
    pub fn get_mut_self(&self) -> &mut SharedPtr<T> {
        unsafe {
            let x = self as *const SharedPtr<T> as *mut SharedPtr<T>;
            return &mut *x;
        }
    }

    //析构函数
    #[inline]
    pub fn destroy(&self) {
        if !self.is_valid() {
            return;
        }
        //ref减1，如果ref减成0
        if self.get_refcount().dec_ref() {
            //释放ptr
            self.destroy_ptr();
            if self.get_refcount().dec_wref() {
                //ref_count释放后赋新值
                self.destroy_refcount();
            }
        }
    }

    //将ptr指向的堆值释放，ptr在这个方法退栈后也释放
    #[inline]
    pub fn destroy_ptr(&self) {
        unsafe {
            let _ = Box::from_raw(self.ptr);
            //use ref count to test the ptr is destroyed
            //not the ptr == null
        }
        //assert!(false);
    }

    //将ref及其指向值释放后赋新值
    #[inline]
    pub fn destroy_refcount(&self) {
        RefCount::destroy(self.ref_count);
        self.get_mut_self().ref_count = ptr::null_mut::<RefCount>();
    }

    //确认你的SharedPtr是否有效，其中的ref_count必须不为空且其中的ref必须大于0
    #[inline]
    pub fn is_valid(&self) -> bool {
        self.data_valid()
    }

    #[inline]
    pub fn data_valid(&self) -> bool {
        !self.ref_count.is_null() && self.get_refcount().get_ref() > 0
    }

    #[inline]
    pub fn refcount_valid(&self) -> bool {
        self.ref_count != ptr::null_mut()
    }

    #[inline]
    pub fn get_refcount(&self) -> &mut RefCount {
        unsafe { &mut *self.ref_count }
    }

    #[inline]
    pub fn get_mut(&self) -> &mut T {
        unsafe { &mut *self.ptr }
    }

    #[inline]
    pub fn get_raw(&self) -> (*mut T, *mut RefCount) {
        (self.ptr, self.ref_count)
    }
}

impl<T: ?Sized> Drop for SharedPtr<T> {
    fn drop(&mut self) {
        self.destroy();
    }
}

impl<T: ?Sized> Clone for SharedPtr<T> {
    //clone会增加ref，并返回一个SharedPtr
    fn clone(&self) -> Self {
        self.get_refcount().inc_ref();

        SharedPtr {
            ptr: self.ptr,
            ref_count: self.ref_count,
        }
    }

    fn clone_from(&mut self, source: &Self) {
        self.destroy();

        self.ptr = source.ptr.clone();
        self.ref_count = source.ref_count.clone();
        self.get_refcount().inc_ref();
    }
}

impl<T: ?Sized> Deref for SharedPtr<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.get_mut()
    }
}

impl<T: ?Sized> DerefMut for SharedPtr<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.get_mut()
    }
}

unsafe impl<T: ?Sized> Send for SharedPtr<T> {}
unsafe impl<T: ?Sized> Sync for SharedPtr<T> {}

pub struct WeakPtr<T: ?Sized> {
    ptr: *mut T,
    ref_count: *mut RefCount,
}

impl<T: ?Sized> WeakPtr<T> {
    //如果ref_count不为空，wref+1，返回WeakPtr
    #[inline]
    pub fn new(s: &SharedPtr<T>) -> WeakPtr<T> {
        let (ptr, ref_count) = s.get_raw();
        if ref_count != ptr::null_mut() {
            unsafe {
                (*ref_count).inc_wref();
            }
        }

        WeakPtr {
            ptr: ptr,
            ref_count: ref_count,
        }
    }

    #[inline]
    pub fn destroy(&self) {
        if !self.is_valid() {
            return;
        }
        if self.get_mut().dec_wref() {
            self.destroy_refcount();
        }
    }

    #[inline]
    pub fn get_mut_self(&self) -> &mut WeakPtr<T> {
        unsafe {
            let x = self as *const WeakPtr<T> as *mut WeakPtr<T>;
            return &mut *x;
        }
    }

    #[inline]
    pub fn destroy_refcount(&self) {
        RefCount::destroy(self.ref_count);
        self.get_mut_self().ref_count = ptr::null_mut();
        //assert!(false);
    }

    #[inline]
    pub fn is_valid(&self) -> bool {
        self.ref_count != ptr::null_mut()
    }

    #[inline]
    pub fn get_mut(&self) -> &mut RefCount {
        unsafe { &mut *self.ref_count }
    }

    #[inline]
    pub fn lock(&self) -> Option<SharedPtr<T>> {
        //将ref+1，如果成功则返回Some(r)
        if self.ref_count != ptr::null_mut() && self.get_mut().inc_ref_nz() {
            let r = SharedPtr {
                ptr: self.ptr,
                ref_count: self.ref_count,
            };
            return Some(r);
        }
        return None;
    }
}

impl<T: ?Sized> Drop for WeakPtr<T> {
    fn drop(&mut self) {
        self.destroy();
    }
}

impl<T: ?Sized> Clone for WeakPtr<T> {
    fn clone(&self) -> Self {
        self.get_mut().inc_wref();

        WeakPtr {
            ptr: self.ptr,
            ref_count: self.ref_count,
        }
    }

    fn clone_from(&mut self, source: &Self) {
        self.destroy();

        self.ptr = source.ptr.clone();
        self.ref_count = source.ref_count.clone();
        self.get_mut().inc_wref();
    }
}

unsafe impl<T: ?Sized> Send for WeakPtr<T> {}
unsafe impl<T: ?Sized> Sync for WeakPtr<T> {}