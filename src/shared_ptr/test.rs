//这是群里面四神的项目：https://gitee.com/egmkang/shared_ptr-rs
#[cfg(test)]
mod test{
    use crate::shared_ptr::lib::{RefCount,SharedPtr,WeakPtr};

    //RefCount简单测试
    #[test]
    fn ref_count_add_and_sub() {
        let rc = RefCount::new();
        let reference: &RefCount = unsafe { &*rc };
        assert_eq!(1, reference.get_ref());
        assert_eq!(1, reference.get_wref());

        reference.inc_ref();
        assert_eq!(2, reference.get_ref());
        reference.inc_ref();
        assert_eq!(3, reference.get_ref());

        reference.inc_wref();
        assert_eq!(2, reference.get_wref());

        let r1 = reference.dec_ref();
        assert!(!r1);
        assert_eq!(2, reference.get_ref());

        let r2 = reference.dec_ref();
        assert!(!r2);
        assert_eq!(1, reference.get_ref());

        let r = reference.dec_ref();
        assert!(r);
        assert_eq!(0, reference.get_ref());
    }

    //RefCount简单测试
    #[test]
    fn ref_count_inc_ref_nz() {
        let rc = RefCount::new();
        let reference: &RefCount = unsafe { &*rc };

        assert_eq!(1, reference.get_ref());

        reference.dec_ref();

        let r = reference.inc_ref_nz();
        assert!(!r);

        reference.inc_ref();
        let r1 = reference.inc_ref_nz();
        assert!(r1);
        assert_eq!(2, reference.get_ref());
    }

    //SharedPtr简单测试
    #[test]
    fn shared_ptr_simple_test() {
        let p: SharedPtr<i32> = SharedPtr::new(Box::new(1));

        assert_eq!(1, *p.get_mut());

        *p.get_mut() = 2;
        assert_eq!(2, *p.get_mut());

        //move here
        let x = p;
        assert_eq!(2, *x.get_mut());
    }

    //SharedPtr简单测试
    #[test]
    fn shared_ptr_test_drop() {
        let p: SharedPtr<i32> = SharedPtr::new(Box::new(1));
        drop(p);
    }

    //SharedPtr关键测试
    #[test]
    fn shared_ptr_clone() {
        let p: SharedPtr<i32> = SharedPtr::new(Box::new(1));
        //每次clone都会增加ref
        let x = p.clone();

        assert_eq!(1, *p.get_mut());

        *x.get_mut() = 2;
        assert_eq!(2, *p.get_mut());
        assert_eq!(2, *x.get_mut());

        assert_eq!(2, p.get_refcount().get_ref());
        assert_eq!(1, p.get_refcount().get_wref());

        let z = x.clone();

        assert_eq!(3, x.get_refcount().get_ref());
        assert_eq!(1, x.get_refcount().get_wref());
        //ref减1，减到0后就destroy
        drop(p);
        drop(z);

        assert_eq!(1, x.get_refcount().get_ref());
        assert_eq!(1, x.get_refcount().get_wref());

        drop(x);
    }

    struct Sample {
        num: i32,
    }

    impl Sample {
        pub fn new(i: i32) -> Sample {
            Sample { num: i }
        }

        pub fn get_number(&self) -> i32 {
            return self.num;
        }
    }

    #[test]
    fn shared_ptr_deref() {
        let p: SharedPtr<Sample> = SharedPtr::new(Box::new(Sample::new(10)));
        assert_eq!(10, p.get_number());
        p.get_mut().num = 20;
        assert_eq!(20, p.get_number())
    }

    #[test]
    fn weak_ptr_lock() {
        let p: SharedPtr<i32> = SharedPtr::new(Box::new(1));
        let w = WeakPtr::new(&p);//这里会将wref+1

        assert_eq!(2, p.get_refcount().get_wref());

        let l = w.lock();//这里ref+1
        match l {
            None => assert!(false),
            Some(r) => {
                assert_eq!(2, r.get_refcount().get_ref());
                *r.get_mut() = 10;
                assert_eq!(10, *r.get_mut());
            }
        }
    }

    #[test]
    fn weak_ptr_lock_after_drop() {
        let p: SharedPtr<i32> = SharedPtr::new(Box::new(1));
        let w = WeakPtr::new(&p);

        drop(p);

        let l = w.lock();
        match l {
            Some(r) => assert!(false),
            None => assert!(true),
        }
    }

    #[test]
    fn weak_ptr_clone() {
        let p: SharedPtr<i32> = SharedPtr::new(Box::new(1));
        let w = WeakPtr::new(&p);

        let c = w.clone();
        assert_eq!(3, c.get_mut().get_wref());

        drop(c);
        assert_eq!(2, w.get_mut().get_wref());

        *p.get_mut() = 10;
        assert_eq!(10, *p.get_mut());

        let w1 = w.clone();

        if let Some(p1) = w1.lock() {
            assert!(p1.is_valid());
            assert_eq!(10, *p1.get_mut());

            drop(p);
            drop(p1);

            let p2 = w1.lock();
            assert!(p2.is_none());
        } else {
            assert!(false);
        }
    }
}

