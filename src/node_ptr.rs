use std::ptr::NonNull;

use loom::sync::atomic::AtomicIsize;

use crate::sync::{Alloc, AtomicPtr, Mutex, MutexGuard, Ordering};

pub(crate) struct NodePtr {
    ptr: AtomicPtr<NodeRc>,
    mutex: Mutex<()>,
    phantom_rc: AtomicIsize,
}

impl NodePtr {
    pub(crate) fn new<T>(ptr: *mut T) -> Self {
        let ptr = NodeRc::new_boxed(NonNull::new(ptr as _).unwrap());

        Self {
            ptr: AtomicPtr::new(ptr),
            mutex: Mutex::new(()),
            phantom_rc: AtomicIsize::new(0),
        }
    }

    /// Get a shared reference.
    ///
    /// The ref holds one reference counting, thus it is legal as long as it exist.
    pub(crate) fn read(&self) -> NodeRef {
        let phantom_rc = self.phantom_rc.fetch_add(1, Ordering::SeqCst) + 1;
        let ptr = self.ptr.load(Ordering::SeqCst);
        unsafe {
            NodeRc::accumulate_rc(ptr, 1);
            self.phantom_rc.fetch_add(-1, Ordering::SeqCst);
            // if self.phantom_rc.fetch_add(-1, Ordering::SeqCst) < phantom_rc {
            //     NodeRc::accumulate_rc(ptr, -1);
            //     self.phantom_rc.fetch_add(1, Ordering::SeqCst);
            // }
            NodeRef {
                ptr: NonNull::new_unchecked(ptr),
            }
        }
    }

    /// Get a unique mutable reference.
    ///
    /// This ref won't increase underlying reference counter. Its lifetime is bounded to
    /// the [NodePtr].
    pub(crate) fn write(&self) -> NodeRefMut {
        let guard = self.mutex.lock().unwrap();
        NodeRefMut { ptr: self, guard }
    }
}

impl Drop for NodePtr {
    fn drop(&mut self) {
        let ptr = self.ptr.load(Ordering::SeqCst);
        unsafe {
            NodeRc::accumulate_rc(ptr, -1);
        }
    }
}

pub(crate) struct NodeRef {
    ptr: NonNull<NodeRc>,
}

impl NodeRef {
    pub(crate) fn get(&self) -> NonNull<()> {
        unsafe { self.ptr.as_ref().ptr }
    }
}

impl Drop for NodeRef {
    fn drop(&mut self) {
        let ptr = self.ptr.as_ptr();
        unsafe {
            NodeRc::accumulate_rc(ptr, -1);
        }
    }
}

pub(crate) struct NodeRefMut<'a> {
    ptr: &'a NodePtr,
    guard: MutexGuard<'a, ()>,
}

impl<'a> NodeRefMut<'a> {
    pub(crate) fn get(&self) -> NonNull<()> {
        unsafe { (*self.ptr.ptr.load(Ordering::SeqCst)).ptr }
    }

    /// Replace source [NodePtr]'s pointer.
    pub(crate) fn replace<T>(&self, ptr: *mut T) {
        let new_item = NodeRc::new_boxed(NonNull::new(ptr as _).unwrap());
        let replaced = self.ptr.ptr.swap(new_item, Ordering::SeqCst);
        // let phantom_rc = self.ptr.phantom_rc.swap(0, Ordering::SeqCst) - 1;
        let phantom_rc = self.ptr.phantom_rc.load(Ordering::SeqCst);
        unsafe {
            if phantom_rc == 0 {
                NodeRc::accumulate_rc(replaced, -1);
            } else {
                NodeRc::decrease_one(replaced);
            }
        }
    }
}

pub(crate) struct NodeRc {
    ptr: NonNull<()>,
    count: AtomicIsize,
}

impl NodeRc {
    fn new_boxed(ptr: NonNull<()>) -> *mut Self {
        let rc = Self {
            ptr,
            count: AtomicIsize::new(1),
        };
        Box::into_raw(Box::new_in(rc, Alloc))
    }

    unsafe fn accumulate_rc(ptr: *mut Self, rc: isize) {
        let updated = (*ptr).count.fetch_add(rc, Ordering::SeqCst) + rc;
        println!("{:?} accumulate rc {}, after: {}", (*ptr).ptr, rc, updated);
        if updated < 1 {
            println!("destroy after accumulate {:?}", (*ptr).ptr);
            Box::from_raw_in(ptr, Alloc);
        }
    }

    unsafe fn decrease_one(ptr: *mut Self) {
        (*ptr).count.fetch_add(-1, Ordering::SeqCst);
        println!("{:?} decrease one", (*ptr).ptr);
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::sync::Arc;
    use loom::thread;

    #[test]
    fn rw() {
        loom::model(|| {
            let node_ptr = NodePtr::new(0x1usize as *mut ());
            let node = Arc::new(node_ptr);

            let read_ref_before = node.read();
            let reader_before = thread::spawn(move || {
                let ptr = read_ref_before.get();
                let addr = ptr.as_ptr() as usize;
                assert_eq!(addr, 0x1usize);
            });

            let node_write = node.clone();
            let writer = thread::spawn(move || {
                let write_ref = node_write.write();
                write_ref.replace(0x2usize as *mut ());

                let ptr = write_ref.get();
                let addr = ptr.as_ptr() as usize;
                assert_eq!(addr, 0x2usize);
            });

            let read_ref_after = node.read();
            let reader_after = thread::spawn(move || {
                let ptr = read_ref_after.get();
                let addr = ptr.as_ptr() as usize;
                // read starts after writer is indeterminate.
                assert!((addr == 0x1usize) || (addr == 0x2usize));
            });

            reader_before.join().unwrap();
            writer.join().unwrap();
            reader_after.join().unwrap();

            // read after finished write is deterministic.
            // let read_ref_after_all = node.read();
            // thread::spawn(move || {
            //     let ptr = read_ref_after_all.get();
            //     let addr = ptr.as_ptr() as usize;
            //     assert_eq!(addr, 0x2usize);
            // })
            // .join()
            // .unwrap();
        })
    }

    #[test]
    fn loom_alloc() {
        loom::model(|| {
            let rc = NodeRc::new_boxed(NonNull::new(0x1usize as *mut ()).unwrap());
            unsafe { NodeRc::accumulate_rc(rc, -1) };
        })
    }

    #[test]
    fn single_write() {
        loom::model(|| {
            let node_ptr = NodePtr::new(0x1usize as *mut ());
            let node = Arc::new(node_ptr);

            let node_write = node.clone();
            let writer = thread::spawn(move || {
                let write_ref = node_write.write();
                write_ref.replace(0x2usize as *mut ());

                let ptr = write_ref.get();
                let addr = ptr.as_ptr() as usize;
                assert_eq!(addr, 0x2usize);
            });

            writer.join().unwrap();
        })
    }

    #[test]
    fn read_before_write_begin() {
        loom::model(|| {
            let node_ptr = NodePtr::new(0x1usize as *mut ());
            let node = Arc::new(node_ptr);

            let read_ref = node.read();
            let reader = thread::spawn(move || {
                println!("reader thread begin");
                let ptr = read_ref.get();
                let addr = ptr.as_ptr() as usize;
                assert_eq!(addr, 0x1usize);
                println!("reader thread finish");
            });

            let node_write = node.clone();
            let writer = thread::spawn(move || {
                println!("writer thread begin");
                let write_ref = node_write.write();
                write_ref.replace(0x2usize as *mut ());

                let ptr = write_ref.get();
                let addr = ptr.as_ptr() as usize;
                assert_eq!(addr, 0x2usize);
                println!("writer thread finish");
            });

            reader.join().unwrap();
            writer.join().unwrap();
        })
    }

    #[test]
    fn read_after_write_begin() {
        loom::model(|| {
            let node_ptr = NodePtr::new(0x1usize as *mut ());
            let node = Arc::new(node_ptr);

            let node_write = node.clone();
            let writer = thread::spawn(move || {
                println!("writer thread begin");
                let write_ref = node_write.write();
                write_ref.replace(0x2usize as *mut ());

                let ptr = write_ref.get();
                let addr = ptr.as_ptr() as usize;
                assert_eq!(addr, 0x2usize);
                println!("writer thread finish");
            });

            let read_ref = node.read();
            let reader = thread::spawn(move || {
                println!("reader thread begin");
                let ptr = read_ref.get();
                let addr = ptr.as_ptr() as usize;
                assert_eq!(addr, 0x1usize);
                println!("reader thread finish");
            });

            writer.join().unwrap();
            reader.join().unwrap();
        })
    }
}
