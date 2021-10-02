use std::ptr::NonNull;

use crate::sync::{AtomicPtr, AtomicUsize, Mutex, MutexGuard, Ordering};

crate struct NodePtr {
    ptr: AtomicPtr<NodeRc>,
    mutex: Mutex<()>,
}

impl NodePtr {
    crate fn new<T>(ptr: *mut T) -> Self {
        let ptr = NodeRc::new_boxed(NonNull::new(ptr as _).unwrap());

        Self {
            ptr: AtomicPtr::new(ptr),
            mutex: Mutex::new(()),
        }
    }

    /// Get a shared reference.
    ///
    /// The ref holds one reference counting, thus it is legal as long as it exist.
    crate fn read(&self) -> NodeRef {
        let ptr = self.ptr.load(Ordering::SeqCst);
        println!("read ptr: {:?}", ptr);
        unsafe {
            (*ptr).increase();
            NodeRef {
                ptr: NonNull::new_unchecked(ptr),
            }
        }
    }

    /// Get a unique mutable reference.
    ///
    /// This ref won't increase underlying reference counter. Its lifetime is bounded to
    /// the [NodePtr].
    crate fn write(&self) -> NodeRefMut {
        let guard = self.mutex.lock().unwrap();
        NodeRefMut { ptr: self, guard }
    }
}

impl Drop for NodePtr {
    fn drop(&mut self) {
        let ptr = self.ptr.load(Ordering::SeqCst);
        unsafe {
            NodeRc::destroy(ptr);
        }
    }
}

crate struct NodeRef {
    ptr: NonNull<NodeRc>,
}

impl NodeRef {
    crate fn get(&self) -> NonNull<()> {
        unsafe { self.ptr.as_ref().ptr }
    }
}

impl Drop for NodeRef {
    fn drop(&mut self) {
        let ptr = self.ptr.as_ptr();
        unsafe {
            NodeRc::destroy(ptr);
        }
    }
}

crate struct NodeRefMut<'a> {
    ptr: &'a NodePtr,
    guard: MutexGuard<'a, ()>,
}

impl<'a> NodeRefMut<'a> {
    crate fn get(&self) -> NonNull<()> {
        unsafe { (*self.ptr.ptr.load(Ordering::SeqCst)).ptr }
    }

    /// Replace source [NodePtr]'s pointer.
    crate fn replace<T>(&self, ptr: *mut T) {
        let new_rc = NodeRc::new_boxed(NonNull::new(ptr as _).unwrap());
        let replaced = self.ptr.ptr.swap(new_rc, Ordering::SeqCst);
        unsafe {
            NodeRc::destroy(replaced);
        }
    }
}

crate struct NodeRc {
    ptr: NonNull<()>,
    count: AtomicUsize,
}

impl NodeRc {
    fn new_boxed(ptr: NonNull<()>) -> *mut Self {
        let rc = Self {
            ptr,
            count: AtomicUsize::new(1),
        };
        Box::into_raw(Box::new(rc))
    }

    fn increase(&self) {
        self.count.fetch_add(1, Ordering::SeqCst);
    }

    /// Return `true` if it's the last reference.
    fn decrease(&self) -> bool {
        if self.count.fetch_sub(1, Ordering::SeqCst) <= 1 {
            // todo: drop node
            true
        } else {
            false
        }
    }

    unsafe fn destroy(ptr: *mut Self) {
        if (*ptr).decrease() {
            println!("destroying {:?}", (*ptr).ptr);
            Box::from_raw(ptr);
        }
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

            let node_write = node.clone();
            let writer = thread::spawn(move || {
                let write_ref = node_write.write();
                write_ref.replace(0x2usize as *mut ());

                let ptr = write_ref.get();
                let addr = ptr.as_ptr() as usize;
                assert_eq!(addr, 0x2usize);
                println!("writer finished");
            });

            let read_ref = node.read();
            let reader = thread::spawn(move || {
                println!("reader start");
                let ptr = read_ref.get();
                let addr = ptr.as_ptr() as usize;
                assert_eq!(addr, 0x1usize);
            });

            writer.join().unwrap();
            reader.join().unwrap();
        })
    }
}
