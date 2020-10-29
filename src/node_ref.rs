use std::intrinsics::atomic_store;
use std::ops::Deref;
use std::ptr;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering::{self, Relaxed as DefaultOrdering};

#[derive(Debug)]
pub struct NodeContainer {
    node: *mut usize,
    counter: AtomicUsize,
}

impl NodeContainer {
    pub fn new(node: *mut usize) -> Self {
        Self {
            node,
            counter: AtomicUsize::new(1),
        }
    }

    pub fn add_ref(&self) {
        self.counter.fetch_add(1, DefaultOrdering);
    }

    /// Called when removing a reference. Container will decrease ref count and
    /// reclaim space pointered by `node` field. Return a bool indicates this
    /// countainer needs to be reclaim or not.
    pub fn del_ref(&self) -> bool {
        if self.counter.fetch_sub(1, DefaultOrdering) == 1 {
            self.reclaim();
            return true;
        }
        return false;
    }

    fn reclaim(&self) {}
}

/// A reference to underlying `NodeContainer`. This struct itself is not thread safe.
/// Additional operation like lock or atomic write should be taken to ensure lock-free
/// read is safe.
#[derive(Debug)]
pub struct NodeRef {
    ptr: *mut NodeContainer,
}

impl NodeRef {
    pub fn new(node: *mut usize) -> Self {
        let container = NodeContainer::new(node);
        let c_ptr = Box::into_raw(Box::new(container));
        Self { ptr: c_ptr }
    }

    pub fn from_container(ptr: *mut NodeContainer) -> Self {
        Self { ptr }
    }

    pub fn refer(&self) -> Self {
        unsafe {
            (*self.ptr).add_ref();
        }
        Self { ptr: self.ptr }
    }

    pub fn swap(&self, rhs: Self) {}

    pub fn replace(&self, rhs: Self) {}

    // evict self's value (invalid this NodeRef) and return previous value.
    // maybe `into_raw` or `into_inner` is more appropriate?
    pub fn evict(&self) -> Self {
        unimplemented!()
    }

    pub fn load(&self, ordering: Ordering) -> *mut usize {
        unsafe { (*self.ptr).node }
    }

    /// User should guarantee no data race. Like keeping
    pub fn store(&self, ptr: *mut usize, _ordering: Ordering) {
        unsafe {
            atomic_store(
                &(self.ptr as usize) as *const usize as *mut usize,
                ptr as usize,
            );
        }
        // todo!("replace this")
    }
}

impl Drop for NodeRef {
    fn drop(&mut self) {
        unsafe {
            if (*self.ptr).del_ref() {
                let _ = Box::from_raw(self.ptr);
            }
        }
    }
}

impl Default for NodeRef {
    fn default() -> Self {
        Self {
            ptr: ptr::null_mut(),
        }
    }
}

impl Deref for NodeRef {
    type Target = *mut usize;

    fn deref(&self) -> &Self::Target {
        unsafe { &(*self.ptr).node }
    }
}
