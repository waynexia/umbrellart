use std::intrinsics::{atomic_store, atomic_xchg};
use std::ops::Deref;
use std::ptr;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering::{self, Relaxed as DefaultOrdering};

#[derive(Debug)]
struct NodeContainer {
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
///
/// This Ref can be used to achieve two access mode, read and write in particular. For
/// `Read` access, one can make a copy of node by refer() method. The copy provides reader
/// a ensurance that this node won't be reclaimed during read operation. And in this mode
/// every node operation is operating on a "mirror NodeRef" creates by refer(), which means
/// underlying container cannot be replaced. On the contrary, `Write` mode happens when
/// directly operating on the NodeRef stored in tree, so replacing underlying container is
/// persistent.
#[derive(Debug)]
pub struct NodeRef {
    ptr: *mut NodeContainer,
}

impl NodeRef {
    pub fn new(node: *mut usize) -> Self {
        let container = NodeContainer::new(node);
        let ptr = Box::into_raw(Box::new(container));
        Self { ptr }
    }

    // pub fn from_container(ptr: *mut NodeContainer) -> Self {
    //     Self { ptr }
    // }

    pub fn refer(&self) -> Self {
        if self.ptr.is_null() {
            return Self::default();
        }

        unsafe {
            (*self.ptr).add_ref();
        }
        Self { ptr: self.ptr }
    }

    // below are deprecated
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
    // above are deprecated.

    /// User should guarantee no data race. Like keeping a lock.
    /// This method will decrease previous underlying container's reference count if have.
    ///
    /// This method should not be called directly? Use replace_with() instead.
    pub fn replace_underlying(&self, ptr: *mut usize) {
        unsafe {
            let previous = atomic_xchg(
                // &(self.ptr as usize) as *const usize as *mut usize,
                &self.ptr as *const _ as *mut _,
                ptr as usize,
            ) as *mut NodeContainer;
            if !previous.is_null() {
                // decrease previous' refer count
                if (*previous).del_ref() {
                    let _ = Box::from_raw(previous);
                }
            }
        }
    }

    /// No write-confilct free guarantee as above
    pub fn replace_with(&self, new_item: Self) {
        unsafe {
            // increase reference counter as `new_item` will be dropped when get out of this block
            (*new_item.ptr).add_ref();
            self.replace_underlying(new_item.ptr as *mut usize)
        }
    }

    pub fn add_leaf_mark(&self) {
        unsafe {
            let mut container = &mut *self.ptr;
            container.node = (container.node as usize + 1) as *mut usize;
        }
    }

    pub fn remove_leaf_mark(&self) {
        unsafe {
            let mut container = &mut *self.ptr;
            container.node = (container.node as usize - 1) as *mut usize;
        }
    }

    pub fn is_null(&self) -> bool {
        unsafe { (*self.ptr).node.is_null() }
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
        Self::new(ptr::null_mut())
    }
}

impl Deref for NodeRef {
    type Target = *mut usize;

    fn deref(&self) -> &Self::Target {
        unsafe { &(*self.ptr).node }
    }
}
