use crate::node::*;
use std::intrinsics::{atomic_store, atomic_xchg};
use std::mem;
use std::ptr;
use std::sync::atomic::Ordering::Relaxed;
use std::sync::atomic::{AtomicPtr, AtomicUsize};

#[derive(Debug)]
pub struct NodePtr {
    inner: AtomicPtr<NodePtrInner>,
}

impl NodePtr {
    pub fn new(ptr: *mut usize) -> Self {
        let inner = Box::into_raw(Box::new(NodePtrInner::new(ptr)));
        Self {
            inner: AtomicPtr::new(inner),
        }
    }

    pub fn clone(&self) -> Self {
        unsafe {
            (*self.inner.load(Relaxed)).increase_counter();
        }
        Self::from_inner(self.inner.load(Relaxed))
    }

    pub fn swap(&self, incoming: Self) {
        unsafe {
            let old_ptr = self.load();
            let incoming_ptr = incoming.load();
            self.store(incoming_ptr);
            incoming.store(old_ptr);
            let old_count = (*self.inner.load(Relaxed)).count.load(Relaxed);
            // let incoming_count = (*incoming.inner.load(Relaxed)).count.load(Relaxed);
            (*self.inner.load(Relaxed)).set_count(&(*incoming.inner.load(Relaxed)).count);
            (*incoming.inner.load(Relaxed)).set_count(&AtomicUsize::new(old_count));
            // (*self.inner.load(Relaxed)).store(incoming_ptr);
            // (*incoming.inner.load(Relaxed)).store(old_ptr);

            // let old_inner = self.inner.swap(incoming.inner.load(Relaxed), Relaxed);
            // // for incoming's drop
            // (*self.inner.load(Relaxed)).increase_counter();
            // // for self's drop
            // (*self.inner.load(Relaxed)).increase_counter();
            // // decrease leaf's rc
            // let _ = Self::from_inner(old_inner);
            // // drop `self`
            // let _ = Self::from_inner(old_inner);
        }
    }

    pub fn replace(&self, src: Self) {
        unsafe {
            // copy inner
            // let old_ptr = (*self.inner.load(Relaxed)).ptr.swap(src.load(), Relaxed);
            (*self.inner.load(Relaxed)).set_count(&(*src.inner.load(Relaxed)).count);
            (*self.inner.load(Relaxed)).store(src.load());
            // (*self.inner.load(Relaxed)).decrsease_counter();
            // let _ = Box::from_raw(old_ptr);

            // (*src.inner).increase_counter();
            // atomic_store(
            //     &(self.inner as usize) as *const usize as *mut usize,
            //     src.inner as usize,
            // );

            // (*src.inner.load(Relaxed)).increase_counter();
            // let old_inner = self.inner.swap(src.inner.load(Relaxed), Relaxed);
            // // let _ = Box::from_raw(old_inner);
            // let _ = Self::from_inner(old_inner);
        }
    }

    // todo: remove this
    pub fn store(&self, ptr: *mut usize) {
        unsafe { (*self.inner.load(Relaxed)).store(ptr) }
    }

    // todo: remove this
    pub fn load(&self) -> *mut usize {
        unsafe { (*self.inner.load(Relaxed)).load() }
    }

    // todo: remove this
    pub fn atomic_swap(&self, ptr: *mut usize) -> *mut usize {
        unsafe { (*self.inner.load(Relaxed)).atomic_swap(ptr) }
    }

    pub fn get_type(&self) -> NodeType {
        let ptr = unsafe { (*self.inner.load(Relaxed)).load() };
        if (ptr as usize) & 1 == 1 {
            NodeType::KVPair
        } else {
            unsafe { (*(ptr as *mut Node4)).header.node_type }
        }
    }

    fn from_inner(inner: *mut NodePtrInner) -> Self {
        Self {
            inner: AtomicPtr::new(inner),
        }
    }
}

impl Drop for NodePtr {
    fn drop(&mut self) {
        let cnt = unsafe { (*self.inner.load(Relaxed)).drop() };
        if cnt == 0 {
            let _ = unsafe { Box::from_raw(self.inner.load(Relaxed)) };
        }
    }
}

impl Default for NodePtr {
    // todo: lazy initialze
    fn default() -> Self {
        let inner = Box::into_raw(Box::new(NodePtrInner::default()));
        Self {
            // inner: ptr::null_mut(),
            inner: AtomicPtr::new(inner),
        }
    }
}

#[derive(Debug)]
pub struct NodePtrInner {
    ptr: AtomicPtr<usize>,
    count: AtomicUsize,
}

impl NodePtrInner {
    fn new(ptr: *mut usize) -> Self {
        Self {
            ptr: AtomicPtr::new(ptr),
            count: AtomicUsize::new(1),
        }
    }

    pub fn obsolate(&self) {
        let cnt = self.count.fetch_sub(1, Relaxed);
        assert!(cnt > 0);
    }

    fn store(&self, ptr: *mut usize) {
        self.ptr.store(ptr, Relaxed);
    }

    fn load(&self) -> *mut usize {
        self.ptr.load(Relaxed)
    }

    pub fn atomic_swap(&self, ptr: *mut usize) -> *mut usize {
        self.ptr.swap(ptr, Relaxed)
    }

    pub fn get_type(&self) -> NodeType {
        let ptr = self.ptr.load(Relaxed);
        if (ptr as usize) & 1 == 1 {
            NodeType::KVPair
        } else {
            unsafe { (*(ptr as *mut Node4)).header.node_type }
        }
    }

    pub fn refer(&self) -> NodeRef {
        NodeRef { ptr_ref: &self }
    }

    /// Manually increase strong counter by one.
    /// Usually when creating a new inner node to replace an old one, atomic store
    /// is called instead of "move". which will lead to a `drop` call and decrease
    /// counter. In that situation needs to invoke this method to balance that `drop` call.
    pub fn increase_counter(&self) {
        self.count.fetch_add(1, Relaxed);
    }

    /// Same as `obsolate` but without that semantic.
    pub fn decrease_counter(&self) {
        self.count.fetch_sub(1, Relaxed);
    }

    /// Replace `self`'s content with `src`'s.
    /// old value will be overwrote. `src`'s counter is maintained by `self`.
    pub fn replace(&self, src: &Self) {
        // assert!(self.load().is_null());

        self.store(src.load());
        self.count.store(src.count.load(Relaxed), Relaxed);
        // todo: check whether this forget work
        mem::forget(src);
    }

    /// Swap self's content into `outdated`'s place (swap pointer).
    /// outdated node is obsolated and cannot be entered (other threads already accessing
    /// to it is fine). And its memory will be reclaimed once no one refering to it.
    pub fn swap(&self, incoming: &Self) {
        // let old_ptr = self.load();
        // outdated.store(old_ptr);
        // outdated.obsolate();

        let old_ptr = self.load();
        self.store(incoming.load());
        // todo: how to deal with self.count and incoming.count
        // todo: check whether this forget work
        // mem::forget(incoming);
        incoming.increase_counter();
    }

    fn set_count(&self, count: &AtomicUsize) {
        self.count.store(count.load(Relaxed), Relaxed);
    }

    fn drop(&mut self) -> usize {
        let cnt = self.count.fetch_sub(1, Relaxed);
        if cnt == 1 {
            let ptr = self.load();
            if ptr.is_null() {
                return 0;
            }
            println!("going to drop a NodePtr");

            match self.get_type() {
                NodeType::Node4 => unsafe {
                    let _ = Box::from_raw(ptr as *mut Node4);
                },
                NodeType::Node16 => unsafe {
                    let _ = Box::from_raw(ptr as *mut Node16);
                },
                NodeType::Node48 => unsafe {
                    let _ = Box::from_raw(ptr as *mut Node48);
                },
                NodeType::Node256 => unsafe {
                    let _ = Box::from_raw(ptr as *mut Node256);
                },
                NodeType::KVPair => return 0,
            }
        }
        cnt - 1
    }
}

// impl Drop for NodePtrInner {
// }

impl Default for NodePtrInner {
    fn default() -> Self {
        Self {
            ptr: AtomicPtr::new(ptr::null_mut::<usize>()),
            count: AtomicUsize::new(1),
        }
    }
}

pub struct NodeRef<'a> {
    ptr_ref: &'a NodePtrInner,
}

impl<'a> Drop for NodeRef<'a> {
    fn drop(&mut self) {
        self.ptr_ref.count.fetch_sub(1, Relaxed);
    }
}
