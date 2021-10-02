#[cfg(loom)]
crate use loom::sync::atomic::AtomicPtr;
#[cfg(not(loom))]
crate use std::sync::atomic::AtomicPtr;

#[cfg(loom)]
crate use loom::sync::atomic::AtomicUsize;
#[cfg(not(loom))]
crate use std::sync::atomic::AtomicUsize;

#[cfg(loom)]
crate use loom::sync::Mutex;
#[cfg(not(loom))]
crate use std::sync::Mutex;

#[cfg(loom)]
crate use loom::sync::MutexGuard;
#[cfg(not(loom))]
crate use std::sync::MutexGuard;

#[cfg(loom)]
crate use loom::sync::atomic::Ordering;
#[cfg(not(loom))]
crate use std::sync::atomic::Ordering;

#[cfg(loom)]
crate use loom::sync::Arc;
#[cfg(not(loom))]
crate use std::sync::Arc;

#[cfg(loom)]
use loom::alloc::Layout;
#[cfg(loom)]
use std::alloc::AllocError;
#[cfg(loom)]
use std::ptr::NonNull;
#[cfg(loom)]
crate struct Alloc;
#[cfg(loom)]
impl Alloc {
    fn alloc_impl(&self, layout: Layout, zeroed: bool) -> Result<NonNull<[u8]>, AllocError> {
        match layout.size() {
            0 => Ok(NonNull::slice_from_raw_parts(layout.dangling(), 0)),
            // SAFETY: `layout` is non-zero in size,
            size => unsafe {
                let raw_ptr = if zeroed {
                    loom::alloc::alloc_zeroed(layout)
                } else {
                    loom::alloc::alloc(layout)
                };
                let ptr = NonNull::new(raw_ptr).ok_or(AllocError)?;
                Ok(NonNull::slice_from_raw_parts(ptr, size))
            },
        }
    }
}
#[cfg(loom)]
unsafe impl std::alloc::Allocator for Alloc {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        self.alloc_impl(layout, false)
    }

    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        if layout.size() != 0 {
            // SAFETY: `layout` is non-zero in size,
            // other conditions must be upheld by the caller

            loom::alloc::dealloc(ptr.as_ptr(), layout)
        }
    }

    fn allocate_zeroed(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        self.alloc_impl(layout, true)
    }
}
#[cfg(not(loom))]
crate use std::alloc::System as Alloc;
