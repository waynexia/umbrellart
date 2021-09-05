use std::alloc::{alloc, dealloc, Layout};
use std::ptr;

const MEMORY_ALIGN: usize = 64;

#[repr(C)]
#[derive(Clone, Debug)]
pub struct PrefixArray {
    ptr: *const u8,
    length: u32,
}

impl Default for PrefixArray {
    fn default() -> Self {
        Self {
            ptr: ptr::null(),
            length: 0,
        }
    }
}

impl PrefixArray {
    #[allow(dead_code)]
    pub fn copy_from(other: &Self) -> Self {
        let mut ret = Self::default();
        ret.set_values(other.values());
        ret
    }

    /// set prefix len and values
    pub fn set_values(&mut self, new_prefix: &[u8]) {
        unsafe {
            self.reallocate(new_prefix.len());
            ptr::copy(new_prefix.as_ptr(), self.ptr as *mut u8, new_prefix.len());
        }
        self.length = new_prefix.len() as u32;
    }

    pub fn len(&self) -> u32 {
        self.length
    }

    pub fn value(&self, index: usize) -> u8 {
        debug_assert!(index < self.length as usize);
        unsafe { *(self.ptr.add(index)) }
    }

    pub fn values(&self) -> &[u8] {
        unsafe { std::slice::from_raw_parts(self.ptr as *const u8, self.length as usize) }
    }

    /// old value will be discarded
    unsafe fn reallocate(&mut self, size: usize) {
        dealloc(
            self.ptr as *mut u8,
            Layout::from_size_align(self.length as usize * 8, MEMORY_ALIGN).unwrap(),
        );
        self.ptr = alloc(Layout::from_size_align(size * 8, MEMORY_ALIGN).unwrap());
    }
}
