#![feature(core_intrinsics)]
#![feature(nonnull_slice_from_raw_parts)]
#![feature(alloc_layout_extra)]
#![feature(trait_alias)]
#![feature(allocator_api)]
#![allow(dead_code)]

mod node;
mod node_ptr;
mod node_ref;
mod serialized;
mod sync;

pub use node::*;
// for fuzz test. should not export.
pub use node_ref::NodeRef;
