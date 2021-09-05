#![feature(core_intrinsics)]
#![allow(dead_code)]

mod node;
mod node_ref;

pub use node::*;
// for fuzz test. should not export.
pub use node_ref::NodeRef;
