#![feature(box_into_inner)]
#![feature(pointer_is_aligned)]
#![feature(strict_provenance)]

mod dynamic_node;
mod leaf;
mod node;
mod node_256;
mod node_48;
mod tree;
mod utils;

pub use tree::Art;
