use std::marker::PhantomData;

use crate::node::{Node, NodePtr};

pub struct Art<V> {
    root: NodePtr,
    _phantom_v: PhantomData<V>,
}

impl<V> Art<V> {
    pub fn get(&self, key: &[u8]) -> Option<&V> {
        Node::search(self.root, key)
    }
}
