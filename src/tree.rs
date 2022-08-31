use std::marker::PhantomData;

use crate::leaf::NodeLeaf;
use crate::node::{Node, NodePtr};

pub struct Art<V> {
    root: NodePtr,
    _phantom_v: PhantomData<V>,
}

impl<V> Art<V> {
    pub fn get(&self, key: &[u8]) -> Option<&V> {
        Node::search(self.root, key)
    }

    pub fn insert(&mut self, key: &[u8], value: V) -> Option<V> {
        let leaf = NodeLeaf::new(key.to_vec(), NodePtr::boxed(value));
        let result = Node::<V>::insert(&mut self.root, key, NodePtr::boxed(leaf));

        todo!()
    }
}
