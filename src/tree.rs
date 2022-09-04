use std::marker::PhantomData;

use crate::leaf::NodeLeaf;
use crate::node::{Node, NodePtr};

pub struct Art<V> {
    root: NodePtr,
    _phantom: PhantomData<V>,
}

impl<V> Art<V> {
    pub fn new() -> Self {
        Self {
            root: NodePtr::default(),
            _phantom: PhantomData,
        }
    }

    pub fn get(&self, key: &[u8]) -> Option<&V> {
        Node::<V>::search(&self.root, key)
            .map(|leaf| leaf.cast_to::<NodeLeaf>()?.value.cast_to::<V>())
            .flatten()
    }

    pub fn insert(&mut self, key: &[u8], value: V) -> Option<V> {
        let leaf = NodeLeaf::new(key.to_vec(), NodePtr::boxed(value));
        Node::<V>::insert(&mut self.root, key, NodePtr::boxed(leaf))
            .map(|ptr| ptr.into_option())
            .flatten()
            .map(NodePtr::unbox::<V>)
    }

    pub fn remove(&mut self, key: &[u8]) -> Option<V> {
        let leaf = Node::<V>::remove(&mut self.root, key)?;
        let item = leaf.cast_to::<NodeLeaf>()?.value.unbox::<V>();
        leaf.drop();

        Some(item)
    }
}
