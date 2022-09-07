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
            .and_then(|leaf| leaf.cast_to::<NodeLeaf>()?.value.cast_to::<V>())
    }

    pub fn insert(&mut self, key: &[u8], value: V) -> Option<V> {
        let leaf = NodeLeaf::new(key.to_vec(), NodePtr::boxed(value));
        Node::<V>::insert(&mut self.root, key, NodePtr::boxed(leaf))
            .and_then(|ptr| ptr.into_option())
            .map(NodePtr::unbox::<V>)
    }

    pub fn remove(&mut self, key: &[u8]) -> Option<V> {
        let leaf = Node::<V>::remove(&mut self.root, key)?;
        let item = leaf.cast_to::<NodeLeaf>()?.value.unbox::<V>();
        leaf.drop();

        Some(item)
    }
}

impl<V> Default for Art<V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<V> Drop for Art<V> {
    fn drop(&mut self) {
        self.root.drop();
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    #[cfg(not(miri))]
    fn fuzz_case_5() {
        let mut art = Art::new();
        art.insert(
            &[
                79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 0,
            ],
            1,
        );
        art.insert(&[79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 0], 2);

        let result = art
            .remove(&[79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 0])
            .unwrap();
        assert_eq!(result, 2);
    }

    #[test]
    #[cfg(not(miri))]
    fn fuzz_case_6() {
        let mut art = Art::new();
        art.insert(
            &[
                79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79,
                0,
            ],
            1,
        );
        art.insert(&[79, 79, 79, 0], 2);
        art.insert(
            &[
                79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 0,
            ],
            3,
        );

        let result = art.remove(&[79, 79, 79, 0]).unwrap();
        assert_eq!(result, 2);

        let result = art
            .remove(&[
                79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 0,
            ])
            .unwrap();
        assert_eq!(result, 3);

        let result = art
            .remove(&[
                79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79,
                0,
            ])
            .unwrap();
        assert_eq!(result, 1);
    }
}
