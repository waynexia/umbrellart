use std::{marker::PhantomData, mem};

#[repr(u8)]
enum NodeType {
    DynamicNode,
    PartialNode,
}

struct ItemPointer(*const ());

impl ItemPointer {
    fn as_node_header_unchecked(&self) -> &NodeHeader {
        unsafe { &*mem::transmute::<*const (), *const NodeHeader>(self.0) }
    }

    fn new_value_ptr<V>(ptr: &mut V) -> Self {
        let biased_ptr = ptr as *const V as usize + 1;
        Self(biased_ptr as *const ())
    }

    fn is_value_ptr(&self) -> bool {
        self.0 as usize % 2 != 0
    }
}

struct NodeHeader {
    prefix_length: u32,
    prefix_ptr: ItemPointer,
    leaf_ptr: ItemPointer,
    node_type: NodeType,
    node_cap: u8,
}

impl NodeHeader {
    fn insert(&self, key: &[u8], value: ItemPointer) {
        let node: &DynamicNode<4> = self.cast_to_dynamic_node();
    }

    fn cast_to_dynamic_node<const CAP: usize>(&self) -> &DynamicNode<CAP> {
        todo!()
    }
}

struct DynamicNode<const CAP: usize> {
    header: NodeHeader,
    key_slot: [ItemPointer; CAP],
    value_slot: [ItemPointer; CAP],
}

type Node4 = DynamicNode<4>;

type Node16 = DynamicNode<16>;

struct PartialNode<const CAP: usize> {
    header: NodeHeader,
    key_slot: [ItemPointer; CAP],
    value_slot: [ItemPointer; 256],
}

type Node48 = PartialNode<48>;

// type FullNode = PartialNode<256>;

struct FullNode {
    header: NodeHeader,
    key_slot: [ItemPointer; 256],
    value_slot: [ItemPointer; 256],
}

pub struct Tree<V> {
    root: ItemPointer,
    _phantom_value: PhantomData<V>,
}

impl<V> Tree<V> {
    pub fn insert<K: AsRef<[u8]>>(&mut self, key: K, value: V) {
        let leaked_value = Box::leak(Box::new(value));
        let value_ptr = ItemPointer::new_value_ptr(leaked_value);

        self.root
            .as_node_header_unchecked()
            .insert(key.as_ref(), value_ptr);
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn header_size() {
        println!("{:?}", std::mem::size_of::<NodeHeader>())
    }
}
