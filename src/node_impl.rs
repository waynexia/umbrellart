use std::mem;

use crate::node::{Header, NodePtr, NodeType};

#[repr(C)]
#[derive(Debug)]
pub(crate) struct DynamicNode<const CAPACITY: usize, const TYPE: u8> {
    header: Header,
    children: [NodePtr; CAPACITY],
    keys: [u8; CAPACITY],
}

impl<const CAPACITY: usize, const TYPE: u8> DynamicNode<CAPACITY, TYPE> {
    // todo: make this as const generic param directly when that feature is not
    // "incomplete".
    const TYPE: NodeType = NodeType::from_u8::<TYPE>();

    /// Construct a [DynamicNode] with existing [Header]. This is used to
    /// accomplish node expand/shrink.
    fn from_header(header: Header) -> Self {
        debug_assert!(header.node_type() == Self::TYPE);
        Self {
            header,
            keys: [0; CAPACITY],
            children: [NodePtr::default(); CAPACITY],
        }
    }

    pub fn new() -> Self {
        let header = Header::new(Self::TYPE);
        Self {
            header,
            keys: [0; CAPACITY],
            children: [NodePtr::default(); CAPACITY],
        }
    }

    pub fn find_key(&self, key: u8) -> Option<NodePtr> {
        for (index, ptr) in self.children.iter().enumerate() {
            if !ptr.is_null() {
                if self.keys[index] == key {
                    return Some(self.children[index]);
                }
            }
        }

        None
    }

    /// # Notice
    ///
    /// Caller should ensure the capacity.
    pub fn add_child(&mut self, key: u8, child: NodePtr) {
        assert!(self.header.size() < CAPACITY);
        self.header.inc_count();

        // find a empty slot
        let (index, _) = self
            .children
            .iter()
            .enumerate()
            .find(|(_, ptr)| ptr.is_null())
            .unwrap();

        self.keys[index] = key;
        self.children[index] = child;
    }

    pub fn remove_child(&mut self, key: u8) -> Option<NodePtr> {
        // try to find this key
        let (index, _) = self
            .children
            .iter()
            .zip(self.keys.iter())
            .enumerate()
            .find(|(_, (ptr, k))| !ptr.is_null() && **k == key)?;

        // remove this key and return the pointer
        self.header.dec_count();
        let taken = mem::take(&mut self.children[index]);
        Some(taken)
    }
}

pub(crate) type Node4 = DynamicNode<4, 0>;

impl Node4 {
    #[allow(dead_code)]
    const fn assert_node4_size() {
        // 16 for header
        // 32 for children
        // 4 (+4 for padding) for keys
        const _: () = assert!(std::mem::size_of::<Node4>() == 56);
    }

    pub fn grow(self) -> Node16 {
        let Self {
            mut header,
            children,
            keys,
        } = self;

        // change the type and construct a Node16
        header.change_type(NodeType::Node16);
        let mut node16 = Node16::from_header(header);

        // Node4 and Node16 have the same logic on children and keys array. So just copy
        // them.
        node16.children.copy_from_slice(&children);
        node16.keys.copy_from_slice(&keys);

        node16
    }
}

pub(crate) type Node16 = DynamicNode<16, 1>;

impl Node16 {
    #[allow(dead_code)]
    const fn assert_node16_size() {
        // 16 for header
        // 128 for children
        // 16 for keys
        const _: () = assert!(std::mem::size_of::<Node16>() == 160);
    }

    pub fn grow(self) -> Node48 {
        todo!()
    }

    pub fn shrink(self) -> Node4 {
        todo!()
    }
}

#[repr(C)]
#[derive(Debug)]
pub struct Node48 {
    header: Header,
    children: [NodePtr; Self::CAPACITY],
    keys: [u8; u8::MAX as usize],
}

impl Node48 {
    const CAPACITY: usize = 48;

    #[allow(dead_code)]
    const fn assert_node4_size() {
        // 16 for header
        // 384 (8 * 48) for children
        // 256 for keys
        const _: () = assert!(std::mem::size_of::<Node48>() == 656);
    }

    /// Construct a [Node48] with existing [Header]. This is used to
    /// accomplish node expand/shrink.
    fn from_header(header: Header) -> Self {
        debug_assert!(header.node_type() == NodeType::Node48);
        Self {
            header,
            keys: [0; u8::MAX as usize],
            children: [NodePtr::default(); Self::CAPACITY],
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn dynamic_node_insert_find_remove<const CAP: usize, const TYPE: u8>(
        _node: DynamicNode<CAP, TYPE>,
    ) {
        let mut node = DynamicNode::<CAP, TYPE>::new();

        node.add_child(9, NodePtr::from_usize(2));
        assert!(node.find_key(9).is_some());
        assert!(node.find_key(10).is_none());
        assert!(node.remove_child(9).is_some());
        assert!(node.remove_child(9).is_none());
        assert!(node.find_key(9).is_none());
    }

    fn dynamic_node_overflow<const CAP: usize, const TYPE: u8>(_node: DynamicNode<CAP, TYPE>) {
        let mut node = DynamicNode::<CAP, TYPE>::new();

        for i in 0..CAP {
            node.add_child(i as u8, NodePtr::from_usize(2));
        }

        node.add_child(10, NodePtr::from_usize(2));
    }

    fn dynamic_node_erases<const CAP: usize, const TYPE: u8>(_node: DynamicNode<CAP, TYPE>) {
        let mut node = DynamicNode::<CAP, TYPE>::new();

        for i in 0..u8::MAX {
            node.add_child(i, NodePtr::from_usize(2));
            assert!(node.remove_child(i).is_some());
        }
    }

    #[test]
    fn node4_insert_find_remove() {
        dynamic_node_insert_find_remove(Node4::new());
    }

    #[test]
    #[should_panic]
    fn node4_overflow() {
        dynamic_node_overflow(Node4::new());
    }

    #[test]
    fn node4_erases() {
        dynamic_node_erases(Node4::new());
    }

    #[test]
    fn node16_insert_find_remove() {
        dynamic_node_insert_find_remove(Node16::new());
    }

    #[test]
    #[should_panic]
    fn node16_overflow() {
        dynamic_node_overflow(Node16::new());
    }

    #[test]
    fn node16_erases() {
        dynamic_node_erases(Node16::new());
    }
}
