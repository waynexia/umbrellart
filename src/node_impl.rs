use std::mem;

use crate::node::{Header, NodePtr, NodeType};

#[repr(C)]
#[derive(Debug)]
pub(crate) struct Node4 {
    header: Header,
    children: [NodePtr; Self::CAPACITY],
    keys: [u8; Self::CAPACITY],
}

impl Node4 {
    const CAPACITY: usize = 4;

    #[allow(dead_code)]
    const fn assert_node4_size() {
        // 16 for header
        // 32 for children
        // 4 (+4 for padding) for keys
        const _: () = assert!(std::mem::size_of::<Node4>() == 56);
    }

    pub fn new() -> Self {
        let header = Header::new(NodeType::Node4);
        Self {
            header,
            keys: [0; Self::CAPACITY],
            children: [NodePtr::default(); Self::CAPACITY],
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
        assert!(self.header.size() < Self::CAPACITY);
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

pub(crate) struct Node16 {
    header: Header,
    children: [NodePtr; Self::CAPACITY],
    keys: [u8; Self::CAPACITY],
}

impl Node16 {
    const CAPACITY: usize = 16;

    #[allow(dead_code)]
    const fn assert_node4_size() {
        // 16 for header
        // 128 for children
        // 16 for keys
        const _: () = assert!(std::mem::size_of::<Node16>() == 160);
    }

    /// Construct a [Node16] with existing [Header]. This is used to accomplish
    /// node expand/shrink.
    fn from_header(header: Header) -> Self {
        Self {
            header,
            keys: [0; Self::CAPACITY],
            children: [NodePtr::default(); Self::CAPACITY],
        }
    }

    pub fn new() -> Self {
        Self {
            header: Header::new(NodeType::Node16),
            keys: [0; Self::CAPACITY],
            children: [NodePtr::default(); Self::CAPACITY],
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn node4_insert_find_remove() {
        let mut node4 = Node4::new();

        node4.add_child(9, NodePtr::from_usize(2));
        assert!(node4.find_key(9).is_some());
        assert!(node4.find_key(10).is_none());
        assert!(node4.remove_child(9).is_some());
        assert!(node4.remove_child(9).is_none());
        assert!(node4.find_key(9).is_none());
    }

    #[test]
    #[should_panic]
    fn node4_overflow() {
        let mut node4 = Node4::new();

        for i in 0..Node4::CAPACITY {
            node4.add_child(i as u8, NodePtr::from_usize(2));
        }

        node4.add_child(10, NodePtr::from_usize(2));
    }

    #[test]
    fn node4_erases() {
        let mut node4 = Node4::new();

        for i in 0..u8::MAX {
            node4.add_child(i, NodePtr::from_usize(2));
            assert!(node4.remove_child(i).is_some());
        }
    }
}
