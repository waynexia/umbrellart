//! [DynamicNode] is the node has the same length of keys and children slots.
//! [Node4] and [Node16] is implemented on it.

use std::mem;

use crate::node::{Header, NodePtr, NodeType};
use crate::node_48::Node48;

#[repr(C)]
#[derive(Debug)]
pub(crate) struct DynamicNode<const CAPACITY: usize, const TYPE: u8> {
    pub(crate) header: Header,
    /// N slots in the beginning are valid items (N is header's item count)
    pub(crate) children: [NodePtr; CAPACITY],
    pub(crate) keys: [u8; CAPACITY],
}

impl<const CAPACITY: usize, const TYPE: u8> DynamicNode<CAPACITY, TYPE> {
    // todo: make this as const generic param directly when that feature is not
    // "incomplete".
    const TYPE: NodeType = NodeType::from_u8::<TYPE>();

    /// Construct a [DynamicNode] with existing [Header]. This is used to
    /// accomplish node expand/shrink.
    pub(crate) fn from_header(header: Header) -> Self {
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

    /// Panic if the pointer is invalid.
    pub unsafe fn from_node_ptr(ptr: NodePtr) -> Self {
        let node_type = ptr.try_as_header().unwrap().node_type();
        assert_eq!(node_type, Self::TYPE);

        Box::into_inner(Box::from_raw(ptr.0 as *const Self as *mut Self))
    }

    pub fn find_key(&self, key: u8) -> Option<&NodePtr> {
        for (index, ptr) in self.children.iter().enumerate() {
            if !ptr.is_null() {
                if self.keys[index] == key {
                    return Some(&self.children[index]);
                }
            }
        }

        None
    }

    pub fn find_key_mut(&mut self, key: u8) -> Option<&mut NodePtr> {
        for (index, ptr) in self.children.iter().enumerate() {
            if !ptr.is_null() {
                if self.keys[index] == key {
                    return Some(&mut self.children[index]);
                }
            }
        }

        None
    }

    pub fn first_child(&self) -> Option<&NodePtr> {
        for ptr in &self.children {
            if !ptr.is_null() {
                return Some(ptr);
            }
        }

        None
    }

    /// # Notice
    ///
    /// Caller should ensure the capacity. For simplicity this needs at least
    /// one empty slot (don't consider the situation that a duplicate insertion
    /// won't occupy new slot).
    pub fn add_child(&mut self, key: u8, child: NodePtr) -> Option<NodePtr> {
        assert!(self.header.size() < CAPACITY);

        // go though all keys and children to find duplicate key and/or empty slot. If
        // duplicate key already exist this will get it's index and child. Otherwise it
        // will get the first empty slot.
        let (index, exist) = self.keys.iter().zip(self.children.iter()).enumerate().fold(
            (None, None),
            |(mut maybe_index, mut maybe_exist), (index, (k, child))| {
                // is an empty slot.
                if child.is_null() {
                    maybe_index.get_or_insert(index);
                    return (maybe_index, maybe_exist);
                }

                // is duplicate key
                if *k == key {
                    maybe_exist = Some(*child);
                    maybe_index = Some(index);
                }

                (maybe_index, maybe_exist)
            },
        );

        // handle duplicate key
        if exist.is_some() {
            // todo: what if it's not a Leaf node
            self.children[index.unwrap() as usize] = child;
            return exist;
        }

        // insert into slot
        let index = index.unwrap();
        self.keys[index] = key;
        self.children[index] = child;
        self.header.inc_count();
        None
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

    /// Decouple this struct. Because [DynamicNode] implements [Drop], its
    /// fields cannot be moved out directly.
    fn decouple(self) -> (Header, [NodePtr; CAPACITY], [u8; CAPACITY]) {
        #[repr(C)]
        struct NotDropDynamicNode<const CAP: usize> {
            header: Header,
            children: [NodePtr; CAP],
            keys: [u8; CAP],
        }

        // todo: compiler doesn't believe the two `CAPACITY` are the same so I can't
        // direct `transmute`.
        // issue: https://github.com/rust-lang/rust/issues/61956
        let dynamic_node: NotDropDynamicNode<CAPACITY> = unsafe { mem::transmute_copy(&self) };
        mem::forget(self);
        let NotDropDynamicNode {
            header,
            children,
            keys,
        } = dynamic_node;

        (header, children, keys)
    }
}

impl<const CAPACITY: usize, const TYPE: u8> Drop for DynamicNode<CAPACITY, TYPE> {
    fn drop(&mut self) {
        for child in self.children {
            if !child.is_null() {
                child.drop();
            }
        }
    }
}

pub(crate) type Node4 = DynamicNode<4, 0>;

impl Node4 {
    // todo: how to access `DynamicNode`'s CAPACITY?
    const CAPACITY: usize = 4;

    #[allow(dead_code)]
    const fn assert_node4_size() {
        // 16 for header
        // 32 for children
        // 4 (+4 for padding) for keys
        const _: () = assert!(std::mem::size_of::<Node4>() == 56);
    }

    pub fn should_grow(&self) -> bool {
        self.header.size() >= Self::CAPACITY
    }

    pub fn should_shrink(&self) -> bool {
        // Node4 cannot shrink
        false
    }

    pub fn grow(self) -> Node16 {
        let (mut header, children, keys) = self.decouple();

        // Change the type and construct a Node16.
        // Differ to `Node16`, this copies key and child slots directly
        // into new node thus no need to reset header's counter.
        header.change_type(NodeType::Node16);
        let mut node16 = Node16::from_header(header);

        // Node4 and Node16 have the same logic on children and keys array. So just copy
        // them.
        node16.children[0..children.len()].copy_from_slice(&children);
        node16.keys[0..children.len()].copy_from_slice(&keys);

        node16
    }

    pub fn shrink(self) -> ! {
        unreachable!("Node4 cannot shrink")
    }
}

pub(crate) type Node16 = DynamicNode<16, 1>;

impl Node16 {
    pub const CAPACITY: usize = 16;

    #[allow(dead_code)]
    const fn assert_node16_size() {
        // 16 for header
        // 128 for children
        // 16 for keys
        const _: () = assert!(std::mem::size_of::<Node16>() == 160);
    }

    pub fn should_grow(&self) -> bool {
        self.header.size() >= Self::CAPACITY
    }

    pub fn should_shrink(&self) -> bool {
        // don't shrink immediately
        self.header.size() <= Node4::CAPACITY / 2
    }

    pub fn grow(self) -> Node48 {
        let (mut header, children, keys) = self.decouple();

        // change header and construct a Node48
        header.change_type(NodeType::Node48);
        header.reset_count();
        let mut node48 = Node48::from_header(header);

        for (key, child) in keys.into_iter().zip(children.into_iter()) {
            if !child.is_null() {
                node48.add_child(key, child);
            }
        }

        node48
    }

    pub fn shrink(self) -> Node4 {
        assert!(self.header.size() < Node4::CAPACITY);

        let (mut header, children, keys) = self.decouple();

        // change header and construct a Node48
        header.change_type(NodeType::Node4);
        header.reset_count();
        let mut node4 = Node4::from_header(header);

        for (key, child) in keys.into_iter().zip(children.into_iter()) {
            if !child.is_null() {
                node4.add_child(key, child);
            }
        }

        node4
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::leaf::NodeLeaf;

    fn do_insert_find_remove<const CAP: usize, const TYPE: u8>(_node: DynamicNode<CAP, TYPE>) {
        let mut node = DynamicNode::<CAP, TYPE>::new();

        node.add_child(9, NodePtr::from_usize(1));
        assert_eq!(*node.find_key(9).unwrap(), NodePtr::from_usize(1));
        assert!(node.find_key(10).is_none());
        assert!(node.remove_child(9).is_some());
        assert!(node.remove_child(9).is_none());
        assert!(node.find_key(9).is_none());
    }

    fn do_overflow<const CAP: usize, const TYPE: u8>(_node: DynamicNode<CAP, TYPE>) {
        let mut node = DynamicNode::<CAP, TYPE>::new();

        for i in 0..CAP {
            node.add_child(i as u8, NodePtr::from_usize(1));
        }

        node.add_child(10, NodePtr::from_usize(1));
    }

    fn do_erases<const CAP: usize, const TYPE: u8>(_node: DynamicNode<CAP, TYPE>) {
        let mut node = DynamicNode::<CAP, TYPE>::new();

        for i in 0..u8::MAX {
            node.add_child(i, NodePtr::from_usize(1));
            assert!(node.remove_child(i).is_some());
        }
    }

    fn do_insert_duplicate<const CAP: usize, const TYPE: u8>(_node: DynamicNode<CAP, TYPE>) {
        let mut node = DynamicNode::<CAP, TYPE>::new();

        assert!(node.add_child(1, NodePtr::from_usize(11)).is_none());
        assert_eq!(
            node.add_child(1, NodePtr::from_usize(101)).unwrap(),
            NodePtr::from_usize(11)
        );

        assert!(node.add_child(2, NodePtr::from_usize(21)).is_none());
        assert!(node.add_child(3, NodePtr::from_usize(31)).is_none());
        assert_eq!(node.remove_child(2).unwrap(), NodePtr::from_usize(21));
        assert_eq!(
            node.add_child(3, NodePtr::from_usize(301)).unwrap(),
            NodePtr::from_usize(31)
        );
        assert!(node.add_child(2, NodePtr::from_usize(201)).is_none());
        assert_eq!(
            node.add_child(2, NodePtr::from_usize(2001)).unwrap(),
            NodePtr::from_usize(201)
        );
        assert_eq!(*node.find_key(2).unwrap(), NodePtr::from_usize(2001));
    }

    #[test]
    fn node4_insert_find_remove() {
        do_insert_find_remove(Node4::new());
    }

    #[test]
    #[should_panic]
    fn node4_overflow() {
        do_overflow(Node4::new());
    }

    #[test]
    fn node4_erases() {
        do_erases(Node4::new());
    }

    #[test]
    fn node4_insert_duplicate() {
        do_insert_duplicate(Node4::new());
    }

    #[test]
    fn node16_insert_find_remove() {
        do_insert_find_remove(Node16::new());
    }

    #[test]
    #[should_panic]
    fn node16_overflow() {
        do_overflow(Node16::new());
    }

    #[test]
    fn node16_erases() {
        do_erases(Node16::new());
    }

    #[test]
    fn node16_insert_duplicate() {
        do_insert_duplicate(Node16::new());
    }

    #[test]
    fn node4_insert_to_full() {
        let mut node = Node4::new();

        for i in 0..Node4::CAPACITY {
            node.add_child(i as u8, NodePtr::from_usize(i * 10 + 1));
        }

        assert!(node.should_grow());
    }

    #[test]
    fn node16_insert_to_full() {
        let mut node = Node16::new();

        for i in 0..Node16::CAPACITY {
            node.add_child(i as u8, NodePtr::from_usize(i * 10 + 1));
        }

        assert!(node.should_grow());
    }

    #[test]
    fn node4_grow_to_node16() {
        let mut node4 = Node4::new();
        for i in 0..Node4::CAPACITY - 1 {
            node4.add_child(i as u8, NodePtr::from_usize(i * 10 + 101));
        }

        let node16 = node4.grow();

        assert_eq!(node16.header.size(), Node4::CAPACITY - 1);
        assert_eq!(node16.header.node_type(), NodeType::Node16);

        assert_eq!(*node16.find_key(0).unwrap(), NodePtr::from_usize(101));
        assert_eq!(*node16.find_key(1).unwrap(), NodePtr::from_usize(111));
        assert_eq!(*node16.find_key(2).unwrap(), NodePtr::from_usize(121));
        for i in Node4::CAPACITY..=u8::MAX as usize {
            assert!(node16.find_key(i as u8).is_none());
        }
    }

    #[test]
    fn node16_grow_to_node48() {
        let mut node16 = Node16::new();
        for i in 0..Node16::CAPACITY - 1 {
            node16.add_child(i as u8, NodePtr::from_usize(i * 10 + 101));
        }

        let node48 = node16.grow();

        assert_eq!(node48.header.size(), Node16::CAPACITY - 1);
        assert_eq!(node48.header.node_type(), NodeType::Node48);

        for i in 0..Node16::CAPACITY - 1 {
            assert_eq!(
                *node48.find_key(i as u8).unwrap(),
                NodePtr::from_usize(i * 10 + 101)
            );
        }
        for i in Node16::CAPACITY..=u8::MAX as usize {
            assert!(node48.find_key(i as u8).is_none());
        }
    }

    #[test]
    fn node16_shrink_to_node4() {
        let mut node16 = Node16::new();
        for i in 0..Node16::CAPACITY - 1 {
            node16.add_child(i as u8, NodePtr::from_usize(i * 10 + 101));
        }
        let mut i = 0;
        while !node16.should_shrink() {
            node16.remove_child(i).unwrap();
            i += 1;
        }

        let node4 = node16.shrink();

        assert_eq!(node4.header.size(), 2);
        assert_eq!(node4.header.node_type(), NodeType::Node4);

        for i in 0..=u8::MAX as usize {
            if i == 13 || i == 14 {
                // the last two elements
                assert_eq!(
                    *node4.find_key(i as u8).unwrap(),
                    NodePtr::from_usize(i * 10 + 101)
                );
            } else {
                assert!(node4.find_key(i as u8).is_none());
            }
        }
    }

    #[test]
    fn drop_node4() {
        let mut node4 = Node4::new();
        for i in 0..4 {
            let leaf_ptr = NodePtr::boxed(NodeLeaf::new(
                vec![i],
                NodePtr::from_usize(i as usize * 8 + 1024),
            ));
            node4.add_child(i, leaf_ptr);
        }
        drop(node4);
    }

    #[test]
    fn drop_node16() {
        let mut node16 = Node16::new();
        for i in 0..4 {
            let leaf_ptr = NodePtr::boxed(NodeLeaf::new(
                vec![i],
                NodePtr::from_usize(i as usize * 8 + 1024),
            ));
            node16.add_child(i, leaf_ptr);
        }
        drop(node16);
    }
}
