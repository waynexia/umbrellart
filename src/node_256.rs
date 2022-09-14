use std::mem;

use crate::node::{Header, NodePtr, NodeType};
use crate::node_48::Node48;

#[repr(C)]
#[derive(Debug)]
pub(crate) struct Node256 {
    pub(crate) header: Header,
    /// All valid [NodePtr]s are occupied slots.
    pub(crate) children: [NodePtr; Self::CAPACITY],
}

impl Node256 {
    /// How many item it can hold.
    const CAPACITY: usize = u8::MAX as usize + 1;

    pub const TYPE: NodeType = NodeType::Node256;

    #[allow(dead_code)]
    const fn assert_node4_size() {
        // 16 for header
        // 2048 (8 * 256) for children
        const _: () = assert!(std::mem::size_of::<Node256>() == 2064);
    }

    /// Construct a [Node256] with existing [Header]. This is used to
    /// accomplish node expand/shrink.
    pub(crate) fn from_header(header: Header) -> Self {
        debug_assert!(header.node_type() == NodeType::Node256);
        Self {
            header,
            children: [NodePtr::default(); Self::CAPACITY],
        }
    }

    #[cfg(test)]
    pub fn new() -> Self {
        let header = Header::new(NodeType::Node48);
        Self {
            header,
            children: [NodePtr::default(); Self::CAPACITY],
        }
    }

    /// Panic if the pointer is invalid.
    pub unsafe fn from_node_ptr(ptr: NodePtr) -> Self {
        let node_type = ptr.try_as_header().unwrap().node_type();
        assert_eq!(node_type, Self::TYPE);

        Box::into_inner(Box::from_raw(ptr.0 as *const Self as *mut Self))
    }

    pub fn find_key(&self, key: u8) -> Option<&NodePtr> {
        if self.children[key as usize].is_null() {
            None
        } else {
            Some(&self.children[key as usize])
        }
    }

    pub fn find_key_mut(&mut self, key: u8) -> Option<&mut NodePtr> {
        if self.children[key as usize].is_null() {
            None
        } else {
            Some(&mut self.children[key as usize])
        }
    }

    pub fn first_child(&self) -> Option<&NodePtr> {
        self.children.iter().find(|&ptr| !ptr.is_null())
    }

    pub fn add_child(&mut self, key: u8, child: NodePtr) -> Option<NodePtr> {
        let res = mem::replace(&mut self.children[key as usize], child).into_option();
        if res.is_none() {
            self.header.inc_count();
        }
        res
    }

    pub fn remove_child(&mut self, key: u8) -> Option<NodePtr> {
        let res = mem::take(&mut self.children[key as usize]).into_option();
        if res.is_some() {
            self.header.dec_count();
        }
        res
    }

    pub fn should_grow(&self) -> bool {
        false
    }

    pub fn should_shrink(&self) -> bool {
        self.header.size() <= Node48::CAPACITY / 2
    }

    pub fn grow(self) -> ! {
        unreachable!("Node256 cannot grow")
    }

    pub fn shrink(self) -> Node48 {
        assert!(self.header.size() < Node48::CAPACITY);

        let (mut header, children) = self.decouple();

        // change header and construct Node48
        header.change_type(NodeType::Node48);
        header.reset_count();
        let mut node48 = Node48::from_header(header);

        for (key, child) in children.into_iter().enumerate() {
            if !child.is_null() {
                node48.add_child(key as u8, child);
            }
        }

        node48
    }

    /// Decouple this struct. Because [Node256] implements [Drop], its fields
    /// cannot be moved out directly.
    fn decouple(self) -> (Header, [NodePtr; Self::CAPACITY]) {
        #[repr(C)]
        struct NotDropNode256 {
            header: Header,
            children: [NodePtr; Node256::CAPACITY],
        }

        let node256: NotDropNode256 = unsafe { mem::transmute(self) };
        let NotDropNode256 { header, children } = node256;

        (header, children)
    }

    pub fn drop<V>(self) {
        for ptr in self.children {
            if !ptr.is_null() {
                ptr.drop::<V>();
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::leaf::NodeLeaf;

    #[test]
    fn insert_find_remove() {
        let mut node = Node256::new();

        node.add_child(u8::MAX, NodePtr::from_usize(1));
        assert_eq!(*node.find_key(u8::MAX).unwrap(), NodePtr::from_usize(1));
        assert!(node.find_key(0).is_none());
        assert!(node.find_key(2).is_none());
        assert!(node.find_key(u8::MAX - 1).is_none());
        assert!(node.remove_child(0).is_none());
        assert!(node.remove_child(2).is_none());
        assert!(node.remove_child(u8::MAX - 1).is_none());
        assert_eq!(node.remove_child(u8::MAX).unwrap(), NodePtr::from_usize(1));
        assert!(node.find_key(u8::MAX).is_none());

        node.drop::<()>();
    }

    #[test]
    fn insert_duplicate() {
        let mut node = Node256::new();

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

        node.drop::<()>();
    }

    #[test]
    fn shrink_to_node48() {
        let mut node256 = Node256::new();
        for i in 0..Node48::CAPACITY - 1 {
            assert!(node256
                .add_child(i as u8, NodePtr::from_usize(i * 10 + 201))
                .is_none());
        }

        let node48 = node256.shrink();

        assert_eq!(node48.header.size(), Node48::CAPACITY - 1);
        assert_eq!(node48.header.node_type(), NodeType::Node48);

        for i in 0..Node48::CAPACITY - 1 {
            assert_eq!(
                *node48.find_key(i as u8).unwrap(),
                NodePtr::from_usize(i * 10 + 201)
            );
        }
        for i in Node48::CAPACITY..=u8::MAX as usize {
            assert!(node48.find_key(i as u8).is_none());
        }
        node48.drop::<()>();
    }

    #[test]
    fn drop_node256() {
        let mut node256 = Node256::new();
        for i in 0..4 {
            let leaf_ptr = NodePtr::boxed(NodeLeaf::new(
                vec![i],
                NodePtr::from_usize(i as usize * 8 + 1024),
            ));
            node256.add_child(i, leaf_ptr);
        }
        node256.drop::<()>();
    }
}
