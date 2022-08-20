use crate::dynamic_node::Node16;
use crate::node::{Header, NodePtr, NodeType};
use crate::node_256::Node256;

#[repr(C)]
#[derive(Debug)]
pub(crate) struct Node48 {
    pub(crate) header: Header,
    pub(crate) children: [NodePtr; Self::CAPACITY],
    pub(crate) keys: [u8; Self::MAX],
}

impl Node48 {
    /// Alias for [u8::MAX], used as key slot's capacity.
    const MAX: usize = u8::MAX as usize + 1;
    /// How many item it can hold.
    pub const CAPACITY: usize = 48;
    /// Sentinel value for an vacant key.
    const NULL_INDEX: u8 = u8::MAX;

    #[allow(dead_code)]
    const fn assert_node4_size() {
        // 16 for header
        // 384 (8 * 48) for children
        // 256 for keys
        const _: () = assert!(std::mem::size_of::<Node48>() == 656);
    }

    /// Construct a [Node48] with existing [Header]. This is used to
    /// accomplish node expand/shrink.
    pub(crate) fn from_header(header: Header) -> Self {
        debug_assert!(header.node_type() == NodeType::Node48);
        Self {
            header,
            keys: [Self::NULL_INDEX; Self::MAX],
            children: [NodePtr::default(); Self::CAPACITY],
        }
    }

    pub fn new() -> Self {
        let header = Header::new(NodeType::Node48);
        Self {
            header,
            keys: [Self::NULL_INDEX; Self::MAX],
            children: [NodePtr::default(); Self::CAPACITY],
        }
    }

    pub fn find_key(&self, key: u8) -> Option<NodePtr> {
        let index = self.keys[key as usize];

        if index != Self::NULL_INDEX && !self.children[index as usize].is_null() {
            Some(self.children[index as usize])
        } else {
            None
        }
    }

    /// # Notice
    ///
    /// Caller should ensure the capacity. For simplicity this needs at least
    /// one empty slot (don't consider the situation that a duplicate insertion
    /// won't occupy new slot).
    pub fn add_child(&mut self, key: u8, child: NodePtr) -> Option<NodePtr> {
        assert!(self.header.size() < Self::CAPACITY);
        let index = self.keys[key as usize];

        // already exist, replace previous key.
        if index != Self::NULL_INDEX {
            let exist = self.children[index as usize];
            // todo: branch on Ptr's type
            self.children[index as usize] = child;
            return Some(exist);
        }

        // find a slot
        let mut slot = 0;
        while slot <= Self::CAPACITY {
            if self.children[slot].is_null() {
                break;
            }
            // It will find, in the correct case...
            slot += 1;
        }

        self.children[slot] = child;
        self.keys[key as usize] = slot as u8;
        self.header.inc_count();

        None
    }

    pub fn remove_child(&mut self, key: u8) -> Option<NodePtr> {
        // doesn't exist, nothing to do
        if self.keys[key as usize] == Self::NULL_INDEX {
            return None;
        }

        // remove existing
        let index = self.keys[key as usize];
        let removed = self.children[index as usize];
        self.children[index as usize] = NodePtr::default();
        self.keys[key as usize] = Self::NULL_INDEX;
        self.header.dec_count();

        Some(removed)
    }

    pub fn should_grow(&self) -> bool {
        self.header.size() >= Self::CAPACITY
    }

    pub fn should_shrink(&self) -> bool {
        self.header.size() <= Node16::CAPACITY / 2
    }

    pub fn grow(self) -> Node256 {
        let Self {
            mut header,
            children,
            keys,
        } = self;
        let item_count = header.size();

        // change header and construct Node256
        header.change_type(NodeType::Node256);
        header.reset_count();
        let mut node256 = Node256::from_header(header);

        for (key, child) in keys.into_iter().zip(children.into_iter()) {
            if key != Self::NULL_INDEX {
                node256.add_child(key, child);
            }
        }

        node256
    }

    pub fn shrink(self) -> Node16 {
        assert!(self.header.size() < Node16::CAPACITY);

        let Self {
            mut header,
            children,
            keys,
        } = self;

        // change header and construct Node256
        header.change_type(NodeType::Node16);
        header.reset_count();
        let mut node16 = Node16::from_header(header);

        for (key, index) in keys.into_iter().enumerate() {
            if index != Self::NULL_INDEX {
                node16.add_child(key as u8, children[index as usize]);
            }
        }

        node16
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn insert_find_remove() {
        let mut node = Node48::new();

        node.add_child(u8::MAX, NodePtr::from_usize(2));
        assert_eq!(node.find_key(u8::MAX).unwrap(), NodePtr::from_usize(2));
        assert!(node.find_key(0).is_none());
        assert!(node.find_key(2).is_none());
        assert!(node.find_key(u8::MAX - 1).is_none());
        assert!(node.remove_child(0).is_none());
        assert!(node.remove_child(2).is_none());
        assert!(node.remove_child(u8::MAX - 1).is_none());
        assert_eq!(node.remove_child(u8::MAX).unwrap(), NodePtr::from_usize(2));
        assert!(node.find_key(u8::MAX).is_none());
    }

    #[test]
    fn erases() {
        let mut node = Node48::new();

        for _ in 0..4 {
            for i in 0..u8::MAX {
                assert!(node
                    .add_child(i, NodePtr::from_usize(i as usize * 10 + 40))
                    .is_none());
                assert_eq!(
                    node.remove_child(i,).unwrap(),
                    NodePtr::from_usize(i as usize * 10 + 40)
                );
            }
        }
    }

    #[test]
    fn insert_duplicate() {
        let mut node = Node48::new();

        assert!(node.add_child(1, NodePtr::from_usize(10)).is_none());
        assert_eq!(
            node.add_child(1, NodePtr::from_usize(100)).unwrap(),
            NodePtr::from_usize(10)
        );

        assert!(node.add_child(2, NodePtr::from_usize(20)).is_none());
        assert!(node.add_child(3, NodePtr::from_usize(30)).is_none());
        assert_eq!(node.remove_child(2).unwrap(), NodePtr::from_usize(20));
        assert_eq!(
            node.add_child(3, NodePtr::from_usize(300)).unwrap(),
            NodePtr::from_usize(30)
        );
        assert!(node.add_child(2, NodePtr::from_usize(200)).is_none());
        assert_eq!(
            node.add_child(2, NodePtr::from_usize(2000)).unwrap(),
            NodePtr::from_usize(200)
        );
        assert_eq!(node.find_key(2).unwrap(), NodePtr::from_usize(2000));
    }

    #[test]
    fn insert_to_full() {
        let mut node = Node48::new();

        for i in 0..Node48::CAPACITY {
            assert!(node
                .add_child(i as u8, NodePtr::from_usize(i * 10 + 40))
                .is_none());
        }

        assert!(node.should_grow());
    }

    #[test]
    fn grow_to_node256() {
        let mut node48 = Node48::new();
        for i in 0..Node48::CAPACITY - 1 {
            assert!(node48
                .add_child(i as u8, NodePtr::from_usize(i * 10 + 40))
                .is_none());
        }

        let node256 = node48.grow();

        assert_eq!(node256.header.size(), Node48::CAPACITY - 1);
        assert_eq!(node256.header.node_type(), NodeType::Node256);

        for i in 0..Node48::CAPACITY - 1 {
            assert_eq!(
                node256.find_key(i as u8).unwrap(),
                NodePtr::from_usize(i * 10 + 40)
            );
        }
        for i in Node48::CAPACITY..=u8::MAX as usize {
            assert!(node256.find_key(i as u8).is_none());
        }
    }

    #[test]
    fn shrink_to_node16() {
        let mut node48 = Node48::new();
        for i in 0..Node16::CAPACITY - 1 {
            assert!(node48
                .add_child(i as u8, NodePtr::from_usize(i * 10 + 40))
                .is_none());
        }

        let node16 = node48.shrink();

        assert_eq!(node16.header.size(), Node16::CAPACITY - 1);
        assert_eq!(node16.header.node_type(), NodeType::Node16);

        for i in 0..Node16::CAPACITY - 1 {
            assert_eq!(
                node16.find_key(i as u8).unwrap(),
                NodePtr::from_usize(i * 10 + 40)
            );
        }
        for i in Node16::CAPACITY..=u8::MAX as usize {
            assert!(node16.find_key(i as u8).is_none());
        }
    }
}

#[cfg(kani)]
mod kani {}
