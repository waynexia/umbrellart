use crate::dynamic_node::Node16;
use crate::node::{Header, NodePtr, NodeType};
use crate::node_256::Node256;

#[repr(C)]
#[derive(Debug)]
pub(crate) struct Node48 {
    header: Header,
    children: [NodePtr; Self::CAPACITY],
    keys: [u8; Self::MAX],
}

impl Node48 {
    /// Alias for [u8::MAX], used as key slot's capacity.
    const MAX: usize = u8::MAX as usize;
    /// How many item it can hold.
    const CAPACITY: usize = 48;
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
    /// Caller should ensure the capacity.
    pub fn add_child(&mut self, key: u8, child: NodePtr) -> Option<NodePtr> {
        assert!(self.header.size() <= Self::CAPACITY);
        let index = self.keys[key as usize];

        // already exist, replace previous key.
        if index != Self::NULL_INDEX {
            let exist = self.children[index as usize];
            if exist.try_as_header().unwrap().node_type() == NodeType::Leaf {
                self.children[index as usize] = child;
                return Some(exist);
            } else {
                todo!("already exist but isn't leaf node");
            }
        }

        let slot = self.header.size();
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

        // remove the vacancy
        for i in (index as usize + 1)..self.header.size() {
            self.children[i] = self.children[i - 1];
        }
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
        todo!()
    }

    pub fn shrink(self) -> Node16 {
        todo!()
    }
}
