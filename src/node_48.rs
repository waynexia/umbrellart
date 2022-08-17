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

        // Node48 will put all valid items in the front. So we can copy that segment
        // into new node.
        node256.children.copy_from_slice(&children[0..item_count]);
        node256.keys.copy_from_slice(&keys);

        node256
    }

    pub fn shrink(self) -> Node16 {
        assert!(self.should_shrink());
        let Self {
            mut header,
            children,
            keys,
        } = self;
        let item_count = header.size();

        // change header and construct Node256
        header.change_type(NodeType::Node256);
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
