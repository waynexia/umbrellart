use std::mem;

use crate::node::{Header, NodePtr, NodeType};
use crate::node_48::Node48;

#[repr(C)]
#[derive(Debug)]
pub(crate) struct Node256 {
    header: Header,
    pub(crate) children: [NodePtr; Self::CAPACITY],
}

impl Node256 {
    /// How many item it can hold.
    const CAPACITY: usize = u8::MAX as usize + 1;

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

    pub fn new() -> Self {
        let header = Header::new(NodeType::Node48);
        Self {
            header,
            children: [NodePtr::default(); Self::CAPACITY],
        }
    }

    pub fn find_key(&self, key: u8) -> Option<NodePtr> {
        self.children[key as usize].into_option()
    }

    pub fn add_child(&mut self, key: u8, child: NodePtr) -> Option<NodePtr> {
        mem::replace(&mut self.children[key as usize], child).into_option()
    }

    pub fn remove_child(&mut self, key: u8) -> Option<NodePtr> {
        mem::take(&mut self.children[key as usize]).into_option()
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

        let Self {
            mut header,
            children,
        } = self;

        // change header and construct Node256
        header.change_type(NodeType::Node256);
        header.reset_count();
        let mut node48 = Node48::from_header(header);

        for (key, child) in children.into_iter().enumerate() {
            if !child.is_null() {
                node48.add_child(key as u8, child);
            }
        }

        node48
    }
}

#[cfg(test)]
mod test {
    use super::*;
}
