use crate::node::{Header, NodePtr, NodeType};
use crate::node_48::Node48;

#[repr(C)]
#[derive(Debug)]
pub(crate) struct Node256 {
    header: Header,
    pub(crate) children: [NodePtr; Self::CAPACITY],
    pub(crate) keys: [u8; Self::CAPACITY],
}

impl Node256 {
    /// How many item it can hold.
    const CAPACITY: usize = u8::MAX as usize + 1;

    #[allow(dead_code)]
    const fn assert_node4_size() {
        // 16 for header
        // 2048 (8 * 256) for children
        // 256 for keys
        const _: () = assert!(std::mem::size_of::<Node256>() == 2320);
    }

    /// Construct a [Node256] with existing [Header]. This is used to
    /// accomplish node expand/shrink.
    pub(crate) fn from_header(header: Header) -> Self {
        debug_assert!(header.node_type() == NodeType::Node256);
        Self {
            header,
            keys: [0; Self::CAPACITY],
            children: [NodePtr::default(); Self::CAPACITY],
        }
    }

    pub fn new() -> Self {
        let header = Header::new(NodeType::Node48);
        Self {
            header,
            keys: [0; Self::CAPACITY],
            children: [NodePtr::default(); Self::CAPACITY],
        }
    }

    pub fn find_key(&self, key: u8) -> Option<NodePtr> {
        let index = self.keys[key as usize];

        if !self.children[index as usize].is_null() {
            Some(self.children[index as usize])
        } else {
            None
        }
    }

    pub fn add_child(&mut self, key: u8, child: NodePtr) -> Option<NodePtr> {
        todo!()
    }

    pub fn remove_child(&mut self, key: u8) -> Option<NodePtr> {
        todo!()
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
        todo!()
    }
}

#[cfg(test)]
mod test {
    use super::*;
}
