use std::marker::PhantomData;
use std::ptr;

use crate::node_impl::Node4;

type PrefixCount = u32;

#[repr(u8)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum NodeType {
    Node4,
    Node16,
    Node48,
    Node256,
    Leaf,
}

struct AssertLessThan4<const N: u8>;

impl NodeType {
    pub(crate) const fn from_u8<const N: u8>() -> Self {
        match N {
            0 => Self::Node4,
            1 => Self::Node16,
            2 => Self::Node48,
            3 => Self::Node256,
            4 => Self::Leaf,
            // Sadly this cannot be checked in the compile time without incomplete feature
            // `generic_const_exprs`. And even with it the code are wired.
            _ => panic!("Unexpected Node Type"),
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct Header {
    node_type: NodeType,
    /// Item count
    size: u8,
    /// Number of prefix collapsed in this node. This length can greater than
    /// [MAX_PREFIX_STORED], in this case some prefix bytes are optimistic
    /// dropped.
    ///
    /// [MAX_PREFIX_STORED]: #associatedconstant.MAX_PREFIX_STORED
    prefix_len: PrefixCount,
    /// Optimistic prefix collapse. Only store up to [MAX_PREFIX_STORED] bytes.
    ///
    /// [MAX_PREFIX_STORED]: #associatedconstant.MAX_PREFIX_STORED
    prefix: [u8; Self::MAX_PREFIX_STORED],
}

impl Header {
    pub const MAX_PREFIX_STORED: usize = 10;

    #[allow(dead_code)]
    const fn assert_header_size() {
        const _: () = assert!(std::mem::size_of::<Header>() == 16);
    }

    pub fn new(node_type: NodeType) -> Self {
        Self {
            node_type,
            size: 0,
            prefix_len: 0,
            prefix: [0; Self::MAX_PREFIX_STORED],
        }
    }

    pub fn size(&self) -> usize {
        self.size as usize
    }

    pub fn prefix_len(&self) -> usize {
        self.prefix_len as usize
    }

    /// Increase item count.
    pub fn inc_count(&mut self) {
        self.size += 1;
    }

    /// Decrease item count.
    pub fn dec_count(&mut self) {
        self.size -= 1;
    }

    pub fn node_type(&self) -> NodeType {
        self.node_type
    }

    pub fn change_type(&mut self, new_type: NodeType) {
        self.node_type = new_type;
    }

    /// Compare prefix stored in this header. Only
    /// _min([prefix_len],[MAX_PREFIX_STORED])_ bytes will be compared. If
    /// all stored prefix bytes are matched and _[prefix_len] >
    /// [MAX_PREFIX_STORED]_, this comparison is ignoring some bytes due to
    /// optimistic path collapse.
    ///
    /// Return whether the key matches and whether optimistic path collapse
    /// happened.
    ///
    /// [prefix_len]: #field.prefix_len
    /// [MAX_PREFIX_STORED]: #associatedconstant.MAX_PREFIX_STORED
    pub fn compare_prefix(&self, key: &[u8]) -> (bool, bool) {
        let valid_len = self.prefix_len().min(Self::MAX_PREFIX_STORED);
        let match_result = key[0..valid_len] == self.prefix[0..valid_len];
        let optimistic = self.prefix_len() > Self::MAX_PREFIX_STORED;

        (match_result, optimistic)
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct NodePtr(*const ());

impl NodePtr {
    pub fn from_ptr<T>(ptr: *const T) -> Self {
        Self(ptr as _)
    }

    pub fn from_mut_ptr<T>(ptr: *mut T) -> Self {
        Self(ptr as *const T as _)
    }

    pub fn from_usize(ptr: usize) -> Self {
        Self(ptr as _)
    }

    pub fn is_null(&self) -> bool {
        self.0.is_null()
    }

    /// # Safety
    ///
    /// [NodePtr] should only comes from a valid Node. All nodes are
    /// `#[repr(C)]` and with [Header] on the first position so it is safe to
    /// cast to a [Header] reference if this pointer is not null.
    pub fn try_as_header(&self) -> Option<&Header> {
        if self.is_null() {
            None
        } else {
            unsafe { Some(&*(self.0 as *const Header)) }
        }
    }
}

impl Default for NodePtr {
    fn default() -> Self {
        Self(ptr::null())
    }
}

pub(crate) struct Node<V> {
    _marker: PhantomData<V>,
}

impl<V> Node<V> {
    pub fn search<'a>(node_ref: NodePtr, key: &[u8]) -> Option<&'a V> {
        let mut curr_node = node_ref;
        let key_len = key.len();
        let mut depth = 0;
        let mut has_optimistic_skipped = false;

        loop {
            let header = curr_node.try_as_header()?;
            let (matched, skipped) = header.compare_prefix(&key[depth..]);
            has_optimistic_skipped |= skipped;
            if !matched {
                return None;
            }
            depth += header.prefix_len();
            curr_node =
                unsafe { &*(header as *const Header as *const Node4) }.find_key(key[depth])?;
            if depth == key_len {
                todo!("check result and return")
            }
        }

        None
    }
}

#[cfg(test)]
mod test {
    use super::*;
}
