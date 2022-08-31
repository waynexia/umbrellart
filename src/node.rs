use std::marker::PhantomData;
use std::ptr;

use crate::dynamic_node::{Node16, Node4};
use crate::leaf::NodeLeaf;
use crate::node_256::Node256;
use crate::node_48::Node48;

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
    size: u16,
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
    pub const MAX_PREFIX_STORED: usize = 8;

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

    pub fn with_prefix(node_type: NodeType, prefix: &[u8]) -> Self {
        let mut header = Self::new(node_type);

        let stored_prefix_len = Self::MAX_PREFIX_STORED.min(prefix.len());
        header.prefix_len = prefix.len() as _;
        header.prefix[0..stored_prefix_len].copy_from_slice(&prefix[0..stored_prefix_len]);

        header
    }

    pub fn size(&self) -> usize {
        self.size as usize
    }

    /// Retrieve all prefix bytes stored in this header.
    pub fn prefix(&self) -> &[u8] {
        &self.prefix[0..self.prefix_len as usize]
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

    /// Reset item counter. Note this is only for growing a node.
    pub fn reset_count(&mut self) {
        self.size = 0;
    }

    /// Compare prefix stored in this header. Only
    /// _min([prefix_len],[MAX_PREFIX_STORED])_ bytes will be compared. If
    /// all stored prefix bytes are matched and _[prefix_len] >
    /// [MAX_PREFIX_STORED]_ means this comparison has ignored some bytes due to
    /// optimistic path collapse.
    ///
    /// Return how many bytes matches and whether optimistic path collapse
    /// happened.
    ///
    /// [prefix_len]: #field.prefix_len
    /// [MAX_PREFIX_STORED]: #associatedconstant.MAX_PREFIX_STORED
    pub fn compare_prefix(&self, key: &[u8]) -> (usize, bool) {
        let valid_len = self.prefix_len().min(Self::MAX_PREFIX_STORED);
        let mut optimistic = self.prefix_len() > Self::MAX_PREFIX_STORED;

        let mut match_result = 0;
        for i in 0..valid_len {
            if key[i] == self.prefix[i] {
                match_result += 1;
            } else {
                break;
            }
        }

        optimistic &= match_result >= valid_len;

        (match_result, optimistic)
    }

    /// Fully compare key with prefix stored in this header. Return whether the
    /// key matches and whether optimistic path collapse happened. Refer to
    /// [compare_prefix](#method.compare_prefix) for details about path
    /// collapsing.
    pub fn compare_prefix_fully(&self, key: &[u8]) -> (bool, bool) {
        let (matched, optimistic) = self.compare_prefix(key);
        let is_fully_match = matched == self.prefix_len().min(Self::MAX_PREFIX_STORED);

        (is_fully_match, optimistic)
    }
}

#[derive(Debug, Clone, Copy)]
#[cfg_attr(test, derive(PartialEq, Eq))]
pub(crate) struct NodePtr(pub(crate) *mut ());

impl NodePtr {
    #[inline]
    pub fn from_ptr<T>(ptr: *const T) -> Self {
        Self(ptr as _)
    }

    /// "Leak" a item and return its pointer
    #[inline]
    pub fn boxed<T>(item: T) -> Self {
        let ptr = Box::leak(Box::new(item));
        Self(ptr as *mut T as *mut ())
    }

    #[inline]
    pub fn cast_to<T>(&self) -> Option<&T> {
        if !self.is_valid_rust_pointer() {
            return None;
        }

        unsafe { Some(&*(self.0 as *const T)) }
    }

    #[inline]
    pub fn from_usize(ptr: usize) -> Self {
        Self(ptr as _)
    }

    #[inline]
    pub fn is_null(&self) -> bool {
        self.0.is_null()
    }

    /// # Safety
    ///
    /// [NodePtr] should only comes from a valid Node. All nodes are
    /// `#[repr(C)]` and with [Header] on the first position so it is safe to
    /// cast to a [Header] reference if this pointer is not null.
    #[inline]
    pub fn try_as_header(&self) -> Option<&Header> {
        if self.is_null() {
            None
        } else {
            unsafe { Some(&*(self.0 as *const Header)) }
        }
    }

    #[inline]
    pub fn try_as_header_mut(&mut self) -> Option<&mut Header> {
        if self.is_null() {
            None
        } else {
            unsafe { Some(&mut *(self.0 as *mut Header)) }
        }
    }

    #[inline]
    pub fn into_option(self) -> Option<Self> {
        if self.is_null() {
            None
        } else {
            Some(self)
        }
    }

    /// Drop the resource referenced by this pointer. Only when the resource is
    /// one of the `Node`s will take efforts.
    ///
    /// Because [NodePtr] is [Copy]-able, implement [Drop] is not good.
    pub fn drop(self) {
        if !self.is_valid_rust_pointer() {
            return;
        }

        unsafe {
            match self.try_as_header().unwrap().node_type() {
                NodeType::Node4 => _ = Node4::from_node_ptr(self),
                NodeType::Node16 => _ = Node16::from_node_ptr(self),
                NodeType::Node48 => _ = Node48::from_node_ptr(self),
                NodeType::Node256 => _ = Node256::from_node_ptr(self),
                NodeType::Leaf => _ = NodeLeaf::from_node_ptr(self),
            }
        }
    }

    /// Check whether this pointer is null or unaligned by 2
    #[inline]
    fn is_valid_rust_pointer(&self) -> bool {
        !self.is_null() && self.0.is_aligned_to(2)
    }
}

impl Default for NodePtr {
    fn default() -> Self {
        Self(ptr::null_mut())
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
            let (matched, skipped) = header.compare_prefix_fully(&key[depth..]);
            has_optimistic_skipped |= skipped;
            if !matched {
                return None;
            }
            depth += header.prefix_len();
            curr_node = Self::find_key(curr_node, key[depth])?;

            if depth == key_len {
                todo!("check result and return")
            }
        }
    }

    pub fn insert(node_ref: &mut NodePtr, key: &[u8], leaf: NodePtr) -> Option<NodePtr> {
        let mut curr_node = node_ref;
        let key_len = key.len();
        let mut depth = 0;

        loop {
            // replace a empty node with inserted leaf.
            if curr_node.is_null() {
                *curr_node = leaf;
                return None;
            }

            let header = curr_node.try_as_header_mut().unwrap();
            // expand leaf node to a Node4
            if header.node_type() == NodeType::Leaf {
                // Safety: both `curr_node` and `leaf` should be legal node pointers.
                let lhs = curr_node.cast_to::<NodeLeaf>().unwrap();
                let rhs = leaf.cast_to::<NodeLeaf>().unwrap();

                // make a new inner node with the common parts of two leaves as prefix
                let common_key = lhs.get_common_key(rhs, depth);
                depth += common_key.len();
                let new_header = Header::with_prefix(NodeType::Node4, common_key);
                let mut new_node = Node4::from_header(new_header);
                new_node.add_child(key[depth], leaf);
                new_node.add_child(lhs.load_key().unwrap()[depth], *curr_node);

                // finish this expand. replace previous leaf's pointer with the new inner node
                *curr_node = NodePtr::boxed(new_node);
                return None;
            }

            // check how many prefix bytes are matched
            let (matched, is_optimistic_match) = header.compare_prefix(&key[depth..]);
            if is_optimistic_match {
                todo!("compare with full prefix");
            }

            // prefix mismatch, need to generate a new inner node for the common part
            if matched != header.prefix_len() {
                // make a new parent node then add leaf and curr_node to it.
                let new_header = Header::with_prefix(NodeType::Node4, &key[depth..]);
                let mut new_node = Node4::from_header(new_header);
                new_node.add_child(key[depth + matched], leaf);
                // todo: should copy from a fully expanded prefix, not copy_within.
                // todo: set header's length
                header
                    .prefix
                    .copy_within(matched..Header::MAX_PREFIX_STORED, 0);
                // todo: handle omitted prefix (header.prefix)
                new_node.add_child(header.prefix[matched], *curr_node);

                // replace curr_node with the new node.
                *curr_node = NodePtr::boxed(new_node);
                return None;
            }
            depth += matched;
            let next_node = Node::<V>::find_key_mut(*curr_node, key[depth]);
            if let Some(node) = next_node {
                curr_node = node;
                continue;
            } else {
                if Node::<V>::should_grow(*curr_node) {
                    *curr_node = Node::<V>::grow(*curr_node);
                }
                Node::<V>::add_child(*curr_node, key[depth], leaf);
                // todo: handle the result of `add_child`
                return None;
            }
        }
    }
}

macro_rules! dispatch_node_fn {
    ($fn_name:ident, ($($v:tt: $t:ty),*), $out:ty) => {
        fn $fn_name(node_ref:NodePtr, $($v:$t),*) -> $out{
            let header = node_ref.try_as_header().unwrap();
            match header.node_type() {
                NodeType::Node4 => {
                    let node: &mut Node4 =
                        unsafe { &mut *(std::mem::transmute::<*const (), *mut Node4>(node_ref.0)) };
                    node.$fn_name($($v),*)
                }
                NodeType::Node16 => {
                    let node: &mut Node16 =
                        unsafe { &mut *(std::mem::transmute::<*const (), *mut Node16>(node_ref.0)) };
                    node.$fn_name($($v),*)
                }
                NodeType::Node48 => {
                    let node: &mut Node48 =
                        unsafe { &mut *(std::mem::transmute::<*const (), *mut Node48>(node_ref.0)) };
                    node.$fn_name($($v),*)
                }
                NodeType::Node256 => {
                    let node: &mut Node256 =
                        unsafe { &mut *(std::mem::transmute::<*const (), *mut Node256>(node_ref.0)) };
                    node.$fn_name($($v),*)
                }
                NodeType::Leaf => {
                    unreachable!("This function is only for inner nodes")
                }
            }
        }
    };

}

/// Inner methods implementations for variant nodes.
impl<V> Node<V> {
    dispatch_node_fn!(find_key, (key: u8), Option<NodePtr>);

    dispatch_node_fn!(find_key_mut, (key: u8), Option<&'static mut NodePtr>);

    dispatch_node_fn!(add_child, (key: u8, child: NodePtr), Option<NodePtr>);

    dispatch_node_fn!(remove_child, (key: u8), Option<NodePtr>);

    dispatch_node_fn!(should_grow, (), bool);

    dispatch_node_fn!(should_shrink, (), bool);

    fn grow(node_ptr: NodePtr) -> NodePtr {
        let header = node_ptr.try_as_header().unwrap();
        match header.node_type() {
            NodeType::Node4 => {
                let node: Node4 = unsafe { Node4::from_node_ptr(node_ptr) };
                NodePtr::boxed(node.grow())
            }
            NodeType::Node16 => {
                let node: Node16 = unsafe { Node16::from_node_ptr(node_ptr) };
                NodePtr::boxed(node.grow())
            }
            NodeType::Node48 => {
                let node: Node48 = unsafe { Node48::from_node_ptr(node_ptr) };
                NodePtr::boxed(node.grow())
            }
            NodeType::Node256 => {
                let node: Node256 = unsafe { Node256::from_node_ptr(node_ptr) };
                #[allow(unreachable_code)]
                NodePtr::boxed(node.grow())
            }
            NodeType::Leaf => {
                unreachable!("This function is only for inner nodes")
            }
        }
    }

    fn shrink(node_ptr: NodePtr) -> NodePtr {
        let header = node_ptr.try_as_header().unwrap();
        match header.node_type() {
            NodeType::Node4 => {
                let node: Node4 = unsafe { Node4::from_node_ptr(node_ptr) };
                #[allow(unreachable_code)]
                NodePtr::boxed(node.shrink())
            }
            NodeType::Node16 => {
                let node: Node16 = unsafe { Node16::from_node_ptr(node_ptr) };
                NodePtr::boxed(node.shrink())
            }
            NodeType::Node48 => {
                let node: Node48 = unsafe { Node48::from_node_ptr(node_ptr) };
                NodePtr::boxed(node.shrink())
            }
            NodeType::Node256 => {
                let node: Node256 = unsafe { Node256::from_node_ptr(node_ptr) };
                NodePtr::boxed(node.shrink())
            }
            NodeType::Leaf => {
                unreachable!("This function is only for inner nodes")
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn new_by_insertion() {
        let mut root = NodePtr::default();
        Node::<()>::insert(&mut root, &[1, 2, 3, 4, 5, 6], NodePtr::from_usize(10));

        assert_eq!(root, NodePtr::from_usize(10));
    }

    #[test]
    fn no_prefix_insertion() {
        let mut root = NodePtr::default();
        for i in 0..=u8::MAX {
            println!("inserting {}", i);
            let leaf_ptr = NodePtr::boxed(NodeLeaf::new(
                vec![i],
                NodePtr::from_usize(i as usize * 8 + 1024),
            ));
            println!("leaf pointer: {:?}", leaf_ptr);
            assert!(Node::<()>::insert(&mut root, &[i], leaf_ptr).is_none());
            println!("root pointer: {:?}", root);
        }

        root.drop();
    }
}
