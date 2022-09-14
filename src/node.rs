use std::marker::PhantomData;
use std::ptr;

use crate::dynamic_node::{Node16, Node4};
use crate::leaf::NodeLeaf;
use crate::node_256::Node256;
use crate::node_48::Node48;
use crate::utils;

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
        let valid = Self::MAX_PREFIX_STORED.min(self.prefix_len as usize);
        &self.prefix[0..valid]
    }

    /// Get the actual prefix's length, include optimistic ignored parts.
    pub fn prefix_len(&self) -> usize {
        self.prefix_len as usize
    }

    pub fn set_prefix(&mut self, new_prefix: &[u8]) {
        // leaf node doesn't have prefix
        if self.node_type == NodeType::Leaf {
            return;
        }

        let valid = new_prefix.len().min(Self::MAX_PREFIX_STORED);
        self.prefix[0..valid].copy_from_slice(&new_prefix[0..valid]);
        self.prefix_len = new_prefix.len() as _;
    }

    pub fn is_prefix_omitted(&self) -> bool {
        self.prefix_len as usize > Self::MAX_PREFIX_STORED
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
        for (i, byte) in key.iter().enumerate().take(valid_len) {
            if *byte == self.prefix[i] {
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
    /// "Leak" a item and return its pointer
    #[inline]
    pub fn boxed<T>(item: T) -> Self {
        let ptr = Box::leak(Box::new(item));
        Self(ptr as *mut T as *mut ())
    }

    #[inline]
    pub fn unbox<T>(self) -> T {
        assert!(self.is_valid_rust_pointer());
        unsafe { Box::into_inner(Box::from_raw(self.0 as *const T as *mut T)) }
    }

    #[inline]
    pub fn cast_to<T>(&self) -> Option<&T> {
        if !self.is_valid_rust_pointer() {
            return None;
        }

        unsafe { Some(&*(self.0 as *const T)) }
    }

    #[inline]
    pub fn cast_to_mut<T>(&mut self) -> Option<&mut T> {
        if !self.is_valid_rust_pointer() {
            return None;
        }

        unsafe { Some(&mut *(self.0 as *const T as *mut T)) }
    }

    #[cfg(test)]
    #[inline]
    pub fn from_usize(ptr: usize) -> Self {
        Self(ptr::from_exposed_addr_mut(ptr))
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
    pub fn drop<V>(self) {
        if !self.is_valid_rust_pointer() {
            return;
        }

        unsafe {
            match self.try_as_header().unwrap().node_type() {
                NodeType::Node4 => Node4::from_node_ptr(self).drop::<V>(),
                NodeType::Node16 => Node16::from_node_ptr(self).drop::<V>(),
                NodeType::Node48 => Node48::from_node_ptr(self).drop::<V>(),
                NodeType::Node256 => Node256::from_node_ptr(self).drop::<V>(),
                NodeType::Leaf => {
                    let item = NodeLeaf::from_node_ptr(self).value;
                    if item.is_valid_rust_pointer() {
                        item.unbox::<V>();
                    }
                }
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
    pub fn search<'a>(node_ref: &'a NodePtr, key: &[u8]) -> Option<&'a NodePtr> {
        let mut curr_node = node_ref;
        let mut depth = 0;
        let mut has_optimistic_skipped = false;

        loop {
            if curr_node.is_null() {
                return None;
            }

            let header = curr_node.try_as_header()?;
            if header.node_type() == NodeType::Leaf {
                let leaf = curr_node.cast_to::<NodeLeaf>().unwrap();
                if !has_optimistic_skipped || leaf.is_key_match(key) {
                    return Some(curr_node);
                }
                return None;
            }

            let (matched, is_optimistic_match) = header.compare_prefix_fully(&key[depth..]);
            has_optimistic_skipped |= is_optimistic_match;
            if !matched {
                return None;
            }
            depth += header.prefix_len();
            curr_node = Self::find_key(*curr_node, key[depth])?;
            depth += 1;
        }
    }

    pub fn insert(node_ref: &mut NodePtr, key: &[u8], leaf: NodePtr) -> Option<NodePtr> {
        let mut curr_node = node_ref;
        let mut depth = 0;

        loop {
            // replace a empty node with inserted leaf.
            if curr_node.is_null() {
                *curr_node = leaf;
                return None;
            }

            let header = curr_node.try_as_header().unwrap();
            // expand leaf node to a Node4
            if header.node_type() == NodeType::Leaf {
                // Safety: both `curr_node` and `leaf` should be legal node pointers.
                let lhs = curr_node.cast_to::<NodeLeaf>().unwrap();
                let rhs = leaf.cast_to::<NodeLeaf>().unwrap();
                let common_key = lhs.get_common_key(rhs, depth);

                // Inserting the same key again, replace it.
                if common_key == &key[depth..] {
                    let old_leaf = curr_node.unbox::<NodeLeaf>();
                    let old_value = old_leaf.value;
                    *curr_node = leaf;
                    return Some(old_value);
                }

                // make a new inner node with the common parts of two leaves as prefix
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
            // todo: refine these. Only when (1) compare omitted prefix and (2) extending
            // prefix, need load full key.
            let prefix_len = header.prefix_len();
            let (mut matched, is_optimistic_match) = header.compare_prefix(&key[depth..]);
            let curr_prefix = if header.is_prefix_omitted() {
                Self::load_full_key(curr_node).unwrap()[depth..depth + prefix_len].to_vec()
            } else {
                header.prefix().to_owned()
            };
            if is_optimistic_match {
                // Safety: Non-null node should contains k-v pair(s)
                let full_key = Self::load_full_key(curr_node).unwrap();
                matched =
                    utils::compare_slices(&key[depth..], &full_key[depth..depth + prefix_len]);
            }

            // prefix mismatch, need to generate a new inner node for the common part
            if matched != prefix_len {
                // truncate old node's prefix
                let header = curr_node.try_as_header_mut().unwrap();
                header.set_prefix(&curr_prefix[matched + 1..]);

                // make a new parent node then add leaf and curr_node to it.
                let new_header = Header::with_prefix(NodeType::Node4, &key[depth..depth + matched]);
                let mut new_node = Node4::from_header(new_header);
                new_node.add_child(key[depth + matched], leaf);
                new_node.add_child(curr_prefix[matched], *curr_node);

                // replace curr_node with the new node.
                *curr_node = NodePtr::boxed(new_node);
                return None;
            }

            // need not to change current node's prefix, continue insertion
            depth += matched;
            let next_node = Self::find_key_mut(*curr_node, key[depth]);
            if let Some(node) = next_node {
                // insert into next level
                curr_node = node;
                depth += 1;
                continue;
            } else {
                // insert into current node
                if Self::should_grow(*curr_node) {
                    *curr_node = Self::grow(*curr_node);
                }
                return Self::add_child(*curr_node, key[depth], leaf);
            }
        }
    }

    pub fn remove(node_ref: &mut NodePtr, key: &[u8]) -> Option<NodePtr> {
        let mut curr_node = node_ref;
        let mut depth = 0;

        loop {
            if curr_node.is_null() {
                return None;
            }

            let header = curr_node.try_as_header()?;
            if header.node_type() == NodeType::Leaf {
                let leaf = curr_node.cast_to::<NodeLeaf>()?;
                let mut result = None;
                if leaf.is_key_match(key) {
                    // replace this leaf node with NIL
                    result = Some(*curr_node);
                    *curr_node = NodePtr::default();
                }
                return result;
            }

            let (mut matched, is_optimistic_match) = header.compare_prefix(&key[depth..]);
            if is_optimistic_match {
                // Safety: Non-null node should contains k-v pair(s)
                let full_key = Self::load_full_key(curr_node).unwrap();
                matched = utils::compare_slices(
                    &key[depth..],
                    &full_key[depth..depth + header.prefix_len()],
                );
            }

            if matched != header.prefix_len() {
                return None;
            }

            depth += matched;
            let next_node = Self::find_key_mut(*curr_node, key[depth])?;
            let next_header = next_node.try_as_header()?;
            if next_header.node_type() == NodeType::Leaf {
                let leaf = next_node.cast_to::<NodeLeaf>()?;
                if !leaf.is_key_match(key) {
                    return None;
                }
                let res = Self::remove_child(*curr_node, key[depth])?;
                if Self::should_shrink(*curr_node) {
                    *curr_node = Self::shrink(*curr_node);
                } else {
                    // `should_shrink` will transmute `curr_node` to a mut ref, which invalids
                    // previous cast. Re-cast here to avoid UB.
                    let header = curr_node.try_as_header()?;
                    if header.node_type() == NodeType::Node4 && header.size() == 1 {
                        // collapse the inner Node4 with only one child.
                        // todo: maybe allow Node4 shrink to NodeLeaf
                        let node_depth = depth - matched;
                        let curr_prefix = if header.is_prefix_omitted() {
                            Self::load_full_key(curr_node).unwrap()
                                [node_depth..node_depth + header.prefix_len()]
                                .to_vec()
                        } else {
                            header.prefix().to_owned()
                        };
                        let node4 = curr_node.cast_to_mut::<Node4>()?;
                        let first_key = node4.first_key()?;
                        let mut last_child = *node4.first_child()?;
                        let last_child_header = last_child.try_as_header_mut()?;
                        // Adjust prefix. `curr_prefix` might be optimistically omitted, but it
                        // doesn't matter.
                        last_child_header.set_prefix(
                            &[
                                curr_prefix,
                                vec![first_key],
                                last_child_header.prefix().to_owned(),
                                // omitted part
                                vec![
                                    0;
                                    last_child_header.prefix_len()
                                        - last_child_header.prefix().len()
                                ],
                            ]
                            .concat(),
                        );
                        // remove that Node4
                        node4.remove_child(first_key);
                        (*curr_node).unbox::<Node4>();
                        *curr_node = last_child;
                    }
                }
                return Some(res);
            }
            curr_node = next_node;
            depth += 1;
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
    dispatch_node_fn!(find_key, (key: u8), Option<&'static NodePtr>);

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

    fn load_full_key(node_ptr: &NodePtr) -> Option<Vec<u8>> {
        let header = node_ptr.try_as_header().unwrap();
        match header.node_type() {
            NodeType::Node4 => {
                let node: &mut Node4 =
                    unsafe { &mut *(std::mem::transmute::<*const (), *mut Node4>(node_ptr.0)) };
                Self::load_full_key(node.first_child()?)
            }
            NodeType::Node16 => {
                let node: &mut Node16 =
                    unsafe { &mut *(std::mem::transmute::<*const (), *mut Node16>(node_ptr.0)) };
                Self::load_full_key(node.first_child()?)
            }
            NodeType::Node48 => {
                let node: &mut Node48 =
                    unsafe { &mut *(std::mem::transmute::<*const (), *mut Node48>(node_ptr.0)) };
                Self::load_full_key(node.first_child()?)
            }
            NodeType::Node256 => {
                let node: &mut Node256 =
                    unsafe { &mut *(std::mem::transmute::<*const (), *mut Node256>(node_ptr.0)) };
                Self::load_full_key(node.first_child()?)
            }
            NodeType::Leaf => {
                let node: &mut NodeLeaf =
                    unsafe { &mut *(std::mem::transmute::<*const (), *mut NodeLeaf>(node_ptr.0)) };
                node.load_key().map(|slice| slice.to_owned())
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
                NodePtr::from_usize(i as usize * 8 + 1024 + 1),
            ));
            println!("leaf pointer: {:?}", leaf_ptr);
            assert!(Node::<()>::insert(&mut root, &[i], leaf_ptr).is_none());
            println!("root pointer: {:?}", root);
        }

        root.drop::<()>();
    }

    fn do_insert_search_drop_test(keys: Vec<Vec<u8>>) {
        let cases = keys
            .into_iter()
            .enumerate()
            .map(|(i, key)| {
                let leaf_ptr = NodePtr::boxed(NodeLeaf::new(
                    key.clone(),
                    NodePtr::from_usize(i as usize * 8 + 1024 + 1),
                ));
                (key, leaf_ptr)
            })
            .collect::<Vec<_>>();

        let mut root = NodePtr::default();
        for (key, leaf) in cases.clone() {
            println!("inserting {:?}, leaf {:?}", key, leaf);
            Node::<()>::insert(&mut root, &key, leaf);
        }
        println!("insert finish");
        for (key, leaf) in cases.clone() {
            println!("searching {:?}", key);
            let result = Node::<()>::search(&root, &key).unwrap();
            assert_eq!(*result, leaf);
        }
        println!("search finish");
        for (key, leaf) in cases {
            println!("removing {:?}", key);
            let result = Node::<()>::remove(&mut root, &key).unwrap();
            assert_eq!(result, leaf);
            result.drop::<()>();
        }

        root.drop::<()>();
    }

    #[test]
    fn expend_stored_prefix() {
        do_insert_search_drop_test(vec![
            vec![1],
            vec![0, 0, 1],
            vec![0, 0, 0, 0],
            vec![3, 3, 3, 3],
            vec![4, 4, 4, 4, 4],
        ]);
    }

    #[test]
    fn expand_optimistic_omitted_prefix() {
        do_insert_search_drop_test(vec![
            vec![255, 0, 255],
            vec![
                255, 255, 7, 10, 10, 96, 10, 10, 10, 0, 10, 0, 0, 96, 10, 10, 10, 10, 10, 10, 7,
                255, 255, 10, 255, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            ],
            vec![255, 10, 255, 255, 255, 255, 7, 7, 7],
            vec![255, 255, 255, 7],
            vec![255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 7, 7],
            vec![120],
        ])
    }

    #[test]
    fn fuzz_case_1() {
        // reason: common length range is mis-calculated when expanding collapsed
        // prefix.
        do_insert_search_drop_test(vec![
            vec![255, 255, 255, 0],
            vec![255, 255, 255, 11, 0],
            vec![7, 7, 0],
            vec![255, 0],
        ])
    }

    #[test]
    fn fuzz_case_2() {
        // reason: extending collapsed prefix doesn't consider omitted parts.
        do_insert_search_drop_test(vec![
            vec![31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 255, 0],
            vec![31, 31, 31, 31, 31, 31, 31, 31, 31, 255, 255, 0],
            vec![255, 0],
        ])
    }

    #[test]
    #[cfg(not(miri))]
    fn fuzz_case_3() {
        // reason: `remove` doesn't consider optimistic prefix
        do_insert_search_drop_test(vec![
            vec![
                31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 0,
            ],
            vec![31, 31, 31, 31, 31, 31, 31, 31, 31, 0],
        ])
    }

    #[test]
    #[cfg(not(miri))]
    fn fuzz_case_4() {
        do_insert_search_drop_test(vec![
            vec![
                79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79,
                0,
            ],
            vec![79, 79, 79, 0],
            vec![
                79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 0,
            ],
        ]);
    }

    #[test]
    #[cfg(not(miri))]
    fn fuzz_case_7() {
        do_insert_search_drop_test(vec![
            vec![79, 79, 79, 79, 79, 79, 79, 79, 79, 96, 0],
            vec![79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 0],
            vec![
                79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 0,
            ],
        ]);
    }

    #[test]
    #[cfg(not(miri))]
    fn fuzz_case_8() {
        do_insert_search_drop_test(vec![
            vec![31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 0],
            vec![31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 0],
            vec![31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 0],
            vec![38, 0],
        ]);
    }

    #[test]
    fn duplicate_keys() {
        let mut root = NodePtr::default();

        let leaf_1 = NodePtr::boxed(NodeLeaf::new(vec![1, 0], NodePtr::from_usize(1024 + 1)));
        let leaf_2 = NodePtr::boxed(NodeLeaf::new(vec![1, 0], NodePtr::from_usize(1024 + 3)));

        // first insertion
        let res = Node::<()>::insert(&mut root, &[1, 0], leaf_1);
        assert!(res.is_none());

        // duplicate insertion
        let res = Node::<()>::insert(&mut root, &[1, 0], leaf_2);
        assert_eq!(res.unwrap(), NodePtr::from_usize(1024 + 1));

        // search
        let res = Node::<()>::search(&root, &[1, 0]).unwrap();
        assert_eq!(*res, leaf_2);

        // remove
        let res = Node::<()>::remove(&mut root, &[1, 0]).unwrap();
        assert_eq!(res, leaf_2);
        res.drop::<()>();

        root.drop::<()>();
    }
}
