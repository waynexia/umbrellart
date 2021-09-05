#![allow(unused_variables)]
#![allow(dead_code)]
use std::mem::{self, MaybeUninit};
use std::sync::atomic::Ordering::Relaxed;
use std::sync::atomic::{AtomicI8, AtomicU16, AtomicU8};
#[allow(unused_imports)]
use std::{fmt::Debug, path::Prefix};

use crate::node_ref::NodeRef;
use crate::utils::PrefixArray;

use log::{debug, info};

type PrefixCount = u32;
const MAX_PREFIX_STORED: usize = 10;

pub struct Node {}

impl Node {
    /// Search is a `read` operation, the node should be a copy(another referance) of one in tree.
    pub fn search<'a>(node: &NodeRef, key: &[u8], depth: usize) -> Option<NodeRef> {
        if node.is_null() {
            info!("search encounted a null ptr");
            return None;
        }
        // lazy expansion
        // run out of key bytes, should reach leaf node
        if depth == key.len() || Self::is_kvpair(&node) {
            if Self::is_leaf_match(&node, key) {
                if Self::is_kvpair(&node) {
                    return Some(node.refer());
                } else {
                    let leaf = Self::to_node4(&node).leaf.refer();
                    return if !leaf.is_null() {
                        Some(leaf)
                    } else {
                        // assert leaf exist?
                        None
                    };
                }
            }
            return None;
        }
        // check compressed path pessimistically
        if Self::check_prefix(&node, key, depth) != Self::get_prefix_len(&node) {
            println!(
                "prefix not match, {} != {}",
                Self::check_prefix(&node, key, depth),
                Self::get_prefix_len(&node)
            );
            debug!(
                "prefix not match, {} != {}",
                Self::check_prefix(&node, key, depth),
                Self::get_prefix_len(&node)
            );
            return None;
        }
        // step
        let depth = depth + Self::get_prefix_len(&node) as usize;
        // check leaf for sub-string.
        // todo: can avoid double check? (checked above)
        if depth == key.len() {
            if Self::is_leaf_match(&node, key) {
                let leaf = Self::to_node4(&node).leaf.refer();
                debug_assert!(!leaf.is_null());
                return Some(leaf);
            } else {
                return None;
            }
        }
        let next = Self::find_child(&node, &key[depth])?;
        // another lazy expansion?
        if Node::is_kvpair(&next) {
            if Node::is_leaf_match(&next, key) {
                return Some(next.refer());
            }
            return None;
        }
        return Self::search(next, key, depth + 1);
    }

    // leaf pointer is tagged
    pub fn insert<'a>(
        node: &NodeRef,
        key: &[u8],
        leaf: *mut KVPair,
        depth: usize,
    ) -> Result<(), ()> {
        // what if key.len() = 0?

        if node.is_null() {
            let leaf = NodeRef::new(leaf as *mut usize);

            // Make a node4 and add `leaf` to it as one child. Then replace node by that new node4.
            let inner_node_ptr = Self::make_node4();
            let inner_node = NodeRef::new(inner_node_ptr as *mut usize);
            let header = Self::get_header_mut(inner_node_ptr as *mut usize);
            header.count = 1;
            // header.prefix.set_len(key.len() as u32 - 1);
            // header.prefix.set_prerix(key);
            header.prefix.set_values(&key[..key.len() - 1]);
            Self::add_child(&inner_node, *key.last().unwrap(), leaf, true);

            node.replace_with(inner_node);
            return Ok(());
        }
        unsafe {
            // reached a kvpair node. replace it by a inner node, move kvpair to `leaf` and add 1 child.
            // this happens when old key is substring of new key.
            if Self::is_kvpair(&node) {
                let new_inner_node_ptr = Self::make_node4() as *mut usize;
                // maybe no prefix? Todo: check this
                let new_inner_node = &mut *(new_inner_node_ptr as *mut Node4);
                new_inner_node.leaf.replace_with(node.refer());
                let new_inner_ref = NodeRef::new(new_inner_node_ptr);
                let (new_leaf_node, is_kvpair) = Self::make_new_leaf(key, leaf, depth + 1);
                Self::add_child(
                    &new_inner_ref,
                    key[depth],
                    NodeRef::new(new_leaf_node),
                    is_kvpair,
                );

                // swap
                node.replace_with(new_inner_ref);
                return Ok(());
            }
            // p is the length of matched prefix.
            let p = Self::check_prefix(&node, key, depth);
            if p != Self::get_prefix_len(&node) {
                // needs to expand collapsed prefix
                // todo-summary:
                // - check whether the sequence of insert and adjust prefix matter

                let inter_node = NodeRef::new(Node::make_node4() as _);
                let inter_header = Self::get_header_mut_by_noderef(&inter_node);
                let curr_header = Self::get_header_mut_by_noderef(node);
                // copy prefix,
                // for p > MAX_PREFIX_STORED, means new inter node's prefix needn't to change,
                // otherwise it is a subset of curr_prefix.
                let curr_prefix = &mut curr_header.prefix;
                // if p as usize > MAX_PREFIX_STORED {
                //     for i in 0..MAX_PREFIX_STORED {
                //         inter_header.prefix[i] = curr_prefix[i];
                //     }
                // } else {
                //     for i in 0..p as usize {
                //         inter_header.prefix[i] = curr_prefix[i];
                //     }
                // }
                // inter_header.prefix.set_len(p);
                // inter_header.prefix.set_prerix(curr_prefix.values());
                inter_header.prefix.set_values(curr_prefix.values());

                // adjust current node's prefix
                let new_curr_prefix_len = curr_prefix.len() - p - 1;
                let any_child = Node::any_child(&node).unwrap();
                let complete_key = &Node::to_kvpair(any_child).key;
                // for i in 0..new_curr_prefix_len.min(MAX_PREFIX_STORED as u32) as usize {
                // curr_prefix[i] = complete_key[p as usize + i + 1];
                // curr_prefix.set_len(new_curr_prefix_len);
                // curr_prefix.set_prerix(
                //     &complete_key[(p as usize + 1)..(p + new_curr_prefix_len) as usize],
                // );
                if new_curr_prefix_len > 0 {
                    curr_prefix.set_values(
                        &complete_key[(p as usize + 1)..(p + new_curr_prefix_len) as usize],
                    );
                }
                // }

                // link children, maybe need to find a way to insert first then adjust prefix?
                // if p equals to key.len(), the `leaf` is going to be a leaf in `node`
                let bias = if p as usize == key.len() { 1 } else { 0 };
                Self::add_child(
                    &inter_node,
                    complete_key[depth + p as usize],
                    node.refer(),
                    false,
                );
                if bias == 1 {
                    let leaf = NodeRef::new(leaf as *mut usize);
                    leaf.add_leaf_mark();
                    Node::to_node4(&inter_node).leaf.replace_with(leaf);
                } else {
                    let (new_leaf_node, is_kvpair) =
                        Self::make_new_leaf(key, leaf, depth + p as usize + 1);
                    Self::add_child(
                        &inter_node,
                        key[depth + p as usize],
                        NodeRef::new(new_leaf_node),
                        is_kvpair,
                    );
                }

                // replace
                node.replace_with(inter_node);
                return Ok(());
            }

            let depth = depth + p as usize;
            if depth == key.len() {
                // substring case
                let leaf = NodeRef::new(leaf as *mut usize);
                leaf.add_leaf_mark();
                let node = &*(**node as *mut _ as *mut Node4);
                node.leaf.replace_with(leaf);
                return Ok(());
            }
            if let Some(next_node) = Self::find_child(&node, &key[depth]) {
                Self::insert(&next_node, key, leaf, depth + 1)?;
            } else {
                if Self::is_overflow(&node) {
                    Self::grow(&node);
                }
                let (new_leaf_node, is_kvpair) = Self::make_new_leaf(key, leaf, depth + 1);
                Self::add_child(&node, key[depth], NodeRef::new(new_leaf_node), is_kvpair);
            }
            return Ok(());
        }
    }

    // pub fn remove<'a>(node: NodeRef, key: &[u8], depth: usize) -> Option<NodeRef> {
    //     if node.load(Relaxed).is_null() {
    //         return None;
    //     }
    //     if Self::is_kvpair(&node) {
    //         unreachable!("should not reach kvpair");
    //     }
    //     // need check `leaf` field
    //     if depth == key.len() {
    //         let leaf = &Self::to_node4(&node).leaf;
    //         if Self::is_leaf_match(leaf, key) {
    //             // let ret = leaf.swap(ptr::null::<*const usize>() as *mut usize);
    //             // let ret = leaf.evict();
    //             return Some(leaf.refer());
    //         } else {
    //             return None;
    //         }
    //     }

    //     if Self::check_prefix(&node, key, depth) != Self::get_prefix_len(&node) {
    //         return None;
    //     }
    //     let depth = depth + Self::get_prefix_len(&node) as usize;
    //     let next = Self::find_child(&node, &key[depth])?;
    //     if Node::is_kvpair(&next) {
    //         if Node::is_leaf_match(&next, key) {
    //             if Self::is_underflow(&node) {
    //                 Self::shrink(&node);
    //             }
    //             let removed = Self::remove_child(&node, key[depth]);
    //             if Self::is_kvpair(&NodeRef::new(removed as *mut usize)) {
    //                 // let raw_ptr = (removed as usize - 1) as *mut KVPair;
    //                 return Some(*removed);
    //             }
    //         }
    //         return None;
    //     }

    //     let ret = Self::remove(next, key, depth + 1);

    //     // downgrade empty inner node to its `leaf`
    //     if Self::get_header(&next).count == 0 {
    //         let leaf = &Self::to_node4(&node).leaf;
    //         next.store(leaf.load(Relaxed), Relaxed);
    //     }

    //     ret
    // }
}

impl Node {
    fn is_leaf_match(node: &NodeRef, key: &[u8]) -> bool {
        if Self::is_kvpair(node) {
            Self::to_kvpair(node).key.as_slice() == key
        } else {
            let leaf = &Self::to_node4(node).leaf;
            debug_assert!(Self::is_kvpair(leaf));
            if !(*leaf).is_null() {
                Self::to_kvpair(&leaf).key.as_slice() == key
            } else {
                false
            }
        }
    }

    // tagged pointer
    fn is_kvpair(node: &NodeRef) -> bool {
        (**node as usize) % 2 == 1
    }

    fn to_kvpair(node: &NodeRef) -> &KVPair {
        unsafe { &*((**node as usize - 1) as *mut KVPair) }
    }

    // All node struct is order-preserving #[repr(C)]. With Header in the first place
    // and Leaf pointer in the second. This method can only be used to access above two
    // fields when actual type is not specified.
    fn to_node4(node: &NodeRef) -> &Node4 {
        assert!(!Self::is_kvpair(node));
        unsafe { &*(**node as *mut Node4) }
    }

    // Return node.header.prefix_len if match, or 0 if not.
    fn check_prefix(node: &NodeRef, key: &[u8], depth: usize) -> PrefixCount {
        assert!(!Self::is_kvpair(node));

        let header = unsafe { &*(**node as *const Header) };
        let min_length = key.len().min(header.prefix.len() as usize);
        for i in 0..key.len().min(header.prefix.len() as usize)
        // .min(MAX_PREFIX_STORED)
        {
            if header.prefix.value(i + depth) != key[depth + i] {
                return i as u32;
            }
        }
        return min_length as u32;
    }

    fn get_prefix_len(node: &NodeRef) -> PrefixCount {
        assert!(!Self::is_kvpair(node));

        unsafe { (*(**node as *const Header)).prefix.len() }
    }

    fn find_child<'a>(node_ptr: &'a NodeRef, key_byte: &u8) -> Option<&'a NodeRef> {
        assert!(!Self::is_kvpair(node_ptr));

        unsafe {
            match Self::get_header(node_ptr).node_type {
                NodeType::Node4 => {
                    let node = **node_ptr as *const Node4;
                    (*node).find_child(key_byte)
                }
                NodeType::Node16 => {
                    let node = **node_ptr as *const Node16;
                    (*node).find_child(key_byte)
                }
                NodeType::Node48 => {
                    let node = **node_ptr as *const Node48;
                    (*node).find_child(key_byte)
                }
                NodeType::Node256 => {
                    let node = **node_ptr as *const Node256;
                    (*node).find_child(key_byte)
                }
            }
        }
    }

    fn get_header(node: &NodeRef) -> &Header {
        assert!(!Self::is_kvpair(node));

        unsafe { &*(**node as *const Header) }
    }

    fn get_header_mut<'a>(node: *mut usize) -> &'a mut Header {
        unsafe { &mut *(node as *mut Header) }
    }

    fn get_header_mut_by_noderef(node: &NodeRef) -> &mut Header {
        debug_assert!(!Self::is_kvpair(node));

        unsafe { &mut *(**node as *mut Header) }
    }

    // todo: SIMD
    fn add_child(node_ptr: &NodeRef, key_byte: u8, child: NodeRef, is_kvpair: bool) {
        assert!(!Self::is_kvpair(node_ptr));
        // let child = (child as usize + is_kvpair as usize) as *const usize;
        if is_kvpair {
            child.add_leaf_mark();
        }

        unsafe {
            match Self::get_header(node_ptr).node_type {
                NodeType::Node4 => {
                    let node = **node_ptr as *mut Node4;
                    (*node).add_child(key_byte, child)
                }
                NodeType::Node16 => {
                    let node = **node_ptr as *mut Node16;
                    (*node).add_child(key_byte, child)
                }
                NodeType::Node48 => {
                    let node = **node_ptr as *mut Node48;
                    (*node).add_child(key_byte, child)
                }
                NodeType::Node256 => {
                    let node = **node_ptr as *mut Node256;
                    (*node).add_child(key_byte, child)
                }
            }
        }
    }

    // fn remove_child(node_ptr: &NodeRef, key_byte: u8) -> *mut KVPair {
    //     assert!(!Self::is_kvpair(node_ptr));

    //     let ret = unsafe {
    //         match Self::get_header(node_ptr).node_type {
    //             NodeType::Node4 => {
    //                 let node = node_ptr.load(Relaxed) as *mut Node4;
    //                 (*node).remove_child(key_byte)
    //             }
    //             NodeType::Node16 => {
    //                 let node = node_ptr.load(Relaxed) as *mut Node16;
    //                 (*node).remove_child(key_byte)
    //             }
    //             NodeType::Node48 => {
    //                 let node = node_ptr.load(Relaxed) as *mut Node48;
    //                 (*node).remove_child(key_byte)
    //             }
    //             NodeType::Node256 => {
    //                 let node = node_ptr.load(Relaxed) as *mut Node256;
    //                 (*node).remove_child(key_byte)
    //             }
    //         }
    //     };

    //     ret as *mut KVPair
    // }

    // Check node is overflow or not.
    fn is_overflow(node: &NodeRef) -> bool {
        let header = Self::get_header(node);
        header.count
            > match header.node_type {
                NodeType::Node4 => 3,
                NodeType::Node16 => 15,
                NodeType::Node48 => 47,
                // Node256 won't overflow
                NodeType::Node256 => 255,
            }
    }

    fn is_underflow(node: &NodeRef) -> bool {
        let header = Self::get_header(node);
        header.count
            < match header.node_type {
                // Node4 won't underflow
                NodeType::Node4 => 0,
                NodeType::Node16 => 4,
                NodeType::Node48 => 16,
                NodeType::Node256 => 48,
            }
    }

    // create a new larger node, copy header, child (and key)
    // to it and atomic replace old node
    fn grow(node: &NodeRef) {
        let header = Self::get_header(node);
        let grown = match header.node_type {
            NodeType::Node4 => Node4::grow(&node),
            NodeType::Node16 => Node16::grow(&node),
            NodeType::Node48 => Node48::grow(&node),
            NodeType::Node256 => unreachable!("Node256 cannot grow"),
        };

        let grown_node = NodeRef::new(grown);
        node.replace_with(grown_node);
    }

    // retrive any child of given noexport RUSTFLAGS="-Zinstrument-coverage"de.
    // this is for getting a omitted prefix of a node.
    fn any_child(node: &NodeRef) -> Option<&NodeRef> {
        let mut curr = node;

        loop {
            if Self::is_kvpair(curr) {
                return Some(curr);
            }

            let header = Self::get_header(curr);

            unsafe {
                curr = match Self::get_header(curr).node_type {
                    NodeType::Node4 => {
                        let node = **curr as *const Node4;
                        (*node).any_child()?
                    }
                    NodeType::Node16 => {
                        let node = **curr as *const Node16;
                        (*node).any_child()?
                    }
                    NodeType::Node48 => {
                        let node = **curr as *const Node48;
                        (*node).any_child()?
                    }
                    NodeType::Node256 => {
                        let node = **curr as *const Node256;
                        (*node).any_child()?
                    }
                }
            }
        }
    }

    fn shrink(node: &NodeRef) {
        let header = Self::get_header(node);

        let shrunk = match header.node_type {
            NodeType::Node4 => unreachable!("Node4 cannot shrink"),
            NodeType::Node16 => Node16::shrink(&node),
            NodeType::Node48 => Node48::shrink(&node),
            NodeType::Node256 => Node256::shrink(&node),
        };

        node.replace_underlying(shrunk);
    }

    // make a new leaf node. if depth is equal to key length, return `leaf` in in_param,
    // with a boolean flag to identify it type is `KVPair`. otherwise create a inner node
    // and add `leaf` to its child field.
    //
    // todo: not directly +1 / -1
    fn make_new_leaf(key: &[u8], leaf: *mut KVPair, depth: usize) -> (*mut usize, bool) {
        // needn't to wrap a Node4
        if key.len() == depth {
            return (leaf as *mut usize, true);
        }

        println!("{}, {}", key.len(), depth);

        let leaf_node = NodeRef::new(leaf as _);
        NodeRef::add_leaf_mark(&leaf_node);
        let new_leaf = Self::make_node4();
        unsafe {
            let header = Self::get_header_mut(new_leaf as *mut usize);
            header.count = 1;
            // header.prefix_len = (key.len() - depth - 1) as u32;
            // for i in 0..header.prefix_len.min(MAX_PREFIX_STORED as u32) as usize {
            //     header.prefix[i] = key[i + depth];
            // }
            // header.prefix.set_len((key.len() - depth - 1) as u32);
            // header.prefix.set_prerix(&key[depth..]);
            header.prefix.set_values(&key[depth..]);
            (*new_leaf).key[0].store(key[depth + header.prefix.len() as usize], Relaxed);
            (*new_leaf).child[0].replace_with(leaf_node);
            (*new_leaf).mask.store(1, Relaxed);
            (*new_leaf).usued.store(1, Relaxed);
        }
        (new_leaf as *mut usize, false)
    }

    /// Dispatch memory reclain operation. `ptr` should be a boxed raw ptr.
    pub unsafe fn drop(ptr: *mut usize) {
        if ptr as usize % 2 != 0 {
            let ptr = (ptr as usize - 1) as *mut usize as *mut KVPair;
            drop(Box::from_raw(ptr));
        } else {
            match (*(ptr as *mut Node4)).header.node_type {
                NodeType::Node4 => drop(Box::from_raw(ptr as *mut Node4)),
                NodeType::Node16 => drop(Box::from_raw(ptr as *mut Node16)),
                NodeType::Node48 => drop(Box::from_raw(ptr as *mut Node48)),
                NodeType::Node256 => drop(Box::from_raw(ptr as *mut Node256)),
            };
        }
    }
}

// todo: remove this pub (and Node4's pub)
impl Node {
    pub fn make_node4() -> *mut Node4 {
        Box::into_raw(Box::new(Node4::new()))
    }
}

#[derive(Clone, PartialEq, Debug)]
pub enum NodeType {
    Node4,
    Node16,
    Node48,
    Node256,
}

#[derive(Debug, PartialEq)]
pub struct KVPair {
    pub key: Vec<u8>,
    pub value: Vec<u8>,
}

impl KVPair {
    pub fn new(key: Vec<u8>, value: Vec<u8>) -> Self {
        Self { key, value }
    }

    pub fn into_raw(self) -> *mut KVPair {
        Box::into_raw(Box::new(self))
    }
}

#[repr(C)]
#[derive(Debug)]
pub struct Node4 {
    header: Header,
    leaf: NodeRef,
    // mark keys exist or not in bits
    mask: AtomicU8,
    usued: AtomicU8,
    key: [AtomicU8; 4],
    child: [NodeRef; 4],
}

impl Node4 {
    pub fn new() -> Self {
        let (key, child) = {
            let mut key: [MaybeUninit<AtomicU8>; 4] =
                unsafe { MaybeUninit::uninit().assume_init() };
            let mut child: [MaybeUninit<NodeRef>; 4] =
                unsafe { MaybeUninit::uninit().assume_init() };

            for i in 0..4 {
                key[i] = MaybeUninit::new(AtomicU8::default());
                child[i] = MaybeUninit::new(NodeRef::default());
            }

            unsafe { (mem::transmute(key), mem::transmute(child)) }
        };

        Self {
            header: Header::new(NodeType::Node4),
            mask: AtomicU8::new(0),
            usued: AtomicU8::new(0),
            key,
            child,
            leaf: NodeRef::default(),
        }
    }

    pub fn find_child(&self, key: &u8) -> Option<&NodeRef> {
        // for i in 0..self.header.count as usize {
        let usued = self.usued.load(Relaxed);
        let mask = self.mask.load(Relaxed);
        for i in 0..usued as usize {
            if mask >> i & 1 == 1 && self.key[i].load(Relaxed) == *key {
                return Some(&self.child[i]);
            }
        }
        None
    }

    pub fn grow(node: &NodeRef) -> *mut usize {
        let new_node = Box::into_raw(Box::new(Node16::new()));
        let fulled_node = unsafe { &*(**node as *const Node4) };

        // copy header
        unsafe {
            (*new_node)
                .header
                .copy_from(fulled_node as *const Node4 as *mut usize);

            // key & child field
            let mask = fulled_node.mask.load(Relaxed);
            let mut cnt = 0;
            for i in 0..4 {
                if mask >> i & 1 == 1 {
                    (*new_node).key[cnt].store(fulled_node.key[i].load(Relaxed), Relaxed);
                    (*new_node).child[cnt].replace_with(fulled_node.child[i].refer());
                    cnt += 1;
                }
            }
            debug_assert_eq!(fulled_node.usued.load(Relaxed) as usize, cnt);
            (*new_node).usued.store(cnt as u8, Relaxed);
            (*new_node).mask.store((1 << cnt + 1) - 1, Relaxed);
        }

        new_node as *mut usize
    }

    pub fn any_child(&self) -> Option<&NodeRef> {
        if !self.leaf.is_null() {
            return Some(&self.leaf);
        }

        let usued = self.usued.load(Relaxed);
        let mask = self.mask.load(Relaxed);
        for i in 0..usued as usize {
            if mask >> i & 1 == 1 {
                return Some(&self.child[i]);
            }
        }

        None
    }

    pub fn add_child(&mut self, key: u8, child: NodeRef) {
        let usued = self.usued.load(Relaxed);
        self.key[usued as usize].store(key, Relaxed);
        self.child[usued as usize].replace_with(child);

        self.mask
            .store(self.mask.load(Relaxed) | 1 << usued, Relaxed);
        self.usued.fetch_add(1, Relaxed);
        self.header.count += 1;
    }

    // pub fn remove_child(&mut self, key: u8) -> *mut usize {
    //     self.header.count -= 1;
    //     let mask = self.mask.load(Relaxed);
    //     for i in 0..4 {
    //         if mask >> i & 1 == 1 && self.key[i].load(Relaxed) == key {
    //             self.mask.store(mask - (1 << i), Relaxed); // todo: fix this
    //             return self.child[i].swap(ptr::null::<usize>() as *mut usize, Relaxed);
    //         }
    //     }
    //     unreachable!("key must exist")
    // }
}

#[repr(C)]
#[derive(Debug)]
struct Node16 {
    header: Header,
    leaf: NodeRef,
    mask: AtomicU16,
    usued: AtomicU8,
    key: [AtomicU8; 16],
    child: [NodeRef; 16],
}

impl Node16 {
    pub fn new() -> Self {
        let (key, child) = {
            let mut key: [MaybeUninit<AtomicU8>; 16] =
                unsafe { MaybeUninit::uninit().assume_init() };
            let mut child: [MaybeUninit<NodeRef>; 16] =
                unsafe { MaybeUninit::uninit().assume_init() };

            for i in 0..16 {
                key[i] = MaybeUninit::new(AtomicU8::default());
                child[i] = MaybeUninit::new(NodeRef::default());
            }

            unsafe { (mem::transmute(key), mem::transmute(child)) }
        };

        Self {
            header: Header::new(NodeType::Node16),
            leaf: NodeRef::default(),
            mask: AtomicU16::new(0),
            usued: AtomicU8::new(0),
            key,
            child,
        }
    }

    pub fn find_child(&self, key: &u8) -> Option<&NodeRef> {
        // todo: use SIMD or binary search
        let usued = self.usued.load(Relaxed);
        let mask = self.mask.load(Relaxed);
        for i in 0..usued as usize {
            if mask >> i & 1 == 1 && self.key[i].load(Relaxed) == *key {
                return Some(&self.child[i]);
            }
        }
        None
    }

    pub fn grow(node: &NodeRef) -> *mut usize {
        let new_node = Box::into_raw(Box::new(Node48::new()));
        let fulled_node = unsafe { &*(**node as *const Node16) };

        // copy header
        unsafe {
            (*new_node)
                .header
                .copy_from(fulled_node as *const Node16 as *mut usize);

            // key & child field
            let mask = fulled_node.mask.load(Relaxed);
            let mut cnt = 0;
            for i in 0..16 {
                if mask >> i & 1 == 1 {
                    (*new_node).child[cnt].replace_with(fulled_node.child[i].refer());
                    (*new_node).key[fulled_node.key[cnt].load(Relaxed) as usize]
                        .store(i as i8, Relaxed);
                    cnt += 1;
                }
            }
            debug_assert_eq!(fulled_node.usued.load(Relaxed) as usize, cnt);
        }

        new_node as *mut usize
    }

    pub fn shrink(node: &NodeRef) -> *mut usize {
        let new_node = Box::into_raw(Box::new(Node4::new()));
        let empty_node = unsafe { &*(**node as *const Node16) };

        unsafe {
            (*new_node)
                .header
                .copy_from(empty_node as *const Node16 as *mut usize);

            let mut cnt = 0;
            for i in 0..16 {
                if !empty_node.child[i].load(Relaxed).is_null() {
                    (*new_node).key[cnt].store(empty_node.key[i].load(Relaxed), Relaxed);
                    (*new_node).child[cnt].replace_underlying(empty_node.child[i].load(Relaxed));
                    cnt += 1;
                }
            }
            (*new_node).usued.store(cnt as u8, Relaxed);
            (*new_node).mask.store((1 << cnt) - 1, Relaxed);
            assert!(cnt < 4);
        }

        new_node as *mut usize
    }

    pub fn any_child(&self) -> Option<&NodeRef> {
        if !self.leaf.is_null() {
            return Some(&self.leaf);
        }

        let usued = self.usued.load(Relaxed);
        let mask = self.mask.load(Relaxed);
        for i in 0..usued as usize {
            if mask >> i & 1 == 1 {
                return Some(&self.child[i]);
            }
        }

        None
    }

    pub fn add_child(&mut self, key: u8, child: NodeRef) {
        let usued = self.usued.load(Relaxed);
        let mask = self.mask.load(Relaxed);
        self.key[usued as usize].store(key, Relaxed);
        self.child[usued as usize].replace_with(child);

        self.mask.store(mask | 1 << usued, Relaxed);
        self.usued.fetch_add(1, Relaxed);
        self.header.count += 1;
    }

    // pub fn remove_child(&mut self, key: u8) -> *mut usize {
    //     self.header.count -= 1;
    //     let usued = self.usued.load(Relaxed);
    //     let mask = self.mask.load(Relaxed);

    //     for i in 0..usued as usize {
    //         if mask >> i & 1 == 1 && self.key[i].load(Relaxed) == key {
    //             // todo: fix this
    //             self.mask.store(mask - (1 << i), Relaxed);
    //             return self.child[i].swap(ptr::null_mut(), Relaxed);
    //         }
    //     }
    //     unreachable!("key must exist")
    // }
}

#[repr(C)]
#[derive(Debug)]
struct Node48 {
    header: Header,
    leaf: NodeRef,
    // Stores child index, negative means not exist
    key: [AtomicI8; 256],
    child: [NodeRef; 48],
}

impl Node48 {
    pub fn new() -> Self {
        let (key, child) = {
            let mut key: [MaybeUninit<AtomicI8>; 256] =
                unsafe { MaybeUninit::uninit().assume_init() };
            let mut child: [MaybeUninit<NodeRef>; 48] =
                unsafe { MaybeUninit::uninit().assume_init() };

            for i in 0..48 {
                key[i] = MaybeUninit::new(AtomicI8::new(-1));
                child[i] = MaybeUninit::new(NodeRef::default());
            }
            for i in 48..256 {
                key[i] = MaybeUninit::new(AtomicI8::new(-1));
            }

            unsafe { (mem::transmute(key), mem::transmute(child)) }
        };

        Self {
            header: Header::new(NodeType::Node48),
            key,
            child,
            leaf: NodeRef::default(),
        }
    }

    pub fn find_child(&self, key: &u8) -> Option<&NodeRef> {
        if self.key[*key as usize].load(Relaxed) >= 0 {
            return Some(&self.child[self.key[*key as usize].load(Relaxed) as usize]);
        }
        None
    }

    pub fn grow(node: &NodeRef) -> *mut usize {
        let new_node = Box::into_raw(Box::new(Node256::new()));
        // let fulled_node = unsafe { &*(node.load(Relaxed) as *const Node48) };
        let fulled_node = unsafe { &*(**node as *const Node48) };

        // copy header
        unsafe {
            (*new_node)
                .header
                .copy_from(fulled_node as *const Node48 as *mut usize);

            // child field
            for i in 0..=255 {
                if fulled_node.key[i].load(Relaxed) >= 0 {
                    (*new_node).child[i].replace_with(
                        fulled_node.child[fulled_node.key[i].load(Relaxed) as usize].refer(),
                    );
                }
            }
        }

        new_node as *mut usize
    }

    pub fn shrink(node: &NodeRef) -> *mut usize {
        let new_node = Box::into_raw(Box::new(Node16::new()));
        let empty_node = unsafe { &*(node.load(Relaxed) as *const Node48) };

        unsafe {
            (*new_node)
                .header
                .copy_from(empty_node as *const Node48 as *mut usize);

            let mut cnt = 0;
            for i in 0..256 {
                let pos = empty_node.key[i].load(Relaxed);
                if pos >= 0 {
                    (*new_node).key[cnt].store(i as u8, Relaxed);
                    (*new_node).child[cnt]
                        .replace_underlying(empty_node.child[pos as usize].load(Relaxed));
                    cnt += 1;
                }
            }
            (*new_node).usued.store(cnt as u8, Relaxed);
            (*new_node).mask.store((1 << cnt) - 1, Relaxed);
            assert!(cnt < 16);
            debug_assert_eq!(cnt, (*new_node).header.count as usize);
        }

        new_node as *mut usize
    }

    pub fn any_child(&self) -> Option<&NodeRef> {
        if !self.leaf.is_null() {
            return Some(&self.leaf);
        }

        for i in 0..48 {
            if !self.child[i].is_null() {
                return Some(&self.child[i]);
            }
        }

        None
    }

    pub fn add_child(&mut self, key: u8, child: NodeRef) {
        self.child[self.header.count as usize].replace_with(child);
        self.key[key as usize].store(self.header.count as i8, Relaxed);
        self.header.count += 1;
    }

    // pub fn remove_child(&mut self, key: u8) -> *mut usize {
    //     self.header.count -= 1;

    //     let pos = self.key[key as usize].swap(-1, Relaxed);
    //     self.child[pos as usize].swap(ptr::null_mut(), Relaxed)
    // }
}

#[repr(C)]
#[derive(Debug)]
struct Node256 {
    header: Header,
    leaf: NodeRef,
    child: [NodeRef; 256],
}

impl Node256 {
    pub fn new() -> Self {
        let child = {
            let mut child: [MaybeUninit<NodeRef>; 256] =
                unsafe { MaybeUninit::uninit().assume_init() };

            for i in 0..256 {
                child[i] = MaybeUninit::new(NodeRef::default());
            }

            unsafe { mem::transmute(child) }
        };

        Self {
            header: Header::new(NodeType::Node256),
            child,
            leaf: NodeRef::default(),
        }
    }

    pub fn find_child(&self, key: &u8) -> Option<&NodeRef> {
        if !self.child[*key as usize].load(Relaxed).is_null() {
            return Some(&self.child[*key as usize]);
        }
        None
    }

    pub fn shrink(node: &NodeRef) -> *mut usize {
        let new_node = Box::into_raw(Box::new(Node48::new()));
        let empty_node = unsafe { &*(node.load(Relaxed) as *const Node256) };

        unsafe {
            (*new_node)
                .header
                .copy_from(empty_node as *const Node256 as *mut usize);

            let mut cnt = 0;
            for i in 0..256 {
                if !empty_node.child[i].load(Relaxed).is_null() {
                    (*new_node).key[i].store(cnt as i8, Relaxed);
                    (*new_node).child[cnt].replace_underlying(empty_node.child[i].load(Relaxed));
                    cnt += 1;
                }
            }
            assert!(cnt < 48);
        }

        new_node as *mut usize
    }

    pub fn any_child(&self) -> Option<&NodeRef> {
        if !self.leaf.is_null() {
            return Some(&self.leaf);
        }

        for i in 0..256 {
            if !self.child[i].is_null() {
                return Some(&self.child[i]);
            }
        }

        None
    }

    pub fn add_child(&mut self, key: u8, child: NodeRef) {
        self.child[key as usize].replace_with(child);
        self.header.count += 1;
    }

    // pub fn remove_child(&mut self, key: u8) -> *mut usize {
    //     self.header.count -= 1;
    //     self.child[key as usize].swap(ptr::null_mut(), Relaxed)
    // }
}

#[derive(Clone, Debug)]
#[repr(C)]
struct Header {
    node_type: NodeType,
    // item count
    // todo: change `count` to u8
    count: u16,
    prefix: PrefixArray,
}

impl Header {
    pub fn new(node_type: NodeType) -> Self {
        Self {
            node_type,
            count: 0,
            prefix: PrefixArray::default(),
        }
    }

    pub fn copy_from(&mut self, src: *mut usize) {
        let src_header = unsafe { &(*(src as *mut Node4)).header };
        self.count = src_header.count;
        // self.prefix_len = src_header.prefix_len;
        // for i in 0..MAX_PREFIX_STORED.min(src_header.prefix_len as usize) {
        //     self.prefix[i] = src_header.prefix[i];
        // }
        self.prefix = PrefixArray::copy_from(&src_header.prefix);
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::collections::HashMap;

    // todo: consider what is the interface of tagging & untagging kvpair's ptr like
    unsafe fn from_tagged_ptr(node_ref: &NodeRef) -> *mut KVPair {
        let ptr = **node_ref;
        debug_assert!(ptr as usize % 2 == 1);
        (ptr as usize - 1) as *mut usize as _
    }

    #[test]
    fn bootstarp_from_empty() {
        let root = NodeRef::default();
        let kvpair_ptr = KVPair::new([1, 2, 3, 4].to_vec(), [1, 2, 3, 4].to_vec()).into_raw();
        Node::insert(&root, &[1, 2, 3, 4], kvpair_ptr, 0).unwrap();
        let result = Node::search(&root.refer(), &[1, 2, 3, 4], 0).unwrap();
        unsafe {
            assert_eq!(*from_tagged_ptr(&result), *kvpair_ptr);
        }
    }

    #[test]
    fn insert_two_item_in_one_level() {
        let root = NodeRef::default();
        let kvpair1 = KVPair::new([1, 2, 3, 4].to_vec(), [1, 2, 3, 4].to_vec()).into_raw();
        Node::insert(&root, &[1, 2, 3, 4], kvpair1, 0).unwrap();

        let kvpair2 = KVPair::new([1, 2, 3, 5].to_vec(), [1, 2, 3, 5].to_vec()).into_raw();
        Node::insert(&root, &[1, 2, 3, 5], kvpair2, 0).unwrap();

        let result1 = Node::search(&root.refer(), &[1, 2, 3, 4], 0).unwrap();
        let result2 = Node::search(&root.refer(), &[1, 2, 3, 5], 0).unwrap();

        unsafe {
            assert_eq!(*from_tagged_ptr(&result1), *kvpair1);
            assert_eq!(*from_tagged_ptr(&result2), *kvpair2);
        }
    }

    #[test]
    fn expand_collapsed_prefix_by_two_item() {
        let root = NodeRef::default();
        let kvs = vec![vec![1, 2, 3, 4], vec![1, 2, 1]];
        let mut answer = HashMap::new();
        for kv in &kvs {
            let kvpair_ptr = KVPair::new(kv.to_owned(), kv.to_owned()).into_raw();
            answer.insert(kv.to_owned(), kvpair_ptr);
            Node::insert(&root, &kv, kvpair_ptr, 0).unwrap();
        }

        // search
        for kv in &kvs {
            let result = Node::search(&root.refer(), kv, 0).unwrap();
            unsafe {
                assert_eq!(*from_tagged_ptr(&result), *answer.remove(kv).unwrap());
            }
        }
    }

    #[test]
    fn grow_from_4_to_256() {
        let root = NodeRef::default();

        let mut kvs = [[1, 1, 1, 1]; 255];
        for i in 0..255 {
            kvs[i][3] = i as u8;
        }

        // insert
        let mut answer = HashMap::new();
        for kv in &kvs {
            let kvpair_ptr = KVPair::new(kv.to_vec(), kv.to_vec()).into_raw();
            answer.insert(kv.to_owned(), kvpair_ptr);
            Node::insert(&root, kv, kvpair_ptr, 0).unwrap();
        }

        // search
        for kv in &kvs {
            let result = Node::search(&root.refer(), kv, 0).unwrap();
            unsafe {
                assert_eq!(*from_tagged_ptr(&result), **answer.get(kv).unwrap());
            }
        }

        //remove
        // for kv in &kvs {
        //     let result = Node::remove(&root, kv, 0).unwrap();
        //     let kvpair = unsafe { &*(result as *mut KVPair) };
        //     assert_eq!(kvpair.value.as_slice(), kv);
        //     unsafe {
        //         let _ = Box::from_raw(result);
        //     }
        // }
    }

    // original paper seems not considering substring.
    #[test]
    fn insert_two_substring_items() {
        // short first
        let root = NodeRef::default();
        let kvpair1 = KVPair::new([1, 2, 3, 4].to_vec(), [1, 2, 3, 4].to_vec()).into_raw();
        Node::insert(&root, &[1, 2, 3, 4], kvpair1, 0).unwrap();

        let kvpair2 = KVPair::new([1, 2, 3, 4, 5].to_vec(), [1, 2, 3, 4, 5].to_vec()).into_raw();
        Node::insert(&root, &[1, 2, 3, 4, 5], kvpair2, 0).unwrap();

        let result1 = Node::search(&root.refer(), &[1, 2, 3, 4], 0).unwrap();
        let result2 = Node::search(&root.refer(), &[1, 2, 3, 4, 5], 0).unwrap();

        unsafe {
            assert_eq!(*from_tagged_ptr(&result1), *kvpair1);
            assert_eq!(*from_tagged_ptr(&result2), *kvpair2);
        }
        drop(root);

        // long first
        let root = NodeRef::default();
        let kvpair1 = KVPair::new([1, 2, 3, 4, 5].to_vec(), [1, 2, 3, 4, 5].to_vec()).into_raw();
        Node::insert(&root, &[1, 2, 3, 4, 5], kvpair1, 0).unwrap();

        let kvpair2 = KVPair::new([1, 2, 3, 4].to_vec(), [1, 2, 3, 4].to_vec()).into_raw();
        Node::insert(&root, &[1, 2, 3, 4], kvpair2, 0).unwrap();

        let result1 = Node::search(&root.refer(), &[1, 2, 3, 4, 5], 0).unwrap();
        let result2 = Node::search(&root.refer(), &[1, 2, 3, 4], 0).unwrap();

        unsafe {
            assert_eq!(*from_tagged_ptr(&result1), *kvpair1);
            assert_eq!(*from_tagged_ptr(&result2), *kvpair2);
        }
    }

    #[test]
    fn many_substring() {
        let root = NodeRef::default();
        let test_size = 100;

        let mut kvs = Vec::with_capacity(test_size);
        let mut meta = vec![0u8];
        for i in 1..test_size {
            meta.push(i as u8);
            kvs.push(meta.to_owned());
        }

        // insert
        let mut answer = HashMap::new();
        for kv in &kvs {
            let kvpair_ptr = KVPair::new(kv.to_vec(), kv.to_vec()).into_raw();
            answer.insert(kv.to_owned(), kvpair_ptr);
            Node::insert(&root, kv, kvpair_ptr, 0).unwrap();
        }

        // search
        for kv in &kvs {
            let result = Node::search(&root.refer(), kv, 0).unwrap();
            unsafe {
                assert_eq!(*from_tagged_ptr(&result), **answer.get(kv).unwrap());
            }
        }

        // reverse dataset
        kvs.reverse();
        drop(root);
        let root = NodeRef::default();

        // insert
        let mut answer = HashMap::new();
        for kv in &kvs {
            let kvpair_ptr = KVPair::new(kv.to_vec(), kv.to_vec()).into_raw();
            answer.insert(kv.to_owned(), kvpair_ptr);
            Node::insert(&root, kv, kvpair_ptr, 0).unwrap();
        }

        // search
        for kv in &kvs {
            let result = Node::search(&root.refer(), kv, 0).unwrap();
            unsafe {
                assert_eq!(*from_tagged_ptr(&result), **answer.get(kv).unwrap());
            }
        }
    }

    #[test]
    fn expand_collapsed_node_with_other_unrelative_items() {
        let root = NodeRef::default();
        let kvs = vec![
            vec![1],
            vec![0, 0],
            vec![0, 0, 0, 0],
            vec![3, 3, 3, 3],
            vec![4, 4, 4, 4, 4],
        ];

        // insert
        let mut answer = HashMap::new();
        for k in &kvs {
            let kvpair_ptr = KVPair::new(k.to_vec(), k.to_vec()).into_raw();
            answer.insert(k.to_owned(), kvpair_ptr);
            Node::insert(&root, k, kvpair_ptr, 0).unwrap();
        }

        // search
        for k in &kvs {
            let result = Node::search(&root, k, 0).unwrap();
            unsafe {
                assert_eq!(*from_tagged_ptr(&result), **answer.get(k).unwrap());
            }
        }

        // remove
        // for kv in &kvs {
        //     let result = Node::remove(&root, kv, 0).unwrap();
        //     let kvpair = unsafe { &*(result as *mut KVPair) };
        //     assert_eq!(&kvpair.value, kv);
        //     unsafe {
        //         let _ = Box::from_raw(result);
        //     }
        // }
    }

    // reason: when writing/adjusting a new node's prefix, and may following a insert
    // (like make a inner node and add `leaf` to insert to its child). Prefix length
    // is not processed correctlly. Like considering bits used by prefix, or add depth
    // by one as the new node is belongs to next level.
    #[test]
    fn fuzz_case_1() {
        let keys = vec![
            vec![255, 10, 255, 255, 255, 255, 7, 7, 7],
            vec![255, 255, 255, 7],
        ];
        let root = NodeRef::default();
        let mut answer = HashMap::new();

        for key in &keys {
            let kvpair_ptr = KVPair::new(key.to_vec(), key.to_vec()).into_raw();
            answer.insert(key.to_owned(), kvpair_ptr);
            Node::insert(&root, &key, kvpair_ptr, 0).unwrap();
        }

        for key in keys {
            let result = Node::search(&root.refer(), &key, 0).unwrap();
            unsafe {
                assert_eq!(*from_tagged_ptr(&result), **answer.get(&key).unwrap());
            }
        }
    }

    // reason: `MAX_PREFIX_STORED` has not been took into consideration at `make_new_leaf()`
    #[test]
    fn fuzz_case_2() {
        let keys = vec![
            vec![255, 0, 255],
            vec![
                255, 255, 7, 10, 10, 96, 10, 10, 10, 0, 10, 0, 0, 96, 10, 10, 10, 10, 10, 10, 7,
                255, 255, 10, 255, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            ],
        ];
        let root = NodeRef::default();
        let mut answer = HashMap::new();

        for key in &keys {
            let kvpair_ptr = KVPair::new(key.to_vec(), key.to_vec()).into_raw();
            answer.insert(key.to_owned(), kvpair_ptr);
            Node::insert(&root, &key, kvpair_ptr, 0).unwrap();
        }

        for key in keys {
            let result = Node::search(&root.refer(), &key, 0).unwrap();
            unsafe {
                assert_eq!(*from_tagged_ptr(&result), **answer.get(&key).unwrap());
            }
        }
    }

    // reason: a mistake `minus 1` over `MAX_PREFIX_STORED`. That is added when handling previous
    // test and seems not correct.
    #[test]
    fn fuzz_case_3() {
        let keys = vec![
            // `255` * 10 + `7` * 2
            vec![255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 7, 7],
            vec![120],
        ];
        let root = NodeRef::default();
        let mut answer = HashMap::new();

        for key in &keys {
            let kvpair_ptr = KVPair::new(key.to_vec(), key.to_vec()).into_raw();
            answer.insert(key.to_owned(), kvpair_ptr);
            Node::insert(&root, &key, kvpair_ptr, 0).unwrap();
        }

        for key in keys {
            let result = Node::search(&root.refer(), &key, 0).unwrap();
            unsafe {
                assert_eq!(*from_tagged_ptr(&result), **answer.get(&key).unwrap());
            }
        }
    }

    // reason: forget to call `make_new_leaf()` when making a leaf node.
    #[test]
    fn fuzz_case_4() {
        let keys = vec![
            vec![255],
            vec![
                255, 255, 255, 255, 255, 255, 7, 7, 7, 7, 7, 7, 7, 160, 255, 11, 136, 135, 135, 3,
                255, 255, 120, 10, 10, 10, 255, 10, 10, 0, 0, 7, 255, 0,
            ],
        ];
        let root = NodeRef::default();
        let mut answer = HashMap::new();

        for key in &keys {
            let kvpair_ptr = KVPair::new(key.to_vec(), key.to_vec()).into_raw();
            answer.insert(key.to_owned(), kvpair_ptr);
            Node::insert(&root, &key, kvpair_ptr, 0).unwrap();
        }

        for key in keys {
            let result = Node::search(&root.refer(), &key, 0).unwrap();
            unsafe {
                assert_eq!(*from_tagged_ptr(&result), **answer.get(&key).unwrap());
            }
        }
    }

    #[ignore]
    #[test]
    fn fuzz_case_5() {
        // commom prefix: `255` * 13
        let keys = vec![
            vec![
                255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 7, 7, 7, 7, 7, 255,
            ],
            vec![
                255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 11, 120, 120,
                120, 255,
            ],
        ];
        let root = NodeRef::default();
        let mut answer = HashMap::new();

        for key in &keys {
            println!("insert: {:?}", key);
            let kvpair_ptr = KVPair::new(key.to_vec(), key.to_vec()).into_raw();
            answer.insert(key.to_owned(), kvpair_ptr);
            Node::insert(&root, &key, kvpair_ptr, 0).unwrap();
        }

        for key in keys {
            println!("search: {:?}", key);
            let result = Node::search(&root.refer(), &key, 0).unwrap();
            unsafe {
                assert_eq!(*from_tagged_ptr(&result), **answer.get(&key).unwrap());
            }
        }
    }
}
