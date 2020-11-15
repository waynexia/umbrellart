#[allow(unused_variables)]
#[allow(dead_code)]
#[allow(unused_imports)]
use std::fmt::Debug;
use std::mem::{self, MaybeUninit};
use std::sync::atomic::Ordering::Relaxed;
use std::sync::atomic::{AtomicI8, AtomicU16, AtomicU8};

use crate::node_ref::NodeRef;

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

            // Make a node4 and add `leaf` to it. Then replace node by that new node4.
            let inner_node_ptr = Self::make_node4();
            let inner_node = NodeRef::new(inner_node_ptr as *mut usize);
            let header = Self::get_header_mut(inner_node_ptr as *mut usize);
            header.count = 1;
            header.prefix_len = key.len() as u32 - 1;
            for i in 0..MAX_PREFIX_STORED.min(key.len() - 1) {
                header.prefix[i] = key[i];
            }
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
                let leaf = NodeRef::new(leaf as *mut usize);
                Self::add_child(&new_inner_ref, *key.last().unwrap(), leaf, true);
                // swap
                // node.replace_underlying(new_inner_node_ptr);
                node.replace_with(new_inner_ref);
                return Ok(());
            }
            let p = Self::check_prefix(&node, key, depth);
            if p != Self::get_prefix_len(&node) {
                // needs to expand collapsed prefix
                // todo-summary:
                // - check interaction with MAX_PREFIX_STORED
                // - check whether the sequence of insert and adjust prefix matter
                // - maybe need to retrieve entire key when adjusting curr_prefix ?
                let p = p as usize;
                let inter_node = NodeRef::new(Node::make_node4() as _);
                let mut inter_header = Self::get_header_mut_by_noderef(&inter_node);
                let mut curr_header = Self::get_header_mut_by_noderef(node);
                let curr_prefix = curr_header.prefix;
                // todo: should branch for p greater/smaller than MAX_PREFIX_STORED ?
                // copy prefix
                for i in 0..p {
                    inter_header.prefix[i] = curr_prefix[i];
                }
                inter_header.prefix_len = p as u32;

                // adjust current node's prefix
                // todo: consider MAX_PREFIX_STORED
                for i in p..curr_header.prefix_len as usize {
                    curr_header.prefix[i - p] = curr_header.prefix[p];
                }
                curr_header.prefix_len -= p as u32 + 1;

                // link children, maybe need to find a way to insert first then adjust prefix?
                let leaf = NodeRef::new(leaf as *mut usize);
                Self::add_child(&inter_node, curr_prefix[depth + p], node.refer(), false);
                Self::add_child(&inter_node, key[depth + p], leaf, true);

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
        **node as usize % 2 == 1
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
        for i in 0..key
            .len()
            .min(header.prefix_len as usize)
            .min(MAX_PREFIX_STORED)
        {
            if header.prefix[i] != key[depth + i] {
                return i as u32;
            }
        }
        return header.prefix_len;
    }

    fn get_prefix_len(node: &NodeRef) -> PrefixCount {
        assert!(!Self::is_kvpair(node));

        unsafe { (*(**node as *const Header)).prefix_len }
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

        node.replace_underlying(grown);
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

        let new_leaf = Self::make_node4();
        unsafe {
            let header = Self::get_header_mut(new_leaf as *mut usize);
            header.count = 1;
            header.prefix_len = (key.len() - depth - 1) as u32;
            for i in 0..header.prefix_len as usize {
                header.prefix[i] = key[i + depth];
            }
            (*new_leaf).key[0].store(key[depth], Relaxed);
            (*new_leaf).child[0].replace_underlying((leaf as usize + 1) as *mut usize);
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
                    (*new_node).child[cnt].replace_underlying(*fulled_node.child[i]);
                    cnt += 1;
                }
            }
            debug_assert_eq!(fulled_node.usued.load(Relaxed) as usize, cnt);
            (*new_node).usued.store(cnt as u8, Relaxed);
            (*new_node).mask.store((1 << cnt + 1) - 1, Relaxed);
        }

        new_node as *mut usize
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
                    (*new_node).child[cnt].replace_underlying(*fulled_node.child[i]);
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
        let fulled_node = unsafe { &*(node.load(Relaxed) as *const Node48) };

        // copy header
        unsafe {
            (*new_node)
                .header
                .copy_from(fulled_node as *const Node48 as *mut usize);

            // child field
            for i in 0..=255 {
                if fulled_node.key[i].load(Relaxed) >= 0 {
                    (*new_node).child[i].replace_underlying(
                        fulled_node.child[fulled_node.key[i].load(Relaxed) as usize].load(Relaxed),
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
    prefix_len: PrefixCount,
    prefix: [u8; MAX_PREFIX_STORED],
}

impl Header {
    pub fn new(node_type: NodeType) -> Self {
        Self {
            node_type,
            count: 0,
            prefix_len: 0,
            prefix: [0; 10],
        }
    }

    pub fn copy_from(&mut self, src: *mut usize) {
        let src_header = unsafe { &(*(src as *mut Node4)).header };
        self.count = src_header.count;
        self.prefix_len = src_header.prefix_len;
        for i in 0..MAX_PREFIX_STORED.min(src_header.prefix_len as usize) {
            self.prefix[i] = src_header.prefix[i];
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::collections::HashMap;
    use std::sync::atomic::AtomicPtr;

    fn empty_node4() -> *mut Node4 {
        Node::make_node4()
    }

    fn debug_print(node_ptr: *mut usize) {
        unsafe {
            match (node_ptr as *mut Header).as_ref().unwrap().node_type {
                NodeType::Node4 => {
                    let node = (node_ptr as *mut Node4).as_ref().unwrap();
                    debug!("Node4: {:?}", node);
                }
                NodeType::Node16 => {
                    let node = (node_ptr as *mut Node16).as_ref().unwrap();
                    debug!("Node4: {:?}", node);
                }
                NodeType::Node48 => {
                    let node = (node_ptr as *mut Node48).as_ref().unwrap();
                    debug!("Node4: {:?}", node);
                }
                NodeType::Node256 => {
                    let node = (node_ptr as *mut Node256).as_ref().unwrap();
                    debug!("Node4: {:?}", node);
                }
            }
        }
    }

    fn debug_print_atomic(node: &AtomicPtr<usize>) {
        debug_print(node.load(Relaxed));
    }

    // todo: what is the interface of tagging & untagging kvpair's ptr like
    unsafe fn from_tagged_ptr(node_ref: &NodeRef) -> *mut KVPair {
        let ptr = **node_ref;
        debug_assert!(ptr as usize % 2 == 1);
        (ptr as usize - 1) as *mut usize as _
    }

    #[test]
    fn test_node_insert_from_empty() {
        let root = NodeRef::default();
        let kvpair_ptr = KVPair::new([1, 2, 3, 4].to_vec(), [1, 2, 3, 4].to_vec()).into_raw();
        Node::insert(&root, &[1, 2, 3, 4], kvpair_ptr, 0).unwrap();
        let result = Node::search(&root.refer(), &[1, 2, 3, 4], 0).unwrap();
        unsafe {
            assert_eq!(*from_tagged_ptr(&result), *kvpair_ptr);
        }
    }

    #[test]
    fn test_node_simple_insert_two() {
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
    fn test_node_expand_collapsed_prefix() {
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

    // #[test]
    // fn test_node_grow() {
    //     let root = AtomicPtr::new(empty_node4() as *mut usize);
    //     Node::init(&root, &[1, 1, 1, 0], &[1, 1, 1, 0]);

    //     let mut kvs = [[1, 1, 1, 1]; 255];
    //     for i in 1..=255 {
    //         kvs[i - 1][3] = i as u8;
    //     }

    //     // insert
    //     let mut answer = HashMap::new();
    //     for kv in &kvs {
    //         debug_print_atomic(&root);
    //         // let kvpair = KVPair::new(kv.to_vec(), kv.to_vec());
    //         // let kvpair_ptr = Box::into_raw(Box::new(kvpair));
    //         let kvpair_ptr = KVPair::new(kv.to_vec(), kv.to_vec()).into_raw();
    //         answer.insert(kv.to_owned(), kvpair_ptr as *mut usize);
    //         Node::insert(&root, kv, kvpair_ptr, 0).unwrap();
    //     }

    //     // search
    //     for kv in &kvs {
    //         let result = Node::search(&root, kv, 0);
    //         assert_eq!(result.unwrap(), *answer.get(kv).unwrap());
    //     }

    //     //remove
    //     for kv in &kvs {
    //         let result = Node::remove(&root, kv, 0).unwrap();
    //         let kvpair = unsafe { &*(result as *mut KVPair) };
    //         assert_eq!(kvpair.value.as_slice(), kv);
    //         unsafe {
    //             let _ = Box::from_raw(result);
    //         }
    //     }
    // }

    // original paper seems not considering substring.
    #[test]
    fn test_node_substring_no_grow() {
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

    // #[test]
    // fn test_node_substring() {
    //     let root = AtomicPtr::new(empty_node4() as *mut usize);
    //     Node::init(&root, &[0], &[0]);
    //     let test_size = 100;

    //     let mut kvs = Vec::with_capacity(test_size);
    //     let mut meta = vec![0u8];
    //     for i in 1..test_size {
    //         meta.push(i as u8);
    //         kvs.push(meta.to_owned());
    //     }

    //     // insert
    //     let mut answer = HashMap::new();
    //     for kv in &kvs {
    //         debug_print_atomic(&root);
    //         // let kvpair = KVPair::new(kv.to_vec(), kv.to_vec());
    //         // let kvpair_ptr = Box::into_raw(Box::new(kvpair));
    //         let kvpair_ptr = KVPair::new(kv.to_vec(), kv.to_vec()).into_raw();
    //         answer.insert(kv.to_owned(), kvpair_ptr as *mut usize);
    //         Node::insert(&root, kv, kvpair_ptr, 0).unwrap();
    //     }

    //     // search
    //     for kv in &kvs {
    //         let result = Node::search(&root, kv, 0);
    //         assert_eq!(result.unwrap(), *answer.get(kv).unwrap());
    //     }

    //     // remove
    //     for kv in &kvs {
    //         let result = Node::remove(&root, kv, 0).unwrap();
    //         let kvpair = unsafe { &*(result as *mut KVPair) };
    //         assert_eq!(&kvpair.value, kv);
    //         unsafe {
    //             let _ = Box::from_raw(result);
    //         }
    //     }
    // }

    // #[test]
    // fn test_node_collapse() {
    //     let root = AtomicPtr::new(empty_node4() as *mut usize);
    //     Node::init(&root, &[1], &[0]);

    //     let kvs = vec![
    //         vec![0, 0],
    //         vec![0, 0, 0, 0],
    //         vec![3, 3, 3, 3],
    //         vec![4, 4, 4, 4, 4],
    //     ];

    //     let mut answer = HashMap::new();
    //     for k in &kvs {
    //         // let kvpair = KVPair::new(k.to_vec(), k.to_vec());
    //         // let kvpair_ptr = Box::into_raw(Box::new(kvpair));
    //         let kvpair_ptr = KVPair::new(k.to_vec(), k.to_vec()).into_raw();
    //         answer.insert(k.to_owned(), kvpair_ptr as *mut usize);
    //         Node::insert(&root, k, kvpair_ptr, 0).unwrap();
    //     }

    //     for k in &kvs {
    //         let result = Node::search(&root, k, 0);
    //         assert_eq!(result.unwrap(), *answer.get(k).unwrap());
    //     }

    //     // remove
    //     for kv in &kvs {
    //         let result = Node::remove(&root, kv, 0).unwrap();
    //         let kvpair = unsafe { &*(result as *mut KVPair) };
    //         assert_eq!(&kvpair.value, kv);
    //         unsafe {
    //             let _ = Box::from_raw(result);
    //         }
    //     }
    // }
}
