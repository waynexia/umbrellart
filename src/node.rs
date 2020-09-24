use std::alloc::{dealloc, Layout};
#[allow(unused_variables)]
use std::fmt::Debug;
use std::mem::{self, MaybeUninit};
use std::ptr;
use std::sync::atomic::Ordering::Relaxed;
use std::sync::atomic::{AtomicI8, AtomicPtr, AtomicU16, AtomicU8, AtomicUsize};
use std::sync::Arc;

use log::{debug, info};

type PrefixCount = u32;
const MAX_PREFIX_STORED: usize = 10;

pub struct Node {}

impl Node {
    pub fn init(node: &NodePtr, key: &[u8], value: &[u8]) {
        let mut header = Self::get_header_mut(node.load());
        assert!(header.count == 0);
        header.prefix_len = key.len() as u32 - 1;
        for i in 0..(header.prefix_len as usize).min(MAX_PREFIX_STORED) {
            header.prefix[i] = key[i];
        }
        let kvpair = KVPair::new(key.to_owned(), value.to_owned());
        // let kvpair_ptr = Box::into_raw(Box::new(kvpair)) as usize + 1;
        let kvpair_ptr = Box::into_raw(Box::new(kvpair));
        Self::add_child(node, key[key.len() - 1], kvpair_ptr as *mut usize, true);
    }

    pub fn search<'a>(node: &'a NodePtr, key: &[u8], depth: usize) -> Option<*mut usize> {
        if node.load().is_null() {
            info!("search encounted a null ptr");
            return None;
        }
        // lazy expansion
        // run out of key bytes, should reach leaf node
        if depth == key.len() {
            if Self::is_leaf_match(node, key) {
                if Self::is_kvpair(node) {
                    return Some(node.load());
                } else {
                    let leaf = Self::to_node4(node).leaf.load();
                    return if !leaf.is_null() {
                        Some((leaf as usize - 1) as *mut usize)
                    } else {
                        // assert leaf exist?
                        None
                    };
                }
            }
            return None;
        }
        // check compressed path pessimistically
        if Self::check_prefix(node, key, depth) != Self::get_prefix_len(node) {
            debug!(
                "prefix not match, {} != {}",
                Self::check_prefix(node, key, depth),
                Self::get_prefix_len(node)
            );
            return None;
        }
        // step
        let depth = depth + Self::get_prefix_len(node) as usize;
        let next = Self::find_child(node, &key[depth])?;
        let _next_ref = next.refer();
        // another lazy expansion?
        if Node::is_kvpair(next) {
            if Node::is_leaf_match(next, key) {
                return Some((next.load() as usize - 1) as *mut usize);
            }
            return None;
        }
        return Self::search(next, key, depth + 1);
    }

    // leaf pointer is tagged
    pub fn insert<'a>(
        node: &'a NodePtr,
        key: &[u8],
        leaf: *mut KVPair,
        depth: usize,
    ) -> Result<(), ()> {
        if node.load().is_null() {
            node.store(leaf as *mut usize);
            return Ok(());
        }
        unsafe {
            // reached a kvpair node. replace it by a inner node, move kvpair to `leaf` and add 1 child.
            // this happens when old key is substring of new key.
            if Self::is_kvpair(node) {
                let new_inner_node_ptr = Self::make_node4() as *mut usize;
                // maybe no prefix? Todo: check this
                let new_inner_node = &mut *(new_inner_node_ptr as *mut Node4);
                new_inner_node.leaf.store(node.load());
                let tmp_atomic = NodePtr::new(new_inner_node_ptr); // todo: remove this
                Self::add_child(&tmp_atomic, *key.last().unwrap(), leaf as *mut usize, true);
                // swap
                node.store(new_inner_node_ptr);
                return Ok(());
            }
            let p = Self::check_prefix(node, key, depth);
            // todo: remove hard coded "Node4"
            if p != Self::get_prefix_len(node) {
                // make a copy of node and modify it,
                // construct new inner node and replace node
                let mut node_substitute: Node4 =
                    mem::transmute_copy(&*(node.load() as *const Node4)); // ?
                node_substitute.header.prefix_len = p;
                let node_substitute_ptr = Box::into_raw(Box::new(node_substitute));

                let new_inner_node = NodePtr::new(Self::make_node4() as *mut usize);
                let node_prefix = Self::get_header(node).prefix;
                let header = Self::get_header_mut(new_inner_node.load());
                header.prefix_len = p;
                Self::get_header_mut(new_inner_node.load() as *mut usize).prefix_len = p;
                for i in 0..MAX_PREFIX_STORED.min(p as usize) {
                    header.prefix[i] = node_prefix[i];
                }

                Self::add_child(
                    &new_inner_node,
                    key[depth + p as usize],
                    leaf as *const usize,
                    true,
                );
                Self::add_child(
                    &new_inner_node,
                    node_prefix[p as usize],
                    node_substitute_ptr as *mut usize,
                    false,
                );

                node.store(new_inner_node.load() as *mut usize);
                new_inner_node.increase_counter();
                // todo: drop old ptr, maybe call `obsolate` here?
                return Ok(());
            }

            let depth = depth + Self::get_prefix_len(node) as usize;
            if let Some(next_node) = Self::find_child(node, &key[depth]) {
                Self::insert(next_node, key, leaf, depth + 1)?;
            } else {
                if Self::is_overflow(node) {
                    Self::grow(&node);
                }
                let (new_leaf_node, is_kvpair) = Self::make_new_leaf(key, leaf, depth + 1);
                Self::add_child(node, key[depth], new_leaf_node, is_kvpair);
            }
            return Ok(());
        }
    }

    pub fn remove<'a>(node: &'a NodePtr, key: &[u8], depth: usize) -> Option<*mut usize> {
        if node.load().is_null() {
            return None;
        }
        if Self::is_kvpair(node) {
            unreachable!("will not reach kvpair");
        }
        // need check `leaf` field
        if depth == key.len() {
            let leaf = &Self::to_node4(node).leaf;
            if Self::is_leaf_match(leaf, key) {
                let ret = leaf.swap(ptr::null::<*const usize>() as *mut usize);
                return Some((ret as usize - 1) as *mut usize);
            } else {
                return None;
            }
        }

        if Self::check_prefix(node, key, depth) != Self::get_prefix_len(node) {
            return None;
        }
        let depth = depth + Self::get_prefix_len(node) as usize;
        let next = Self::find_child(node, &key[depth])?;
        if Node::is_kvpair(next) {
            if Node::is_leaf_match(next, key) {
                if Self::is_underflow(node) {
                    Self::shrink(node);
                }
                let removed = Self::remove_child(node, key[depth]);
                if Self::is_kvpair(&NodePtr::new(removed as *mut usize)) {
                    let raw_ptr = (removed as usize - 1) as *mut KVPair;
                    return Some(raw_ptr as *mut usize);
                }
            }
            return None;
        }

        let ret = Self::remove(next, key, depth + 1);

        // downgrade empty inner node to its `leaf`
        if Self::get_header(next).count == 0 {
            let leaf = &Self::to_node4(node).leaf;
            next.store(leaf.load());
        }

        ret
    }
}

impl Node {
    fn is_leaf_match(node: &NodePtr, key: &[u8]) -> bool {
        if Self::is_kvpair(node) {
            Self::to_kvpair(node).key.as_slice() == key
        } else {
            let leaf = &Self::to_node4(node).leaf;
            if !leaf.load().is_null() {
                Self::to_kvpair(&leaf).key.as_slice() == key
            } else {
                // assert leaf exist?
                false
            }
        }
    }

    // tagged pointer
    fn is_kvpair(node: &NodePtr) -> bool {
        node.load() as usize % 2 == 1
    }

    fn to_kvpair(node: &NodePtr) -> &KVPair {
        unsafe { &*((node.load() as usize - 1) as *mut KVPair) }
    }

    // All node struct is order-preserving #[repr(C)]. With Header in the first place
    // and Leaf pointer in the second. This method can only be used to access above two
    // fields when actual type is not specified.
    fn to_node4(node: &NodePtr) -> &Node4 {
        assert!(!Self::is_kvpair(node));
        unsafe { &*(node.load() as *mut Node4) }
    }

    // Return node.header.prefix_len if match, or 0 if not.
    fn check_prefix(node: &NodePtr, key: &[u8], depth: usize) -> PrefixCount {
        assert!(!Self::is_kvpair(node));

        let header = unsafe { &*(node.load() as *const Header) };
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

    fn get_prefix_len(node: &NodePtr) -> PrefixCount {
        assert!(!Self::is_kvpair(node));

        unsafe { (*(node.load() as *const Header)).prefix_len }
    }

    fn find_child<'a>(node_ptr: &'a NodePtr, key_byte: &u8) -> Option<&'a NodePtr> {
        assert!(!Self::is_kvpair(node_ptr));

        unsafe {
            match Self::get_header(node_ptr).node_type {
                NodeType::Node4 => {
                    let node = node_ptr.load() as *const Node4;
                    (*node).find_child(key_byte)
                }
                NodeType::Node16 => {
                    let node = node_ptr.load() as *const Node16;
                    (*node).find_child(key_byte)
                }
                NodeType::Node48 => {
                    let node = node_ptr.load() as *const Node48;
                    (*node).find_child(key_byte)
                }
                NodeType::Node256 => {
                    let node = node_ptr.load() as *const Node256;
                    (*node).find_child(key_byte)
                }
                NodeType::KVPair => unreachable!(),
            }
        }
    }

    fn get_header(node: &NodePtr) -> &Header {
        assert!(!Self::is_kvpair(node));

        unsafe { &*(node.load() as *const Header) }
    }

    fn get_header_mut<'a>(node: *mut usize) -> &'a mut Header {
        unsafe { &mut *(node as *mut Header) }
    }

    // todo: SIMD
    fn add_child(node_ptr: &NodePtr, key_byte: u8, child: *const usize, is_kvpair: bool) {
        assert!(!Self::is_kvpair(node_ptr));
        let child = (child as usize + is_kvpair as usize) as *const usize;

        unsafe {
            match Self::get_header(node_ptr).node_type {
                NodeType::Node4 => {
                    let node = node_ptr.load() as *mut Node4;
                    (*node).add_child(key_byte, child)
                }
                NodeType::Node16 => {
                    let node = node_ptr.load() as *mut Node16;
                    (*node).add_child(key_byte, child)
                }
                NodeType::Node48 => {
                    let node = node_ptr.load() as *mut Node48;
                    (*node).add_child(key_byte, child)
                }
                NodeType::Node256 => {
                    let node = node_ptr.load() as *mut Node256;
                    (*node).add_child(key_byte, child)
                }
                NodeType::KVPair => unreachable!(),
            }
        }
    }

    fn remove_child(node_ptr: &NodePtr, key_byte: u8) -> *mut KVPair {
        assert!(!Self::is_kvpair(node_ptr));

        let ret = unsafe {
            match Self::get_header(node_ptr).node_type {
                NodeType::Node4 => {
                    let node = node_ptr.load() as *mut Node4;
                    (*node).remove_child(key_byte)
                }
                NodeType::Node16 => {
                    let node = node_ptr.load() as *mut Node16;
                    (*node).remove_child(key_byte)
                }
                NodeType::Node48 => {
                    let node = node_ptr.load() as *mut Node48;
                    (*node).remove_child(key_byte)
                }
                NodeType::Node256 => {
                    let node = node_ptr.load() as *mut Node256;
                    (*node).remove_child(key_byte)
                }
                NodeType::KVPair => unreachable!(),
            }
        };

        ret as *mut KVPair
    }

    // Check node is overflow or not.
    fn is_overflow(node: &NodePtr) -> bool {
        let header = Self::get_header(node);
        header.count
            > match header.node_type {
                NodeType::Node4 => 3,
                NodeType::Node16 => 15,
                NodeType::Node48 => 47,
                // Node256 won't overflow
                NodeType::Node256 => 255,
                NodeType::KVPair => unreachable!(),
            }
    }

    fn is_underflow(node: &NodePtr) -> bool {
        let header = Self::get_header(node);
        header.count
            < match header.node_type {
                // Node4 won't underflow
                NodeType::Node4 => 0,
                NodeType::Node16 => 4,
                NodeType::Node48 => 16,
                NodeType::Node256 => 48,
                NodeType::KVPair => unreachable!(),
            }
    }

    // create a new larger node, copy header, child (and key)
    // to it and atomic replace old node
    fn grow(node: &NodePtr) {
        let header = Self::get_header(node);
        let grown = match header.node_type {
            NodeType::Node4 => Node4::grow(&node),
            NodeType::Node16 => Node16::grow(&node),
            NodeType::Node48 => Node48::grow(&node),
            NodeType::Node256 => unreachable!("Node256 cannot grow"),
            NodeType::KVPair => unreachable!(),
        };

        node.store(grown);
    }

    fn shrink(node: &NodePtr) {
        let header = Self::get_header(node);

        let shrunk = match header.node_type {
            NodeType::Node4 => unreachable!("Node4 cannot shrink"),
            NodeType::Node16 => Node16::shrink(&node),
            NodeType::Node48 => Node48::shrink(&node),
            NodeType::Node256 => Node256::shrink(&node),
            NodeType::KVPair => unreachable!(),
        };

        node.store(shrunk);
    }

    // make a new leaf node. if depth is equal to key length, return `leaf` in in_param,
    // with a boolean flag to identify it type is `KVPair`. otherwise create a inner node
    // and add `leaf` to its child field.
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
            (*new_leaf).child[0].store((leaf as usize + 1) as *mut usize);
            (*new_leaf).mask.store(1, Relaxed);
            (*new_leaf).usued.store(1, Relaxed);
        }
        (new_leaf as *mut usize, false)
    }
}

// todo: remove this pub (and Node4's pub)
impl Node {
    pub fn make_node4() -> *mut Node4 {
        Box::into_raw(Box::new(Node4::new()))
    }
}

#[derive(Clone, PartialEq, Debug, Copy)]
pub enum NodeType {
    Node4,
    Node16,
    Node48,
    Node256,
    KVPair,
}

#[derive(Debug)]
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
    leaf: NodePtr,
    // mark keys exist or not in bits
    mask: AtomicU8,
    usued: AtomicU8,
    key: [AtomicU8; 4],
    child: [NodePtr; 4],
}

impl Node4 {
    pub fn new() -> Self {
        let (key, child) = {
            let mut key: [MaybeUninit<AtomicU8>; 4] =
                unsafe { MaybeUninit::uninit().assume_init() };
            let mut child: [MaybeUninit<NodePtr>; 4] =
                unsafe { MaybeUninit::uninit().assume_init() };

            for i in 0..4 {
                key[i] = MaybeUninit::new(AtomicU8::default());
                child[i] = MaybeUninit::new(NodePtr::default());
            }

            unsafe { (mem::transmute(key), mem::transmute(child)) }
        };

        let mut ret = Self {
            header: Header::new(NodeType::Node4),
            mask: AtomicU8::new(0),
            usued: AtomicU8::new(0),
            key,
            child,
            leaf: NodePtr::default(),
        };

        ret
    }

    pub fn find_child(&self, key: &u8) -> Option<&NodePtr> {
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

    pub fn grow(node: &NodePtr) -> *mut usize {
        let new_node = Box::into_raw(Box::new(Node16::new()));
        let fulled_node = unsafe { &*(node.load() as *const Node4) };

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
                    (*new_node).child[cnt].store(fulled_node.child[i].load());
                    cnt += 1;
                }
            }
            debug_assert_eq!(fulled_node.usued.load(Relaxed) as usize, cnt);
            (*new_node).usued.store(cnt as u8, Relaxed);
            (*new_node).mask.store((1 << cnt + 1) - 1, Relaxed);
        }

        new_node as *mut usize
    }

    pub fn add_child(&mut self, key: u8, child: *const usize) {
        let usued = self.usued.load(Relaxed);
        self.key[usued as usize].store(key, Relaxed);
        self.child[usued as usize].store(child as *mut usize);

        self.mask
            .store(self.mask.load(Relaxed) | 1 << usued, Relaxed);
        self.usued.fetch_add(1, Relaxed);
        self.header.count += 1;
    }

    pub fn remove_child(&mut self, key: u8) -> *mut usize {
        self.header.count -= 1;
        let mask = self.mask.load(Relaxed);
        for i in 0..4 {
            if mask >> i & 1 == 1 && self.key[i].load(Relaxed) == key {
                self.mask.store(mask - (1 << i), Relaxed);
                return self.child[i].swap(ptr::null::<usize>() as *mut usize);
            }
        }
        unreachable!("key must exist")
    }
}

impl Drop for Node4 {
    fn drop(&mut self) {
        for i in 0..4 {
            let ptr = self.child[i].load();
            if ptr.is_null() {
                return;
            }

            if self.child[i].get_type() == NodeType::KVPair {
                let ptr = (ptr as usize - 1) as *mut KVPair;
                unsafe {
                    let _ = Box::from_raw(ptr);
                }
            }
        }
    }
}

#[repr(C)]
#[derive(Debug)]
struct Node16 {
    header: Header,
    leaf: NodePtr,
    mask: AtomicU16,
    usued: AtomicU8,
    key: [AtomicU8; 16],
    child: [NodePtr; 16],
}

impl Node16 {
    pub fn new() -> Self {
        let (key, child) = {
            let mut key: [MaybeUninit<AtomicU8>; 16] =
                unsafe { MaybeUninit::uninit().assume_init() };
            let mut child: [MaybeUninit<NodePtr>; 16] =
                unsafe { MaybeUninit::uninit().assume_init() };

            for i in 0..16 {
                key[i] = MaybeUninit::new(AtomicU8::default());
                child[i] = MaybeUninit::new(NodePtr::default());
            }

            unsafe { (mem::transmute(key), mem::transmute(child)) }
        };

        let mut ret = Self {
            header: Header::new(NodeType::Node16),
            leaf: NodePtr::default(),
            mask: AtomicU16::new(0),
            usued: AtomicU8::new(0),
            key,
            child,
        };

        ret
    }

    pub fn find_child(&self, key: &u8) -> Option<&NodePtr> {
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

    pub fn grow(node: &NodePtr) -> *mut usize {
        let new_node = Box::into_raw(Box::new(Node48::new()));
        let fulled_node = unsafe { &*(node.load() as *const Node16) };

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
                    (*new_node).child[cnt].store(fulled_node.child[i].load());
                    (*new_node).key[fulled_node.key[cnt].load(Relaxed) as usize]
                        .store(i as i8, Relaxed);
                    cnt += 1;
                }
            }
            debug_assert_eq!(fulled_node.usued.load(Relaxed) as usize, cnt);
        }

        new_node as *mut usize
    }

    pub fn shrink(node: &NodePtr) -> *mut usize {
        let new_node = Box::into_raw(Box::new(Node4::new()));
        let empty_node = unsafe { &*(node.load() as *const Node16) };

        unsafe {
            (*new_node)
                .header
                .copy_from(empty_node as *const Node16 as *mut usize);

            let mut cnt = 0;
            for i in 0..16 {
                if !empty_node.child[i].load().is_null() {
                    (*new_node).key[cnt].store(empty_node.key[i].load(Relaxed), Relaxed);
                    (*new_node).child[cnt].store(empty_node.child[i].load());
                    cnt += 1;
                }
            }
            (*new_node).usued.store(cnt as u8, Relaxed);
            (*new_node).mask.store((1 << cnt) - 1, Relaxed);
            assert!(cnt < 4);
        }

        new_node as *mut usize
    }

    pub fn add_child(&mut self, key: u8, child: *const usize) {
        let usued = self.usued.load(Relaxed);
        let mask = self.mask.load(Relaxed);
        self.key[usued as usize].store(key, Relaxed);
        self.child[usued as usize].store(child as *mut usize);

        self.mask.store(mask | 1 << usued, Relaxed);
        self.usued.fetch_add(1, Relaxed);
        self.header.count += 1;
    }

    pub fn remove_child(&mut self, key: u8) -> *mut usize {
        self.header.count -= 1;
        let usued = self.usued.load(Relaxed);
        let mask = self.mask.load(Relaxed);

        for i in 0..usued as usize {
            if mask >> i & 1 == 1 && self.key[i].load(Relaxed) == key {
                // todo: fix this
                self.mask.store(mask - (1 << i), Relaxed);
                return self.child[i].swap(ptr::null_mut());
            }
        }
        unreachable!("key must exist")
    }
}

#[repr(C)]
#[derive(Debug)]
struct Node48 {
    header: Header,
    leaf: NodePtr,
    // Stores child index, negative means not exist
    key: [AtomicI8; 256],
    child: [NodePtr; 48],
}

impl Node48 {
    pub fn new() -> Self {
        let (key, child) = {
            let mut key: [MaybeUninit<AtomicI8>; 256] =
                unsafe { MaybeUninit::uninit().assume_init() };
            let mut child: [MaybeUninit<NodePtr>; 48] =
                unsafe { MaybeUninit::uninit().assume_init() };

            for i in 0..48 {
                key[i] = MaybeUninit::new(AtomicI8::new(-1));
                child[i] = MaybeUninit::new(NodePtr::default());
            }
            for i in 48..256 {
                key[i] = MaybeUninit::new(AtomicI8::new(-1));
            }

            unsafe { (mem::transmute(key), mem::transmute(child)) }
        };

        let mut ret = Self {
            header: Header::new(NodeType::Node48),
            key,
            child,
            leaf: NodePtr::default(),
        };

        ret
    }

    pub fn find_child(&self, key: &u8) -> Option<&NodePtr> {
        if self.key[*key as usize].load(Relaxed) >= 0 {
            return Some(&self.child[self.key[*key as usize].load(Relaxed) as usize]);
        }
        None
    }

    pub fn grow(node: &NodePtr) -> *mut usize {
        let new_node = Box::into_raw(Box::new(Node256::new()));
        let fulled_node = unsafe { &*(node.load() as *const Node48) };

        // copy header
        unsafe {
            (*new_node)
                .header
                .copy_from(fulled_node as *const Node48 as *mut usize);

            // child field
            for i in 0..=255 {
                if fulled_node.key[i].load(Relaxed) >= 0 {
                    (*new_node).child[i]
                        .store(fulled_node.child[fulled_node.key[i].load(Relaxed) as usize].load());
                }
            }
        }

        new_node as *mut usize
    }

    pub fn shrink(node: &NodePtr) -> *mut usize {
        let new_node = Box::into_raw(Box::new(Node16::new()));
        let empty_node = unsafe { &*(node.load() as *const Node48) };

        unsafe {
            (*new_node)
                .header
                .copy_from(empty_node as *const Node48 as *mut usize);

            let mut cnt = 0;
            for i in 0..256 {
                let pos = empty_node.key[i].load(Relaxed);
                if pos >= 0 {
                    (*new_node).key[cnt].store(i as u8, Relaxed);
                    (*new_node).child[cnt].store(empty_node.child[pos as usize].load());
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

    pub fn add_child(&mut self, key: u8, child: *const usize) {
        self.child[self.header.count as usize].store(child as *mut usize);
        self.key[key as usize].store(self.header.count as i8, Relaxed);
        self.header.count += 1;
    }

    pub fn remove_child(&mut self, key: u8) -> *mut usize {
        self.header.count -= 1;

        let pos = self.key[key as usize].swap(-1, Relaxed);
        self.child[pos as usize].swap(ptr::null_mut())
    }
}

#[repr(C)]
#[derive(Debug)]
struct Node256 {
    header: Header,
    leaf: NodePtr,
    child: [NodePtr; 256],
}

impl Node256 {
    pub fn new() -> Self {
        let child = {
            let mut child: [MaybeUninit<NodePtr>; 256] =
                unsafe { MaybeUninit::uninit().assume_init() };

            for i in 0..256 {
                child[i] = MaybeUninit::new(NodePtr::default());
            }

            unsafe { mem::transmute(child) }
        };

        let mut ret = Self {
            header: Header::new(NodeType::Node256),
            child,
            leaf: NodePtr::default(),
        };

        ret
    }

    pub fn find_child(&self, key: &u8) -> Option<&NodePtr> {
        if !self.child[*key as usize].load().is_null() {
            return Some(&self.child[*key as usize]);
        }
        None
    }

    pub fn shrink(node: &NodePtr) -> *mut usize {
        let new_node = Box::into_raw(Box::new(Node48::new()));
        let empty_node = unsafe { &*(node.load() as *const Node256) };

        unsafe {
            (*new_node)
                .header
                .copy_from(empty_node as *const Node256 as *mut usize);

            let mut cnt = 0;
            for i in 0..256 {
                if !empty_node.child[i].load().is_null() {
                    (*new_node).key[i].store(cnt as i8, Relaxed);
                    (*new_node).child[cnt].store(empty_node.child[i].load());
                    cnt += 1;
                }
            }
            assert!(cnt < 48);
        }

        new_node as *mut usize
    }

    pub fn add_child(&mut self, key: u8, child: *const usize) {
        self.child[key as usize].store(child as *mut usize);
        self.header.count += 1;
    }

    pub fn remove_child(&mut self, key: u8) -> *mut usize {
        self.header.count -= 1;
        self.child[key as usize].swap(ptr::null_mut())
    }
}

#[derive(Debug)]
pub struct NodePtr {
    ptr: AtomicPtr<usize>,
    count: AtomicUsize,
}

impl NodePtr {
    fn new(ptr: *mut usize) -> Self {
        Self {
            ptr: AtomicPtr::new(ptr),
            count: AtomicUsize::new(1),
        }
    }

    fn clone(&self) -> Self {
        todo!()
    }

    unsafe fn obsolate(&self) {
        let cnt = self.count.fetch_sub(1, Relaxed);
        assert!(cnt > 0);
    }

    fn store(&self, ptr: *mut usize) {
        self.ptr.store(ptr, Relaxed);
    }

    fn load(&self) -> *mut usize {
        self.ptr.load(Relaxed)
    }

    fn swap(&self, ptr: *mut usize) -> *mut usize {
        self.ptr.swap(ptr, Relaxed)
    }

    fn get_type(&self) -> NodeType {
        let ptr = self.ptr.load(Relaxed);
        if (ptr as usize) & 1 == 1 {
            NodeType::KVPair
        } else {
            unsafe { (*(ptr as *mut Node4)).header.node_type }
        }
    }

    fn refer(&self) -> NodeRef {
        NodeRef { ptr_ref: &self }
    }

    // Manually increase strong counter by one.
    // Usually when creating a new inner node to replace an old one, atomic store
    // is called instead of "move". which will lead to a `drop` call and decrease
    // counter. In that situation needs to invoke this method to balance that `drop` call.
    fn increase_counter(&self) {
        self.count.fetch_add(1, Relaxed);
    }
}

impl Drop for NodePtr {
    fn drop(&mut self) {
        let cnt = self.count.fetch_sub(1, Relaxed);
        if cnt == 1 {
            let ptr = self.load();
            if ptr.is_null() {
                return;
            }
            println!("going to drop a NodePtr");

            match self.get_type() {
                NodeType::Node4 => unsafe {
                    let _ = Box::from_raw(ptr as *mut Node4);
                },
                NodeType::Node16 => unsafe {
                    let _ = Box::from_raw(ptr as *mut Node16);
                },
                NodeType::Node48 => unsafe {
                    let _ = Box::from_raw(ptr as *mut Node48);
                },
                NodeType::Node256 => unsafe {
                    let _ = Box::from_raw(ptr as *mut Node256);
                },
                NodeType::KVPair => return,
            }
        }
    }
}

impl Default for NodePtr {
    fn default() -> Self {
        Self {
            ptr: AtomicPtr::new(ptr::null_mut::<usize>()),
            count: AtomicUsize::new(1),
        }
    }
}

struct NodeRef<'a> {
    ptr_ref: &'a NodePtr,
}

impl<'a> Drop for NodeRef<'a> {
    fn drop(&mut self) {
        self.ptr_ref.count.fetch_sub(1, Relaxed);
    }
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
                NodeType::KVPair => unreachable!(),
            }
        }
    }

    fn debug_print_atomic(node: &AtomicPtr<usize>) {
        debug_print(node.load(Relaxed));
    }

    // todo: maybe remove this? needn't a specific `init()` call
    #[test]
    fn init() {
        let root = NodePtr::new(empty_node4() as *mut usize);
        Node::init(&root, &[1, 2, 3, 4], &[1, 2, 3, 4]);
        let header = Node::get_header(&root);
        debug!("header: {:?}", header);
        let result = Node::search(&root, &[1, 2, 3, 4], 0);
        debug!("result kvpair: {:?}", result.unwrap());
    }

    // todo: fix and remove ignore
    #[test]
    #[ignore]
    fn test_simple_from_ground() {
        let root = NodePtr::new(ptr::null::<*const usize>() as *mut usize);
        let kvpair = KVPair::new([1, 2, 3, 4].to_vec(), [1, 2, 3, 4].to_vec());
        let kvpair_ptr = Box::into_raw(Box::new(kvpair));
        Node::insert(&root, &[1, 2, 3, 4], kvpair_ptr, 0).unwrap();

        let kvpair = KVPair::new([1, 2, 3, 4, 5].to_vec(), [1, 2, 3, 4, 5].to_vec());
        let kvpair_ptr = Box::into_raw(Box::new(kvpair));
        Node::insert(&root, &[1, 2, 3, 4, 5], kvpair_ptr, 0).unwrap();

        Node::search(&root, &[1, 2, 3, 4], 0).unwrap();
        Node::search(&root, &[1, 2, 3, 4, 5], 0).unwrap();
    }

    #[test]
    fn test_node_expand() {
        let root = NodePtr::new(empty_node4() as *mut usize);
        Node::init(&root, &[1, 2, 3, 4], &[1, 2, 3, 4]);

        let kvs = vec![vec![1, 2, 1], vec![1, 2, 2], vec![1, 2, 2, 1]];

        let mut answer = HashMap::new();
        for kv in &kvs {
            // debug_print_atomic(&root);
            // let kvpair = KVPair::new(kv.to_owned(), kv.to_owned());
            // let kvpair_ptr = Box::into_raw(Box::new(kvpair));
            let kvpair_ptr = KVPair::new(kv.to_owned(), kv.to_owned()).into_raw();
            answer.insert(kv.to_owned(), kvpair_ptr as *mut usize);
            Node::insert(&root, &kv, kvpair_ptr, 0).unwrap();
        }

        // search
        for kv in &kvs {
            let result = Node::search(&root, kv, 0).unwrap();
            assert_eq!(result, *answer.get(kv).unwrap());
        }

        //remove
        for kv in kvs {
            let result = Node::remove(&root, &kv, 0).unwrap();
            let kvpair = unsafe { &*(result as *mut KVPair) };
            assert_eq!(kvpair.value.as_slice(), kv);
            unsafe {
                let _ = Box::from_raw(result);
            }
        }
    }

    #[test]
    fn test_node_grow() {
        let root = NodePtr::new(empty_node4() as *mut usize);
        Node::init(&root, &[1, 1, 1, 0], &[1, 1, 1, 0]);

        let mut kvs = [[1, 1, 1, 1]; 255];
        for i in 1..=255 {
            kvs[i - 1][3] = i as u8;
        }

        // insert
        let mut answer = HashMap::new();
        for kv in &kvs {
            // debug_print_atomic(&root);
            // let kvpair = KVPair::new(kv.to_vec(), kv.to_vec());
            // let kvpair_ptr = Box::into_raw(Box::new(kvpair));
            let kvpair_ptr = KVPair::new(kv.to_vec(), kv.to_vec()).into_raw();
            answer.insert(kv.to_owned(), kvpair_ptr as *mut usize);
            Node::insert(&root, kv, kvpair_ptr, 0).unwrap();
        }

        // search
        for kv in &kvs {
            let result = Node::search(&root, kv, 0);
            assert_eq!(result.unwrap(), *answer.get(kv).unwrap());
        }

        //remove
        for kv in &kvs {
            let result = Node::remove(&root, kv, 0).unwrap();
            let kvpair = unsafe { &*(result as *mut KVPair) };
            assert_eq!(kvpair.value.as_slice(), kv);
            unsafe {
                let _ = Box::from_raw(result);
            }
        }
    }

    #[test]
    fn test_node_substring() {
        let root = NodePtr::new(empty_node4() as *mut usize);
        Node::init(&root, &[0], &[0]);
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
            // debug_print_atomic(&root);
            // let kvpair = KVPair::new(kv.to_vec(), kv.to_vec());
            // let kvpair_ptr = Box::into_raw(Box::new(kvpair));
            let kvpair_ptr = KVPair::new(kv.to_vec(), kv.to_vec()).into_raw();
            answer.insert(kv.to_owned(), kvpair_ptr as *mut usize);
            Node::insert(&root, kv, kvpair_ptr, 0).unwrap();
        }

        // search
        for kv in &kvs {
            let result = Node::search(&root, kv, 0);
            assert_eq!(result.unwrap(), *answer.get(kv).unwrap());
        }

        // remove
        for kv in &kvs {
            let result = Node::remove(&root, kv, 0).unwrap();
            let kvpair = unsafe { &*(result as *mut KVPair) };
            assert_eq!(&kvpair.value, kv);
            unsafe {
                let _ = Box::from_raw(result);
            }
        }
    }

    #[test]
    fn test_node_collapse() {
        let root = NodePtr::new(empty_node4() as *mut usize);
        Node::init(&root, &[1], &[0]);

        let kvs = vec![
            vec![0, 0],
            vec![0, 0, 0, 0],
            vec![3, 3, 3, 3],
            vec![4, 4, 4, 4, 4],
        ];

        let mut answer = HashMap::new();
        for k in &kvs {
            // let kvpair = KVPair::new(k.to_vec(), k.to_vec());
            // let kvpair_ptr = Box::into_raw(Box::new(kvpair));
            let kvpair_ptr = KVPair::new(k.to_vec(), k.to_vec()).into_raw();
            answer.insert(k.to_owned(), kvpair_ptr as *mut usize);
            Node::insert(&root, k, kvpair_ptr, 0).unwrap();
        }

        for k in &kvs {
            let result = Node::search(&root, k, 0);
            assert_eq!(result.unwrap(), *answer.get(k).unwrap());
        }

        // remove
        for kv in &kvs {
            let result = Node::remove(&root, kv, 0).unwrap();
            let kvpair = unsafe { &*(result as *mut KVPair) };
            assert_eq!(&kvpair.value, kv);
            unsafe {
                let _ = Box::from_raw(result);
            }
        }
    }
}
