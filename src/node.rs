use std::alloc::{dealloc, Layout};
#[allow(unused_variables)]
use std::cmp::Ordering;
use std::fmt::{self, Debug, Formatter};
use std::mem::{self, MaybeUninit};
use std::ptr;
use std::sync::atomic::Ordering::Relaxed;
use std::sync::atomic::{AtomicI8, AtomicPtr, AtomicU8};
use std::sync::Arc;

use log::{debug, info};

type PrefixCount = u32;
const MAX_PREFIX_STORED: usize = 10;
type K = usize;
type V = usize;

pub struct Node {}

impl Node {
    pub fn init(node: &AtomicPtr<usize>, key: &[u8], value: &[u8]) {
        let mut header = Self::get_header_mut(node.load(Relaxed));
        assert!(header.count == 0);
        header.prefix_len = key.len() as u32 - 1;
        for i in 0..(header.prefix_len as usize).min(MAX_PREFIX_STORED) {
            header.prefix[i] = key[i];
        }
        let kvpair = KVPair::new(key.to_owned(), value.to_owned());
        let kvpair_ptr = Box::into_raw(Box::new(kvpair)) as usize + 1;
        Self::add_child(node, key[key.len() - 1], kvpair_ptr as *mut usize);
    }

    pub fn search<'a>(node: &'a AtomicPtr<usize>, key: &[u8], depth: usize) -> Option<*mut usize> {
        if node.load(Relaxed).is_null() {
            info!("search encounted a null ptr");
            return None;
        }
        // lazy expansion
        // run out of key bytes, should reach leaf node
        if depth == key.len() {
            if Self::is_leaf_match(node, key) {
                if Self::is_kvpair(node) {
                    return Some(node.load(Relaxed));
                } else {
                    let leaf = Self::to_node4(node).leaf.load(Relaxed);
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
        // another lazy expansion?
        if Node::is_kvpair(next) {
            if Node::is_leaf_match(next, key) {
                return Some((next.load(Relaxed) as usize - 1) as *mut usize);
            }
            return None;
        }
        return Self::search(next, key, depth + 1);
    }

    // leaf pointer is tagged
    pub fn insert<'a>(
        node: &'a AtomicPtr<usize>,
        key: &[u8],
        leaf: *mut KVPair,
        depth: usize,
    ) -> Result<(), ()> {
        if node.load(Relaxed).is_null() {
            node.store(leaf as *mut usize, Relaxed);
            return Ok(());
        }
        unsafe {
            // reached a kvpair node. replace it by a inner node, move kvpair to `leaf` and add 1 child.
            // this happens when old key is substring of new key.
            if Self::is_kvpair(node) {
                let new_inner_node_ptr = Self::make_node4() as *mut usize;
                // maybe no prefix? Todo: check this
                let new_inner_node = &mut *(new_inner_node_ptr as *mut Node4);
                new_inner_node.leaf.store(node.load(Relaxed), Relaxed);
                let tmp_atomic = AtomicPtr::new(new_inner_node_ptr); // todo: remove this
                Self::add_child(&tmp_atomic, *key.last().unwrap(), leaf as *mut usize);
                // swap
                node.store(new_inner_node_ptr, Relaxed);
                return Ok(());
            }
            let p = Self::check_prefix(node, key, depth);
            // todo: remove hard coded "Node4"
            if p != Self::get_prefix_len(node) {
                // make a copy of node and modify it,
                // construct new inner node and replace node
                let mut node_substitute: Node4 =
                    mem::transmute_copy(&*(node.load(Relaxed) as *const Node4)); // ?
                node_substitute.header.prefix_len = p;
                let node_substitute_ptr = Box::into_raw(Box::new(node_substitute));

                let new_inner_node = AtomicPtr::new(Self::make_node4() as *mut usize);
                let node_prefix = Self::get_header(node).prefix;
                let header = Self::get_header_mut(new_inner_node.load(Relaxed));
                header.prefix_len = p;
                Self::get_header_mut(new_inner_node.load(Relaxed) as *mut usize).prefix_len = p;
                for i in 0..MAX_PREFIX_STORED.min(p as usize) {
                    header.prefix[i] = node_prefix[i];
                }

                Self::add_child(
                    &new_inner_node,
                    key[depth + p as usize],
                    leaf as *const usize,
                );
                Self::add_child(
                    &new_inner_node,
                    node_prefix[p as usize],
                    node_substitute_ptr as *mut usize,
                );

                node.store(new_inner_node.load(Relaxed) as *mut usize, Relaxed);
                // todo: drop old ptr
                return Ok(());
            }

            let depth = depth + Self::get_prefix_len(node) as usize;
            if let Some(next_node) = Self::find_child(node, &key[depth]) {
                Self::insert(next_node, key, leaf, depth + 1)?;
            } else {
                if Self::is_overflow(node) {
                    Self::grow(&node);
                }
                let new_leaf_node = Self::make_new_leaf(key, leaf, depth + 1);
                Self::add_child(node, key[depth], new_leaf_node);
            }
            return Ok(());
        }
    }

    pub fn remove<'a>(node: &'a AtomicPtr<usize>, key: &[u8], depth: usize) -> Option<*mut usize> {
        if node.load(Relaxed).is_null() {
            return None;
        }
        if Self::is_kvpair(node) {
            // return None;
            unreachable!("will not reach kvpair");
        }
        // need check `leaf` field
        // todo: under write ex this need not to be atomit
        if depth == key.len() {
            let leaf = &Self::to_node4(node).leaf;
            loop {
                let leaf_ptr = leaf.load(Relaxed);
                if Self::is_leaf_match(node, key) {
                    if leaf.compare_and_swap(leaf_ptr, 0 as *mut usize, Relaxed) == leaf_ptr {
                        return Some(leaf_ptr);
                    } else {
                        continue;
                    }
                } else {
                    return None;
                }
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
                if Self::is_kvpair(&Arc::new(AtomicPtr::new(removed as *mut usize))) {
                    let raw_ptr = (removed as usize - 1) as *mut KVPair;
                    unsafe {
                        ptr::drop_in_place(raw_ptr);
                        dealloc(raw_ptr as *mut u8, Layout::new::<KVPair>());
                    }
                }
            }
            return None;
        }

        let ret = Self::remove(next, key, depth + 1);
        // downgrade empty inner node to its `leaf`
        if Self::get_header(next).count == 0 {
            let leaf = &Self::to_node4(node).leaf;
            next.store(leaf.load(Relaxed), Relaxed);
        }

        ret
    }
}

impl Node {
    fn is_leaf_match(node: &AtomicPtr<usize>, key: &[u8]) -> bool {
        if Self::is_kvpair(node) {
            Self::to_kvpair(node).key.as_slice() == key
        } else {
            let leaf = &Self::to_node4(node).leaf;
            if !leaf.load(Relaxed).is_null() {
                Self::to_kvpair(&leaf).key.as_slice() == key
            } else {
                // assert leaf exist?
                false
            }
        }
    }

    // tagged pointer
    fn is_kvpair(node: &AtomicPtr<usize>) -> bool {
        node.load(Relaxed) as usize % 2 == 1
    }

    fn to_kvpair(node: &AtomicPtr<usize>) -> &KVPair {
        unsafe { &*((node.load(Relaxed) as usize - 1) as *mut KVPair) }
    }

    // All node struct is order-preserving #[repr(C)]. With Header in the first place
    // and Leaf pointer in the second. This method can only be used to access above two
    // fields when actual type is not specified.
    fn to_node4(node: &AtomicPtr<usize>) -> &Node4 {
        assert!(!Self::is_kvpair(node));
        unsafe { &*(node.load(Relaxed) as *mut Node4) }
    }

    // fully check stored key
    fn leaf_match(node: &AtomicPtr<usize>, key: &[u8], _depth: &usize) -> bool {
        assert!(Self::is_kvpair(node));

        let kvpair = unsafe { &*((node.load(Relaxed) as usize - 1) as *const KVPair) };
        if kvpair.key.len() != key.len() {
            return false;
        }

        for (stored, expected) in kvpair.key.iter().zip(key) {
            if stored != expected {
                return false;
            }
        }
        return true;
    }

    // Return node.header.prefix_len if match, or 0 if not.
    fn check_prefix(node: &AtomicPtr<usize>, key: &[u8], depth: usize) -> PrefixCount {
        assert!(!Self::is_kvpair(node));

        let header = unsafe { &*(node.load(Relaxed) as *const Header) };
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

    fn get_prefix_len(node: &AtomicPtr<usize>) -> PrefixCount {
        assert!(!Self::is_kvpair(node));

        unsafe { (*(node.load(Relaxed) as *const Header)).prefix_len }
    }

    fn find_child<'a>(
        node_ptr: &'a AtomicPtr<usize>,
        key_byte: &u8,
    ) -> Option<&'a AtomicPtr<usize>> {
        assert!(!Self::is_kvpair(node_ptr));

        unsafe {
            match Self::get_header(node_ptr).node_type {
                NodeType::Node4 => {
                    let node = node_ptr.load(Relaxed) as *const Node4;
                    (*node).find_child(key_byte)
                }
                NodeType::Node16 => {
                    let node = node_ptr.load(Relaxed) as *const Node16;
                    (*node).find_child(key_byte)
                }
                NodeType::Node48 => {
                    let node = node_ptr.load(Relaxed) as *const Node48;
                    (*node).find_child(key_byte)
                }
                NodeType::Node256 => {
                    let node = node_ptr.load(Relaxed) as *const Node256;
                    (*node).find_child(key_byte)
                }
            }
        }
    }

    fn get_header(node: &AtomicPtr<usize>) -> &Header {
        assert!(!Self::is_kvpair(node));

        unsafe { &*(node.load(Relaxed) as *const Header) }
    }

    fn get_header_mut<'a>(node: *mut usize) -> &'a mut Header {
        // assert!(!Self::is_leaf(node));

        // &mut unsafe { *(node.load(Relaxed) as *mut Header) }
        unsafe { &mut *(node as *mut Header) }
    }

    fn load_prefix(node: &AtomicPtr<usize>) -> Option<&[u8]> {
        assert!(!Self::is_kvpair(node));

        Some(&Self::get_header(node).prefix)
    }

    // todo: SIMD
    // todo: order-preserving
    fn add_child(node_ptr: &AtomicPtr<usize>, key_byte: u8, child: *const usize) {
        assert!(!Self::is_kvpair(node_ptr));

        unsafe {
            match Self::get_header(node_ptr).node_type {
                NodeType::Node4 => {
                    let node = node_ptr.load(Relaxed) as *mut Node4;
                    (*node).add_child(key_byte, child)
                }
                NodeType::Node16 => {
                    let node = node_ptr.load(Relaxed) as *mut Node16;
                    (*node).add_child(key_byte, child)
                }
                NodeType::Node48 => {
                    let node = node_ptr.load(Relaxed) as *mut Node48;
                    (*node).add_child(key_byte, child)
                }
                NodeType::Node256 => {
                    let node = node_ptr.load(Relaxed) as *mut Node256;
                    (*node).add_child(key_byte, child)
                }
            }
        }
    }

    fn remove_child(node_ptr: &AtomicPtr<usize>, key_byte: u8) -> *mut KVPair {
        assert!(!Self::is_kvpair(node_ptr));

        let ret = unsafe {
            match Self::get_header(node_ptr).node_type {
                NodeType::Node4 => {
                    let node = node_ptr.load(Relaxed) as *mut Node4;
                    (*node).remove_child(key_byte)
                }
                NodeType::Node16 => {
                    let node = node_ptr.load(Relaxed) as *mut Node16;
                    (*node).remove_child(key_byte)
                }
                NodeType::Node48 => {
                    let node = node_ptr.load(Relaxed) as *mut Node48;
                    (*node).remove_child(key_byte)
                }
                NodeType::Node256 => {
                    let node = node_ptr.load(Relaxed) as *mut Node256;
                    (*node).remove_child(key_byte)
                }
            }
        };

        ret as *mut KVPair
    }

    fn is_overflow(node: &AtomicPtr<usize>) -> bool {
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

    fn is_underflow(node: &AtomicPtr<usize>) -> bool {
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
    fn grow(node: &AtomicPtr<usize>) {
        let header = Self::get_header(node);
        let grown = match header.node_type {
            NodeType::Node4 => Node4::grow(&node),
            NodeType::Node16 => Node16::grow(&node),
            NodeType::Node48 => Node48::grow(&node),
            NodeType::Node256 => unreachable!("Node256 cannot grow"),
        };

        node.store(grown, Relaxed);
    }

    fn shrink(node: &AtomicPtr<usize>) {
        let header = Self::get_header(node);

        let shrunk = match header.node_type {
            NodeType::Node4 => unreachable!("Node4 cannot shrink"),
            NodeType::Node16 => Node16::shrink(&node),
            NodeType::Node48 => Node48::shrink(&node),
            NodeType::Node256 => Node256::shrink(&node),
        };

        node.store(shrunk, Relaxed);
    }

    fn make_new_leaf(key: &[u8], leaf: *mut KVPair, depth: usize) -> *mut usize {
        // needn't to wrap a Node4
        if key.len() == depth {
            return leaf as *mut usize;
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
            (*new_leaf).child[0].store(leaf as *mut usize, Relaxed);
        }
        new_leaf as *mut usize
    }
}

impl Node {
    fn make_node4() -> *mut Node4 {
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

#[derive(Debug)]
pub struct KVPair {
    pub key: Vec<u8>,
    pub value: Vec<u8>,
}

impl KVPair {
    pub fn new(key: Vec<u8>, value: Vec<u8>) -> Self {
        Self { key, value }
    }
}

#[repr(C)]
#[derive(Debug)]
struct Node4 {
    header: Header,
    leaf: AtomicPtr<usize>,
    key: [AtomicU8; 4],
    child: [AtomicPtr<usize>; 4],
}

impl Node4 {
    pub fn new() -> Self {
        let (key, child) = {
            let mut key: [MaybeUninit<AtomicU8>; 4] =
                unsafe { MaybeUninit::uninit().assume_init() };
            let mut child: [MaybeUninit<AtomicPtr<usize>>; 4] =
                unsafe { MaybeUninit::uninit().assume_init() };

            for i in 0..4 {
                key[i] = MaybeUninit::new(AtomicU8::default());
                child[i] = MaybeUninit::new(AtomicPtr::default());
            }

            unsafe { (mem::transmute(key), mem::transmute(child)) }
        };
        Self {
            header: Header::new(NodeType::Node4),
            key,
            child,
            leaf: AtomicPtr::default(),
        }
    }

    pub fn find_child(&self, key: &u8) -> Option<&AtomicPtr<usize>> {
        for i in 0..self.header.count as usize {
            if &self.key[i].load(Relaxed) == key {
                return Some(&self.child[i]);
            }
        }
        None
    }

    pub fn grow(node: &AtomicPtr<usize>) -> *mut usize {
        let new_node = Box::into_raw(Box::new(Node16::new()));
        let fulled_node = unsafe { &*(node.load(Relaxed) as *const Node4) };

        // copy header
        unsafe {
            (*new_node)
                .header
                .copy_from(fulled_node as *const Node4 as *mut usize);

            // key & child field
            for i in 0..4 {
                (*new_node).key[i].store(fulled_node.key[i].load(Relaxed), Relaxed);
                (*new_node).child[i].store(fulled_node.child[i].load(Relaxed), Relaxed);
            }
        }

        new_node as *mut usize
    }

    pub fn add_child(&mut self, key: u8, child: *const usize) {
        self.key[self.header.count as usize].store(key, Relaxed);
        self.child[self.header.count as usize].store(child as *mut usize, Relaxed);
        self.header.count += 1;
    }

    pub fn remove_child(&mut self, key: u8) -> *mut usize {
        self.header.count -= 1;
        for i in 0..4 {
            if self.key[i].load(Relaxed) == key {
                return self.child[i].swap(ptr::null::<usize>() as *mut usize, Relaxed);
            }
        }
        unreachable!("key must exist")
    }
}

#[repr(C)]
#[derive(Debug)]
struct Node16 {
    header: Header,
    leaf: AtomicPtr<usize>,
    key: [AtomicU8; 16],
    child: [AtomicPtr<usize>; 16],
}

impl Node16 {
    pub fn new() -> Self {
        let (key, child) = {
            let mut key: [MaybeUninit<AtomicU8>; 16] =
                unsafe { MaybeUninit::uninit().assume_init() };
            let mut child: [MaybeUninit<AtomicPtr<usize>>; 16] =
                unsafe { MaybeUninit::uninit().assume_init() };

            for i in 0..16 {
                key[i] = MaybeUninit::new(AtomicU8::default());
                child[i] = MaybeUninit::new(AtomicPtr::default());
            }

            unsafe { (mem::transmute(key), mem::transmute(child)) }
        };
        Self {
            header: Header::new(NodeType::Node16),
            key,
            child,
            leaf: AtomicPtr::default(),
        }
    }

    pub fn find_child(&self, key: &u8) -> Option<&AtomicPtr<usize>> {
        // todo: use SIMD or binary search
        for i in 0..self.header.count as usize {
            if &self.key[i].load(Relaxed) == key {
                return Some(&self.child[i]);
            }
        }
        None
    }

    pub fn grow(node: &AtomicPtr<usize>) -> *mut usize {
        let new_node = Box::into_raw(Box::new(Node48::new()));
        let fulled_node = unsafe { &*(node.load(Relaxed) as *const Node16) };

        // copy header
        unsafe {
            (*new_node)
                .header
                .copy_from(fulled_node as *const Node16 as *mut usize);

            // key & child field
            for i in 0..16 {
                (*new_node).child[i].store(fulled_node.child[i].load(Relaxed), Relaxed);
                (*new_node).key[fulled_node.key[i].load(Relaxed) as usize].store(i as i8, Relaxed);
            }
        }

        new_node as *mut usize
    }

    pub fn shrink(node: &AtomicPtr<usize>) -> *mut usize {
        let new_node = Box::into_raw(Box::new(Node4::new()));
        let empty_node = unsafe { &*(node.load(Relaxed) as *const Node16) };

        unsafe {
            (*new_node)
                .header
                .copy_from(empty_node as *const Node16 as *mut usize);

            let mut cnt = 0;
            for i in 0..16 {
                if !empty_node.child[i].load(Relaxed).is_null() {
                    (*new_node).key[cnt].store(empty_node.key[i].load(Relaxed), Relaxed);
                    (*new_node).child[cnt].store(empty_node.child[i].load(Relaxed), Relaxed);
                    cnt += 1;
                }
            }
            assert_eq!(cnt, 4);
        }

        new_node as *mut usize
    }

    pub fn add_child(&mut self, key: u8, child: *const usize) {
        self.key[self.header.count as usize].store(key, Relaxed);
        self.child[self.header.count as usize].store(child as *mut usize, Relaxed);
        self.header.count += 1;
    }

    pub fn remove_child(&mut self, key: u8) -> *mut usize {
        self.header.count -= 1;
        for i in 0..16 {
            if self.key[i].load(Relaxed) == key {
                return self.child[i].swap(ptr::null_mut(), Relaxed);
            }
        }
        unreachable!("key must exist")
    }
}

#[repr(C)]
#[derive(Debug)]
struct Node48 {
    header: Header,
    leaf: AtomicPtr<usize>,
    // Stores child index, negative means not exist
    key: [AtomicI8; 256],
    child: [AtomicPtr<usize>; 48],
}

impl Node48 {
    pub fn new() -> Self {
        let (key, child) = {
            let mut key: [MaybeUninit<AtomicI8>; 256] =
                unsafe { MaybeUninit::uninit().assume_init() };
            let mut child: [MaybeUninit<AtomicPtr<usize>>; 48] =
                unsafe { MaybeUninit::uninit().assume_init() };

            for i in 0..48 {
                key[i] = MaybeUninit::new(AtomicI8::new(-1));
                child[i] = MaybeUninit::new(AtomicPtr::default());
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
            leaf: AtomicPtr::default(),
        }
    }

    pub fn find_child(&self, key: &u8) -> Option<&AtomicPtr<usize>> {
        if self.key[*key as usize].load(Relaxed) >= 0 {
            return Some(&self.child[self.key[*key as usize].load(Relaxed) as usize]);
        }
        None
    }

    pub fn grow(node: &AtomicPtr<usize>) -> *mut usize {
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
                    (*new_node).child[i].store(
                        fulled_node.child[fulled_node.key[i].load(Relaxed) as usize].load(Relaxed),
                        Relaxed,
                    );
                }
            }
        }

        new_node as *mut usize
    }

    pub fn shrink(node: &AtomicPtr<usize>) -> *mut usize {
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
                        .store(empty_node.child[pos as usize].load(Relaxed), Relaxed);
                    cnt += 1;
                }
            }
            assert_eq!(cnt, 16);
        }

        new_node as *mut usize
    }

    pub fn add_child(&mut self, key: u8, child: *const usize) {
        self.child[self.header.count as usize].store(child as *mut usize, Relaxed);
        self.key[key as usize].store(self.header.count as i8, Relaxed);
        self.header.count += 1;
    }

    pub fn remove_child(&mut self, key: u8) -> *mut usize {
        self.header.count -= 1;

        let pos = self.key[key as usize].swap(-1, Relaxed);
        self.child[pos as usize].swap(ptr::null_mut(), Relaxed)
    }
}

#[repr(C)]
#[derive(Debug)]
struct Node256 {
    header: Header,
    leaf: AtomicPtr<usize>,
    child: [AtomicPtr<usize>; 256],
}

impl Node256 {
    pub fn new() -> Self {
        let child = {
            let mut child: [MaybeUninit<AtomicPtr<usize>>; 256] =
                unsafe { MaybeUninit::uninit().assume_init() };

            for i in 0..256 {
                child[i] = MaybeUninit::new(AtomicPtr::default());
            }

            unsafe { mem::transmute(child) }
        };
        Self {
            header: Header::new(NodeType::Node256),
            child,
            leaf: AtomicPtr::default(),
        }
    }

    pub fn find_child(&self, key: &u8) -> Option<&AtomicPtr<usize>> {
        if !self.child[*key as usize].load(Relaxed).is_null() {
            return Some(&self.child[*key as usize]);
        }
        None
    }

    pub fn shrink(node: &AtomicPtr<usize>) -> *mut usize {
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
                    (*new_node).child[cnt].store(empty_node.child[i].load(Relaxed), Relaxed);
                    cnt += 1;
                }
            }
            assert_eq!(cnt, 48);
        }

        new_node as *mut usize
    }

    pub fn add_child(&self, key: u8, child: *const usize) {
        self.child[key as usize].store(child as *mut usize, Relaxed);
    }

    pub fn remove_child(&mut self, key: u8) -> *mut usize {
        self.header.count -= 1;
        self.child[key as usize].swap(ptr::null_mut(), Relaxed)
    }
}

#[derive(Clone, Debug)]
#[repr(C)]
struct Header {
    node_type: NodeType,
    // item count
    count: u8,
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
        let node = Node::make_node4();
        node
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

    #[test]
    fn init() {
        let root = AtomicPtr::new(empty_node4() as *mut usize);
        Node::init(&root, &[1, 2, 3, 4], &[1, 2, 3, 4]);
        let header = Node::get_header(&root);
        debug!("header: {:?}", header);
        let result = Node::search(&root, &[1, 2, 3, 4], 0);
        debug!("result kvpair: {:?}", result.unwrap());
    }

    #[test]
    fn test_insert_expand() {
        let root = AtomicPtr::new(empty_node4() as *mut usize);
        Node::init(&root, &[1, 2, 3, 4], &[1, 2, 3, 4]);

        let kvs = vec![vec![1, 2, 1], vec![1, 2, 2], vec![1, 2, 2, 1]];

        let mut answer = HashMap::new();
        for kv in &kvs {
            debug_print_atomic(&root);
            let kvpair = KVPair::new(kv.to_owned(), kv.to_owned());
            let kvpair_ptr = Box::into_raw(Box::new(kvpair));
            answer.insert(kv.to_owned(), kvpair_ptr as *mut usize);
            let kvpair_ptr = (kvpair_ptr as usize + 1) as *mut KVPair;
            Node::insert(&root, &kv, kvpair_ptr, 0).unwrap();
        }

        for kv in kvs {
            let result = Node::search(&root, &kv, 0);
            assert_eq!(result.unwrap(), *answer.get(&kv).unwrap());
        }
    }

    #[test]
    fn test_insert_grow() {
        let root = AtomicPtr::new(empty_node4() as *mut usize);
        Node::init(&root, &[1, 1, 1, 0], &[1, 1, 1, 0]);

        let mut kvs = [[1, 1, 1, 1]; 255];
        for i in 1..=255 {
            kvs[i - 1][3] = i as u8;
        }

        let mut answer = HashMap::new();
        for kv in &kvs {
            debug_print_atomic(&root);
            let kvpair = KVPair::new(kv.to_vec(), kv.to_vec());
            let kvpair_ptr = Box::into_raw(Box::new(kvpair));
            answer.insert(kv.to_owned(), kvpair_ptr as *mut usize);
            let kvpair_ptr = (kvpair_ptr as usize + 1) as *mut KVPair;
            Node::insert(&root, kv, kvpair_ptr, 0).unwrap();
        }

        for kv in &kvs {
            let result = Node::search(&root, kv, 0);
            assert_eq!(result.unwrap(), *answer.get(kv).unwrap());
        }
    }

    #[test]
    fn test_insert_substring() {
        let root = AtomicPtr::new(empty_node4() as *mut usize);
        Node::init(&root, &[0], &[0]);
        let test_size = 100;

        let mut kvs = Vec::with_capacity(test_size);
        let mut meta = vec![0u8];
        for i in 1..test_size {
            meta.push(i as u8);
            kvs.push(meta.to_owned());
        }

        let mut answer = HashMap::new();
        for kv in &kvs {
            debug_print_atomic(&root);
            let kvpair = KVPair::new(kv.to_vec(), kv.to_vec());
            let kvpair_ptr = Box::into_raw(Box::new(kvpair));
            answer.insert(kv.to_owned(), kvpair_ptr as *mut usize);
            let kvpair_ptr = (kvpair_ptr as usize + 1) as *mut KVPair;
            Node::insert(&root, kv, kvpair_ptr, 0).unwrap();
        }

        for kv in &kvs {
            let result = Node::search(&root, kv, 0);
            assert_eq!(result.unwrap(), *answer.get(kv).unwrap());
        }
    }

    #[test]
    fn test_insert_collapse() {
        let root = AtomicPtr::new(empty_node4() as *mut usize);
        Node::init(&root, &[1], &[0]);

        let kvs = vec![
            vec![0, 0],
            vec![0, 0, 0, 0],
            vec![3, 3, 3, 3],
            vec![4, 4, 4, 4, 4],
        ];

        let mut answer = HashMap::new();
        for k in &kvs {
            let kvpair = KVPair::new(k.to_vec(), k.to_vec());
            let kvpair_ptr = Box::into_raw(Box::new(kvpair));
            answer.insert(k.to_owned(), kvpair_ptr as *mut usize);
            let kvpair_ptr = (kvpair_ptr as usize + 1) as *mut KVPair;
            Node::insert(&root, k, kvpair_ptr, 0).unwrap();
        }

        for k in &kvs {
            let result = Node::search(&root, k, 0);
            assert_eq!(result.unwrap(), *answer.get(k).unwrap());
        }
    }
}
