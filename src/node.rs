#[allow(unused_variables)]
use std::cmp::Ordering;
use std::mem::{self, MaybeUninit};
use std::ptr;
use std::sync::atomic::Ordering::{Relaxed, SeqCst};
use std::sync::atomic::{AtomicI8, AtomicPtr, AtomicU8};
use std::sync::Arc;

type PrefixCount = u32;
const MAX_PREFIX_STORED: usize = 10;
type K = usize;
type V = usize;

pub enum Node {
    Node4(Node4),
    Node16(Node16),
    Node48(Node48),
    Node256(Node256),
}

impl Node {
    pub fn search(&self, key: &[u8], depth: &usize) -> Option<&Self> {
        // lazy expansion
        if self.is_leaf() {
            if self.leaf_match(key, depth) {
                return Some(&self);
            }
            return None;
        }
        // check compressed path pessimistically
        if self.check_prefix(key, depth) != self.get_prefix_len() {
            return None;
        }
        // step
        let depth: &usize = &(depth + *self.get_prefix_len() as usize);
        let next = self.find_child(&key[*depth])?;
        return next.search(key, &(depth + 1));
    }

    pub fn insert(node: AtomicPtr<usize>, key: &[u8], value: u8, depth: &usize) -> Result<(), ()> {
        unsafe {
            let node_ref = &*(node.load(Relaxed) as *mut Node);
            if node_ref.is_leaf() {
                let mut new_inner_node = Self::make_node4();
                let new_leaf_node = Self::make_node4();
                // set new inner node's prefix to intersection of two keys
                let overlap = key.len().min(node_ref.load_key().unwrap().len());
                for i in 0..overlap {
                    new_inner_node.get_header_mut().prefix[i] = key[i + depth];
                }
                // todo: what if prefix_len > Max_stored_prefix?
                // todo: need to adjust prefix for node and new_leaf_node?
                new_inner_node.get_header_mut().prefix_len = overlap as u32;
                new_inner_node.add_child(key[*depth], &new_leaf_node);
                new_inner_node.add_child(
                    node_ref.load_key().unwrap()[*depth],
                    node.load(Relaxed) as *const Node,
                );
                // todo: atomic swap node and new_inner_node
                // node and other pointers should be AtomicPtr
                return Ok(());
            }
            let p = node_ref.check_prefix(key, depth);
            if p != node_ref.get_prefix_len() {
                // make a copy of node and modify it,
                // construct new inner node and replace node
                let mut node_substitute: Node = mem::transmute_copy(node_ref);
                let mut new_inner_node = Self::make_node4();
                let new_leaf_node = Self::make_node4();
                let node_prefix = node_ref.get_header().prefix;
                new_inner_node.add_child(key[depth + *p as usize], &new_leaf_node);
                new_inner_node.add_child(node_prefix[*p as usize], &node_substitute);
                ptr::copy_nonoverlapping(
                    &node_prefix,
                    &mut new_inner_node.get_header_mut().prefix,
                    mem::size_of::<[u8; MAX_PREFIX_STORED]>(),
                );
                node_substitute.get_header_mut().prefix_len -= p + 1;
                ptr::copy(
                    &node_substitute.get_header().prefix,
                    &mut node_substitute.get_header_mut().prefix,
                    *node_substitute.get_prefix_len() as usize,
                );
                // todo: atomic swap node and new_inner_node
                return Ok(());
            }

            let depth = depth + *node_ref.get_prefix_len() as usize;
            if let Some(next_node) = node_ref.find_child(&key[depth]) {
                Self::insert(*next_node, key, value, &(depth + 1))?;
            } else {
                if node_ref.is_full() {
                    Self::grow(&node);
                }
                let new_leaf_node = Self::make_node4();
                node_ref.add_child(key[depth], &new_leaf_node);
            }
            return Ok(());
        }
    }

    pub fn remove(&mut self, key: &[u8]) -> ! {
        unimplemented!()
    }
}

impl Node {
    fn is_leaf(&self) -> bool {
        // self.get_header().node_type != NodeType::Inner
        todo!()
    }

    // fully check stored key
    fn leaf_match(&self, key: &[u8], _depth: &usize) -> bool {
        // match &self.get_header().node_type {
        //     NodeType::Leaf(stored_key) => stored_key.as_slice() == key,
        //     NodeType::Inner => false,
        // }
        todo!()
    }

    fn check_prefix(&self, key: &[u8], depth: &usize) -> &PrefixCount {
        let header = self.get_header();
        let overlap = key
            .len()
            .min(header.prefix_len as usize)
            .min(MAX_PREFIX_STORED);
        for i in 0..overlap {
            if key[i] != header.prefix[i] {
                // not match
                return &0;
            }
        }
        &header.prefix_len
    }

    fn get_prefix_len(&self) -> &PrefixCount {
        &self.get_header().prefix_len
    }

    fn find_child(&self, key_byte: &u8) -> Option<&AtomicPtr<usize>> {
        match self {
            Node::Node4(node) => node.find_child(key_byte),
            Node::Node16(node) => node.find_child(key_byte),
            Node::Node48(node) => node.find_child(key_byte),
            Node::Node256(node) => node.find_child(key_byte),
        }
    }

    fn get_header(&self) -> &Header {
        match self {
            Node::Node4(node) => &node.header,
            Node::Node16(node) => &node.header,
            Node::Node48(node) => &node.header,
            Node::Node256(node) => &node.header,
        }
    }

    fn get_header_mut(&mut self) -> &mut Header {
        match self {
            Node::Node4(node) => &mut node.header,
            Node::Node16(node) => &mut node.header,
            Node::Node48(node) => &mut node.header,
            Node::Node256(node) => &mut node.header,
        }
    }

    fn load_key(&self) -> Option<&[u8]> {
        // match &self.get_header().node_type {
        //     NodeType::Inner => None,
        //     NodeType::Leaf(key) => Some(&key),
        // }
        todo!()
    }

    // todo: SIMD
    // todo: order-preserving
    fn add_child(&self, key: u8, child: *const Node) {
        todo!()
    }

    fn is_full(&self) -> bool {
        self.get_header().count
            > match self {
                Node::Node4(_) => 3,
                Node::Node16(_) => 15,
                Node::Node48(_) => 47,
                // Node 256 won't full
                Node::Node256(_) => 255,
            }
    }

    // create a new larger node, copy header, child (and key)
    // to it and atomic replace old node
    fn grow(node: &AtomicPtr<usize>) {
        let grown = unsafe {
            match (*(node.load(Relaxed) as *const Header)).node_type {
                NodeType::Node4 => Node4::grow(&node),
                NodeType::Node16 => Node16::grow(&node),
                NodeType::Node48 => Node48::grow(&node),
                NodeType::Node256 => unreachable!("Node256 cannot grow"),
            }
        };

        node.store(grown as *mut usize, Relaxed);
    }
}

impl Node {
    fn make_node4() -> Self {
        Self::Node4(Node4::new())
    }
}

#[derive(Clone, PartialEq)]
pub enum NodeType {
    Node4,
    Node16,
    Node48,
    Node256,
}

pub struct KVPair<K, V> {
    pub key: K,
    pub value: V,
}

#[repr(C)]
struct Node4 {
    header: Header,
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
        }
    }

    pub fn find_child(&self, key: &u8) -> Option<&AtomicPtr<usize>> {
        for i in 0..self.header.count as usize {
            if &self.key[i].load(Relaxed) == key {
                unsafe {
                    return Some(&self.child[i]);
                }
            }
        }
        None
    }

    pub fn grow(node: &AtomicPtr<usize>) -> *const Node {
        let mut new_node = Node16::new();
        let fulled_node = unsafe { &*(node.load(Relaxed) as *const Node4) };

        // copy header
        unsafe {
            ptr::copy_nonoverlapping(
                &fulled_node.header,
                &mut new_node.header,
                mem::size_of::<Header>(),
            );
        }

        // key & child field
        for i in 0..4 {
            new_node.key[i].store(fulled_node.key[i].load(Relaxed), Relaxed);
            new_node.child[i].store(fulled_node.child[i].load(Relaxed), Relaxed);
        }

        &Node::Node16(new_node) as *const Node
    }

    pub fn add_child(&self, key: u8, child: *const Node) {
        self.key[self.header.count as usize].store(key, Relaxed);
        self.child[self.header.count as usize].store(child as *mut usize, Relaxed);
    }
}

#[repr(C)]
struct Node16 {
    header: Header,
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
        }
    }

    pub fn find_child(&self, key: &u8) -> Option<&AtomicPtr<usize>> {
        // todo: use SIMD or binary search
        for i in 0..self.header.count as usize {
            if &self.key[i].load(Relaxed) == key {
                unsafe {
                    return Some(&self.child[i]);
                }
            }
        }
        None
    }

    pub fn grow(node: &AtomicPtr<usize>) -> *const Node {
        let mut new_node = Node48::new();
        let fulled_node = unsafe { &*(node.load(Relaxed) as *const Node4) };

        // copy header
        unsafe {
            ptr::copy_nonoverlapping(
                &fulled_node.header,
                &mut new_node.header,
                mem::size_of::<Header>(),
            );
        }

        // key & child field
        for i in 0..16 {
            new_node.child[i].store(fulled_node.child[i].load(Relaxed), Relaxed);
            new_node.key[fulled_node.key[i].load(Relaxed) as usize].store(i as i8, Relaxed);
        }

        &Node::Node48(new_node) as *const Node
    }
}

#[repr(C)]
struct Node48 {
    header: Header,
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
                key[i] = MaybeUninit::new(AtomicI8::default());
                child[i] = MaybeUninit::new(AtomicPtr::default());
            }
            for i in 48..256 {
                key[i] = MaybeUninit::new(AtomicI8::default());
            }

            unsafe { (mem::transmute(key), mem::transmute(child)) }
        };
        Self {
            header: Header::new(NodeType::Node48),
            key,
            child,
        }
    }

    pub fn find_child(&self, key: &u8) -> Option<&AtomicPtr<usize>> {
        if self.key[*key as usize].load(Relaxed) >= 0 {
            unsafe {
                return Some(
                    // (self.child[self.key[*key as usize].load(Relaxed) as usize].load(Relaxed)
                    //     as *const Node)
                    //     .as_ref()
                    //     .unwrap(),
                    &self.child[self.key[*key as usize].load(Relaxed) as usize],
                );
            }
        }
        None
    }

    pub fn grow(node: &AtomicPtr<usize>) -> *const Node {
        let mut new_node = Node256::new();
        let fulled_node = unsafe { &*(node.load(Relaxed) as *const Node4) };

        // copy header
        unsafe {
            ptr::copy_nonoverlapping(
                &fulled_node.header,
                &mut new_node.header,
                mem::size_of::<Header>(),
            );
        }

        // child field
        for i in 0..=255 {
            if fulled_node.key[i].load(Relaxed) >= 0 {
                new_node.child[i].store(
                    fulled_node.child[fulled_node.key[i].load(Relaxed) as usize].load(Relaxed),
                    Relaxed,
                );
            }
        }

        &Node::Node256(new_node) as *const Node
    }
}

#[repr(C)]
struct Node256 {
    header: Header,
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
        }
    }

    pub fn find_child(&self, key: &u8) -> Option<&AtomicPtr<usize>> {
        if !self.child[*key as usize].load(Relaxed).is_null() {
            unsafe {
                return Some(
                    // (self.child[*key as usize].load(Relaxed) as *const Node)
                    //     .as_ref()
                    //     .unwrap(),
                    &self.child[*key as usize],
                );
            }
        }
        None
    }
}

#[derive(Clone)]
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
}
