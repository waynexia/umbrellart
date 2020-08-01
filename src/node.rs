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

pub struct Node {}

impl Node {
    pub fn init(node: &AtomicPtr<usize>, key: &[u8], value: &[u8]) {
        let mut header = Self::get_header_mut(node.load(Relaxed));
        assert!(header.count == 0);
        header.count = 1;
        header.prefix_len = key.len() as u32;
        for i in 0..key.len().min(MAX_PREFIX_STORED) {
            header.prefix[i] = key[i];
        }
        let kvpair = KVPair::new(key.to_owned(), value.to_owned());
        let kvpair_ptr = Box::into_raw(Box::new(kvpair));
        Self::add_child(node, key[key.len() - 1], kvpair_ptr as *mut usize);
    }

    pub fn search(
        node: &'static AtomicPtr<usize>,
        key: &[u8],
        depth: &usize,
    ) -> Option<&'static AtomicPtr<usize>> {
        if node.load(Relaxed).is_null() {
            return None;
        }
        // lazy expansion
        if Self::is_leaf(node) {
            if Self::leaf_match(node, key, depth) {
                return Some(node);
            }
            return None;
        }
        // check compressed path pessimistically
        if Self::check_prefix(node, key, depth) != Self::get_prefix_len(node) {
            return None;
        }
        // step
        let depth: &usize = &(depth + Self::get_prefix_len(node) as usize);
        let next = Self::find_child(node, &key[*depth])?;
        return Self::search(next, key, &(depth + 1));
    }

    pub fn insert<'a>(
        node: &'a AtomicPtr<usize>,
        key: &[u8],
        value: u8,
        depth: &usize,
    ) -> Result<(), ()> {
        assert!(!Self::is_leaf(node));
        unsafe {
            let header = &*(node.load(Relaxed) as *mut Header);
            if Self::is_leaf(node) {
                let mut new_inner_node = AtomicPtr::new(Self::make_node4() as *mut usize);
                let new_leaf_node = Self::make_node4();
                // set new inner node's prefix to intersection of two keys
                let overlap = key.len().min(Self::get_prefix_len(node) as usize);
                for i in 0..overlap {
                    Self::get_header_mut(new_inner_node.load(Relaxed) as *mut usize).prefix[i] =
                        key[i + depth];
                }
                // todo: what if prefix_len > Max_stored_prefix?
                // todo: need to adjust prefix for node and new_leaf_node?
                Self::get_header_mut(new_inner_node.load(Relaxed) as *mut usize).prefix_len =
                    overlap as u32;
                Self::add_child(&new_inner_node, key[*depth], new_leaf_node as *const usize);
                Self::add_child(
                    &new_inner_node,
                    Self::load_prefix(node).unwrap()[*depth], //?
                    node.load(Relaxed) as *const usize,
                );
                // todo: atomic swap node and new_inner_node
                // node and other pointers should be AtomicPtr
                return Ok(());
            }
            let p = Self::check_prefix(node, key, depth);
            // todo: replace hard coded "Node4"
            if p != Self::get_prefix_len(node) {
                // make a copy of node and modify it,
                // construct new inner node and replace node
                let mut node_substitute: &Node4 =
                    &mem::transmute_copy(&*(node.load(Relaxed) as *const Node4)); // ?
                let mut new_inner_node = AtomicPtr::new(Self::make_node4() as *mut usize);
                let new_leaf_node = Self::make_node4() as *mut usize;
                let node_prefix = Self::get_header(node).prefix;
                Self::add_child(&new_inner_node, key[depth + p as usize], new_leaf_node);
                Self::add_child(
                    &new_inner_node,
                    node_prefix[p as usize],
                    node_substitute as *const Node4 as *mut usize,
                );
                ptr::copy_nonoverlapping(
                    &node_prefix,
                    &mut Self::get_header_mut(new_inner_node.load(Relaxed)).prefix,
                    mem::size_of::<[u8; MAX_PREFIX_STORED]>(),
                );
                Self::get_header_mut(node_substitute as *const Node4 as *mut usize).prefix_len -=
                    p + 1;
                ptr::copy(
                    &Self::get_header(&AtomicPtr::new(
                        node_substitute as *const Node4 as *mut usize,
                    ))
                    .prefix,
                    &mut Self::get_header_mut(node_substitute as *const Node4 as *mut usize).prefix,
                    Self::get_prefix_len(&AtomicPtr::new(
                        node_substitute as *const Node4 as *mut usize,
                    )) as usize,
                );
                // todo: atomic swap node and new_inner_node
                return Ok(());
            }

            let depth = depth + Self::get_prefix_len(node) as usize;
            if let Some(next_node) = Self::find_child(node, &key[depth]) {
                Self::insert(next_node, key, value, &(depth + 1))?;
            } else {
                if Self::is_full(node) {
                    Self::grow(&node);
                }
                let new_leaf_node = Self::make_node4();
                Self::add_child(node, key[depth], new_leaf_node as *mut usize);
            }
            return Ok(());
        }
    }

    pub fn remove(&mut self, key: &[u8]) -> ! {
        unimplemented!()
    }
}

impl Node {
    // tagged pointer
    fn is_leaf(node: &AtomicPtr<usize>) -> bool {
        node.load(Relaxed) as usize % 2 == 1
    }

    // fully check stored key
    fn leaf_match(node: &AtomicPtr<usize>, key: &[u8], _depth: &usize) -> bool {
        assert!(Self::is_leaf(node));

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
    fn check_prefix(node: &AtomicPtr<usize>, key: &[u8], depth: &usize) -> PrefixCount {
        assert!(!Self::is_leaf(node));

        let header = unsafe { &*(node.load(Relaxed) as *const Header) };
        for i in 0..key
            .len()
            .min(header.prefix_len as usize)
            .min(MAX_PREFIX_STORED)
        {
            if header.prefix[i] != key[depth + i] {
                return 0;
            }
        }
        return header.prefix_len;
    }

    fn get_prefix_len(node: &AtomicPtr<usize>) -> PrefixCount {
        assert!(!Self::is_leaf(node));

        unsafe { (*(node.load(Relaxed) as *const Header)).prefix_len }
    }

    fn find_child<'a>(
        node_ptr: &'a AtomicPtr<usize>,
        key_byte: &u8,
    ) -> Option<&'a AtomicPtr<usize>> {
        assert!(!Self::is_leaf(node_ptr));

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
        assert!(!Self::is_leaf(node));

        unsafe { &*(node.load(Relaxed) as *const Header) }
    }

    fn get_header_mut<'a>(node: *mut usize) -> &'a mut Header {
        // assert!(!Self::is_leaf(node));

        // &mut unsafe { *(node.load(Relaxed) as *mut Header) }
        unsafe { &mut *(node as *mut Header) }
    }

    fn load_prefix(node: &AtomicPtr<usize>) -> Option<&[u8]> {
        assert!(!Self::is_leaf(node));

        Some(&Self::get_header(node).prefix)
    }

    // todo: SIMD
    // todo: order-preserving
    fn add_child(node_ptr: &AtomicPtr<usize>, key_byte: u8, child: *const usize) {
        assert!(!Self::is_leaf(node_ptr));

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

    fn is_full(node: &AtomicPtr<usize>) -> bool {
        let header = Self::get_header(node);
        header.count
            > match header.node_type {
                NodeType::Node4 => 3,
                NodeType::Node16 => 15,
                NodeType::Node48 => 47,
                // Node 256 won't full
                NodeType::Node256 => 255,
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
}

impl Node {
    fn make_node4() -> *mut Node4 {
        // Self::Node4(Node4::new())
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

    pub fn grow(node: &AtomicPtr<usize>) -> *mut usize {
        let mut new_node = Box::into_raw(Box::new(Node16::new()));
        let fulled_node = unsafe { &*(node.load(Relaxed) as *const Node4) };

        // copy header
        unsafe {
            ptr::copy_nonoverlapping(
                &fulled_node.header,
                &mut (*new_node).header,
                mem::size_of::<Header>(),
            );

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

    pub fn grow(node: &AtomicPtr<usize>) -> *mut usize {
        let mut new_node = Box::into_raw(Box::new(Node48::new()));
        let fulled_node = unsafe { &*(node.load(Relaxed) as *const Node4) };

        // copy header
        unsafe {
            ptr::copy_nonoverlapping(
                &fulled_node.header,
                &mut (*new_node).header,
                mem::size_of::<Header>(),
            );

            // key & child field
            for i in 0..16 {
                (*new_node).child[i].store(fulled_node.child[i].load(Relaxed), Relaxed);
                (*new_node).key[fulled_node.key[i].load(Relaxed) as usize].store(i as i8, Relaxed);
            }
        }

        new_node as *mut usize
    }

    pub fn add_child(&self, key: u8, child: *const usize) {
        self.key[self.header.count as usize].store(key, Relaxed);
        self.child[self.header.count as usize].store(child as *mut usize, Relaxed);
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

    pub fn grow(node: &AtomicPtr<usize>) -> *mut usize {
        let mut new_node = Box::into_raw(Box::new(Node256::new()));
        let fulled_node = unsafe { &*(node.load(Relaxed) as *const Node4) };

        // copy header
        unsafe {
            ptr::copy_nonoverlapping(
                &fulled_node.header,
                &mut (*new_node).header,
                mem::size_of::<Header>(),
            );

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

    pub fn add_child(&self, key: u8, child: *const usize) {
        todo!()
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
            return Some(
                // (self.child[*key as usize].load(Relaxed) as *const Node)
                //     .as_ref()
                //     .unwrap(),
                &self.child[*key as usize],
            );
        }
        None
    }

    pub fn add_child(&self, key: u8, child: *const usize) {
        todo!()
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
}

#[cfg(test)]
mod test {
    use super::*;

    fn empty_node4() -> *mut Node4 {
        let node = Node::make_node4();
        // let header = Node::get_header_mut(node);
        node
    }

    #[test]
    fn basic_flow() {
        let root = AtomicPtr::new(empty_node4() as *mut usize);
        Node::init(&root, &[1, 2, 3, 4], &[1, 2, 3, 4]);
        // Node::insert(&root, &[1], 1, &0);
        let header = Node::get_header(&root);
        println!("header: {:?}", header);
    }
}
