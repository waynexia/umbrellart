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
        // header.count = 1;
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
            println!("search encounted a null ptr");
            return None;
        }
        // lazy expansion
        // run out of key bytes, should reach leaf node
        if depth == key.len() {
            if Self::is_leaf_match(node, key) {
                return Some(node.load(Relaxed));
            }
            return None;
        }
        // check compressed path pessimistically
        if Self::check_prefix(node, key, depth) != Self::get_prefix_len(node) {
            println!(
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
                return Some((node.load(Relaxed) as usize - 1) as *mut usize);
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
        // assert!(!Self::is_kvpair(node));
        unsafe {
            let header = &*(node.load(Relaxed) as *mut Header);
            // Fig.: 1
            // reached a kvpair node. should insert a inner node, move kvpair to `leaf` and add 1 child.
            // this happens when old key is substring of new key.
            if Self::is_kvpair(node) {
                let new_inner_node_ptr = Self::make_node4() as *mut usize;
                let mut new_header = Self::get_header_mut(new_inner_node_ptr);
                // maybe no prefix? Todo: check this
                // for i in depth..(key.len() - 1).min(depth + MAX_PREFIX_STORED) {
                //     new_header.prefix[depth - i] = key[i];
                // }
                // new_header.prefix_len = (key.len() - 1 - depth) as u32;
                new_header.count = 1;
                let new_inner_node = &mut *(new_inner_node_ptr as *mut Node4);
                new_inner_node.leaf = Some(AtomicPtr::new(node.load(Relaxed)));
                let tmp_atomic = AtomicPtr::new(new_inner_node_ptr); // todo: remove this
                Self::add_child(&tmp_atomic, *key.last().unwrap(), leaf as *mut usize);
                // swap
                node.store(new_inner_node_ptr, Relaxed);
                return Ok(());
            }
            // ???
            // general leaf node?
            // if Self::is_kvpair(node) {
            //     let mut new_inner_node = AtomicPtr::new(Self::make_node4() as *mut usize);
            //     let new_leaf_node = Self::make_node4();
            //     // set new inner node's prefix to intersection of two keys
            //     let overlap = key.len().min(Self::get_prefix_len(node) as usize);
            //     for i in 0..overlap {
            //         Self::get_header_mut(new_inner_node.load(Relaxed) as *mut usize).prefix[i] =
            //             key[i + depth];
            //     }
            //     // todo: what if prefix_len > Max_stored_prefix?
            //     // todo: need to adjust prefix for node and new_leaf_node?
            //     Self::get_header_mut(new_inner_node.load(Relaxed) as *mut usize).prefix_len =
            //         overlap as u32;
            //     Self::add_child(&new_inner_node, key[depth], new_leaf_node as *const usize);
            //     Self::add_child(
            //         &new_inner_node,
            //         Self::load_prefix(node).unwrap()[depth], //?
            //         node.load(Relaxed) as *const usize,
            //     );
            //     // todo: atomic swap node and new_inner_node
            //     // node and other pointers should be AtomicPtr
            //     return Ok(());
            // }
            let p = Self::check_prefix(node, key, depth);
            println!("got prefix length {} with key {:?}", p, key);
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

                // let new_leaf_node = Self::make_node4() as *mut usize;
                // Self::add_child(&new_inner_node, key[depth + p as usize], new_leaf_node);
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
                if Self::is_full(node) {
                    Self::grow(&node);
                }
                // let new_leaf_node = Self::make_node4();
                Self::add_child(node, key[depth], leaf as *mut usize);
            }
            return Ok(());
        }
    }

    pub fn remove(&mut self, key: &[u8]) -> ! {
        unimplemented!()
    }
}

impl Node {
    fn is_leaf_match(node: &AtomicPtr<usize>, key: &[u8]) -> bool {
        if Self::is_kvpair(node) {
            Self::to_kvpair(node).key.as_slice() == key
        } else {
            let node4 = Self::to_node4(node);
            if let Some(leaf_ptr) = &node4.leaf {
                Self::to_kvpair(leaf_ptr).key.as_slice() == key
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
struct Node4 {
    header: Header,
    leaf: Option<AtomicPtr<usize>>,
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
            leaf: None,
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
    leaf: Option<AtomicPtr<usize>>,
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
            leaf: None,
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
    leaf: Option<AtomicPtr<usize>>,
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
            leaf: None,
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
    leaf: Option<AtomicPtr<usize>>,
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
            leaf: None,
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

    fn debug_print(node_ptr: *mut usize) {
        unsafe {
            match (node_ptr as *mut Header).as_ref().unwrap().node_type {
                NodeType::Node4 => {
                    let node = (node_ptr as *mut Node4).as_ref().unwrap();
                    println!("got a node4, header: {:?}", node.header);
                    println!("with key/values:\nkeys: ");
                    for i in 0..4 {
                        print!("No.{}: {}, ", i, node.key[i].load(Relaxed));
                    }
                    println!("\nvalues: ");
                    for i in 0..4 {
                        print!("No.{}: {:?}, ", i, node.child[i].load(Relaxed));
                    }
                    println!();
                } // NodeType::Node16 => {
                //     println!("got a node16");
                //     todo!()
                // }
                // NodeType::Node48 => {
                //     println!("got a node48");
                //     todo!()
                // }
                // NodeType::Node256 => {
                //     println!("got a node256");
                //     todo!()
                // }
                _ => todo!("got pointer {:?}", node_ptr),
            }
        }
    }

    fn debug_print_atomic(node: &AtomicPtr<usize>) {
        debug_print(node.load(Relaxed));
    }

    #[ignore]
    #[test]
    fn init() {
        let root = AtomicPtr::new(empty_node4() as *mut usize);
        Node::init(&root, &[1, 2, 3, 4], &[1, 2, 3, 4]);
        // Node::insert(&root, &[1], 1, &0);
        let header = Node::get_header(&root);
        println!("header: {:?}", header);
        let result = Node::search(&root, &[1, 2, 3, 4], 0);
        println!("result kvpair: {:?}", result.unwrap());
    }

    #[test]
    fn test_insert_expand() {
        let root = AtomicPtr::new(empty_node4() as *mut usize);
        Node::init(&root, &[1, 2, 3, 4], &[1, 2, 3, 4]);

        let kvs = vec![vec![1, 2, 1], vec![1, 2, 2], vec![1, 2, 2, 1]];
        for kv in &kvs {
            println!("root addr: {:?}", root.load(Relaxed));
            debug_print_atomic(&root);
            let kvpair = KVPair::new(kv.to_owned(), kv.to_owned());
            let kvpair_ptr = (Box::into_raw(Box::new(kvpair)) as usize + 1) as *mut KVPair;
            Node::insert(&root, &kv, kvpair_ptr, 0).unwrap();
            println!();
        }

        println!("insert finished");

        for kv in kvs {
            let result = Node::search(&root, &kv, 0);
            println!("search {:?}, got result: {:?}", kv, result.unwrap())
        }
    }
}
