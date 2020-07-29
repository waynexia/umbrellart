use std::cmp::Ordering;
use std::mem;
use std::ptr;

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

    pub fn insert(node: *const Node, key: &[u8], value: u8, depth: &usize) -> Result<(), ()> {
        unsafe {
            let node_ref = node.as_ref().unwrap();
            if node_ref.is_leaf() {
                let mut new_inner_node = Self::make_node4(NodeType::Inner);
                let new_leaf_node = Self::make_node4(NodeType::Leaf(key.to_owned()));
                // set new inner node's prefix to intersection of two keys
                let overlap = key.len().min(node_ref.load_key().unwrap().len());
                for i in 0..overlap {
                    new_inner_node.get_header_mut().prefix[i] = key[i + depth];
                }
                // todo: what if prefix_len > Max_stored_prefix?
                // todo: need to adjust prefix for node and new_leaf_node?
                new_inner_node.get_header_mut().prefix_len = overlap as u32;
                new_inner_node.add_child(key[*depth], &new_leaf_node);
                new_inner_node.add_child(node_ref.load_key().unwrap()[*depth], node);
                // todo: atomic swap node and new_inner_node
                // node and other pointers should be AtomicPtr
                return Ok(());
            }
            let p = node_ref.check_prefix(key, depth);
            if p != node_ref.get_prefix_len() {
                // make a copy of node and do modification on it,
                // construct new inner node and replace node
                let mut node_substitute: Node = mem::transmute_copy(node_ref);
                let mut new_inner_node = Self::make_node4(NodeType::Inner);
                let new_leaf_node = Self::make_node4(NodeType::Leaf(key.to_owned()));
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
                Self::insert(next_node, key, value, &(depth + 1))?;
            } else {
                if node_ref.is_full() {
                    Self::grow(node);
                }
                let new_leaf_node = Self::make_node4(NodeType::Leaf(key.to_owned()));
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
        self.get_header().node_type != NodeType::Inner
    }

    // fully check stored key
    fn leaf_match(&self, key: &[u8], _depth: &usize) -> bool {
        match &self.get_header().node_type {
            NodeType::Leaf(stored_key) => stored_key.as_slice() == key,
            NodeType::Inner => false,
        }
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

    fn find_child(&self, key_byte: &u8) -> Option<&Self> {
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
        match &self.get_header().node_type {
            NodeType::Inner => None,
            NodeType::Leaf(key) => Some(&key),
        }
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
    fn grow(node: *const Node) {
        let grown = unsafe {
            match &*node {
                Node::Node4(node) => Node4::grow(&node),
                Node::Node16(node) => Node16::grow(&node),
                Node::Node48(node) => Node48::grow(&node),
                Node::Node256(_) => unreachable!("Node256 cannot grow"),
            }
        };

        // todo: atomic swap node with grown node
    }
}

impl Node {
    fn make_node4(node_type: NodeType) -> Self {
        Self::Node4(Node4::new(node_type))
    }
}

#[derive(Clone, PartialEq)]
pub enum NodeType {
    Inner,
    Leaf(Vec<u8>),
}

struct Node4 {
    header: Header,
    key: [u8; 4],
    child: [*const usize; 4],
}

impl Node4 {
    pub fn new(node_type: NodeType) -> Self {
        Self {
            header: Header::new(node_type),
            key: [0; 4],
            child: [&0; 4],
        }
    }

    pub fn find_child(&self, key: &u8) -> Option<&Node> {
        for i in 0..self.header.count as usize {
            if &self.key[i] == key {
                unsafe {
                    return Some((self.child[i] as *const Node).as_ref().unwrap());
                }
            }
        }
        None
    }

    pub fn grow(node: &Node4) -> *const Node {
        let mut new_node = Node16::new(NodeType::Inner);

        // copy header
        unsafe {
            ptr::copy_nonoverlapping(&node.header, &mut new_node.header, mem::size_of::<Header>());
        }

        // key & child field
        for i in 0..4 {
            new_node.key[i] = node.key[i];
            new_node.child[i] = node.child[i];
        }

        &Node::Node16(new_node) as *const Node
    }
}

impl Node4 {
    fn find(&self, key: &[u8]) -> Option<*const Node> {
        match key.len().cmp(&(self.header.prefix_len as usize)) {
            Ordering::Less | Ordering::Equal => {
                return None;
            }
            Ordering::Greater => {
                for i in 0..self.header.prefix_len as usize {
                    if key[i] != self.header.prefix[i] {
                        return None;
                    }
                }
                // find in keys
                let key_byte = key[self.header.prefix_len as usize];
                for i in 0..self.header.count as usize {
                    if key_byte == self.key[i] {
                        return Some(self.child[i] as *const Node);
                    }
                }
                return None;
            }
        }
    }

    fn insert(
        &mut self,
        key: &[u8],
        value: *const usize,
        parent: *mut usize,
        parent_index: &usize,
    ) -> Result<(), ()> {
        // ignore collapsing

        // overflow
        if self.header.count == 4 {
            let mut new_node = mem::ManuallyDrop::new(Box::new(Node16::new(NodeType::Inner)));
            (*new_node).header = self.header.clone();
            (*new_node).header.count += 1;
            for i in 0..self.header.count as usize {
                (*new_node).key[i] = self.key[i];
                (*new_node).child[i] = self.child[i];
            }
            // todo: find propriate place (index)
            let new_index = 0;
            (*new_node).key[new_index] = key[0];
            (*new_node).child[new_index] = value;

            unsafe {
                (*(parent as *mut Node4)).child[*parent_index] =
                    Box::into_raw(mem::ManuallyDrop::into_inner(new_node)) as *const usize;
            }
        } else {
            // todo: find propriate place (index)
            let new_index = 0;
            self.key[new_index] = key[0];
        }

        Ok(())
    }

    fn delete(&mut self, key: &[u8]) -> Result<(), ()> {
        // ignore collapsing

        // todo find propriate place (index)
        let delete_index = 0;
        self.key
            .copy_within(delete_index..self.header.count as usize, delete_index);
        self.child
            .copy_within(delete_index..self.header.count as usize, delete_index);

        Ok(())
    }
}

struct Node16 {
    header: Header,
    key: [u8; 16],
    child: [*const usize; 16],
}

impl Node16 {
    pub fn new(node_type: NodeType) -> Self {
        Self {
            header: Header::new(node_type),
            key: [0; 16],
            child: [&0; 16],
        }
    }

    pub fn find_child(&self, key: &u8) -> Option<&Node> {
        // todo: use SIMD or binary search
        for i in 0..self.header.count as usize {
            if &self.key[i] == key {
                unsafe {
                    return Some((self.child[i] as *const Node).as_ref().unwrap());
                }
            }
        }
        None
    }

    pub fn grow(node: &Node16) -> *const Node {
        let mut new_node = Node48::new(NodeType::Inner);

        // copy header
        unsafe {
            ptr::copy_nonoverlapping(&node.header, &mut new_node.header, mem::size_of::<Header>());
        }

        // key & child field
        for i in 0..16 {
            new_node.child[i] = node.child[i];
            new_node.key[node.key[i] as usize] = i as i8;
        }

        &Node::Node48(new_node) as *const Node
    }
}

struct Node48 {
    header: Header,
    // Stores child index, negative means not exist
    key: [i8; 256],
    child: [*const usize; 48],
}

impl Node48 {
    pub fn new(node_type: NodeType) -> Self {
        Self {
            header: Header::new(node_type),
            key: [-1; 256],
            child: [&0; 48],
        }
    }

    pub fn find_child(&self, key: &u8) -> Option<&Node> {
        if self.key[*key as usize] >= 0 {
            unsafe {
                return Some(
                    (self.child[self.key[*key as usize] as usize] as *const Node)
                        .as_ref()
                        .unwrap(),
                );
            }
        }
        None
    }

    pub fn grow(node: &Node48) -> *const Node {
        let mut new_node = Node256::new(NodeType::Inner);

        // copy header
        unsafe {
            ptr::copy_nonoverlapping(&node.header, &mut new_node.header, mem::size_of::<Header>());
        }

        // child field
        for i in 0..=255 {
            if node.key[i] >= 0 {
                new_node.child[i] = node.child[node.key[i] as usize];
            }
        }

        &Node::Node256(new_node) as *const Node
    }
}

struct Node256 {
    header: Header,
    child: [*const usize; 256],
}

impl Node256 {
    pub fn new(node_type: NodeType) -> Self {
        Self {
            header: Header::new(node_type),
            child: [&0; 256],
        }
    }

    pub fn find_child(&self, key: &u8) -> Option<&Node> {
        if !self.child[*key as usize].is_null() {
            unsafe {
                return Some((self.child[*key as usize] as *const Node).as_ref().unwrap());
            }
        }
        None
    }
}

#[derive(Clone)]
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
