pub enum Node {
    Node4(Node4),
    Node16(Node16),
    Node48(Node48),
    Node256(Node256),
}

impl Node {
    pub fn find(&self, key: &[u8]) -> Option<&Self> {
        match self {
            Self::Node4(node) => {}
            Self::Node16(node) => {}
            Self::Node48(node) => {}
            Self::Node256(node) => {}
        }
        None
    }

    pub fn insert(&mut self, key: &[u8], value: u8) -> ! {
        unimplemented!()
    }

    pub fn remove(&mut self, key: &[u8]) -> ! {
        unimplemented!()
    }
}

pub enum NodeType {
    Node4,
    Node16,
    Node48,
    Node256,
}

struct Node4 {
    header: Header,
    key: [u8; 4],
    child: [u8; 4],
}

impl Node4 {
    pub fn new() -> Self {
        Self {
            header: Header::new(NodeType::Node4),
            key: [0; 4],
            child: [0; 4],
        }
    }
}

struct Node16 {
    header: Header,
    key: [u8; 16],
    child: [u8; 16],
}

impl Node16 {
    pub fn new() -> Self {
        Self {
            header: Header::new(NodeType::Node16),
            key: [0; 16],
            child: [0; 16],
        }
    }
}

struct Node48 {
    header: Header,
    key: [u8; 256],
    child: [u8; 48],
}

impl Node48 {
    pub fn new() -> Self {
        Self {
            header: Header::new(NodeType::Node48),
            key: [0; 256],
            child: [0; 48],
        }
    }
}

struct Node256 {
    header: Header,
    child: [u8; 256],
}

impl Node256 {
    pub fn new() -> Self {
        Self {
            header: Header::new(NodeType::Node256),
            child: [0; 256],
        }
    }
}

struct Header {
    node_type: NodeType,
    // item count
    count: u8,
    prefix_len: u64,
    prefix: [u8; 10],
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
