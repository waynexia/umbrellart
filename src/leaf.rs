use crate::node::{Header, NodePtr, NodeType};

#[repr(C)]
#[derive(Debug)]
pub(crate) struct NodeLeaf {
    header: Header,
    key: Vec<u8>,
    value: NodePtr,
}

impl NodeLeaf {
    const TYPE: NodeType = NodeType::Leaf;

    pub fn new(key: Vec<u8>, value: NodePtr) -> Self {
        let (header, key) = if key.len() <= Header::MAX_PREFIX_STORED {
            // inline short key into header
            (Header::with_prefix(NodeType::Leaf, &key), vec![])
        } else {
            (Header::new(NodeType::Leaf), key)
        };

        Self { header, key, value }
    }

    /// Panic if the pointer is invalid.
    pub unsafe fn from_node_ptr(ptr: NodePtr) -> Self {
        let node_type = ptr.try_as_header().unwrap().node_type();
        assert_eq!(node_type, Self::TYPE);

        Box::into_inner(Box::from_raw(ptr.0 as *const Self as *mut Self))
    }

    pub fn load_key(&self) -> Option<Vec<u8>> {
        Some(self.load_key_ref().to_owned())
    }

    fn load_key_ref(&self) -> &[u8] {
        if self.header.prefix_len() != 0 {
            self.header.prefix()
        } else {
            &self.key
        }
    }

    /// Calculate the common key parts from bias. Bytes before bias won't
    /// be considered.
    pub fn get_common_key(&self, other: &NodeLeaf, bias: usize) -> &[u8] {
        let mut index = bias;

        let lhs_key = self.load_key_ref();
        let rhs_key = other.load_key_ref();
        let len = lhs_key.len().min(rhs_key.len());

        while index < len {
            if lhs_key[index] == rhs_key[index] {
                index += 1;
            } else {
                break;
            }
        }

        &lhs_key[bias..bias + index]
    }
}

// todo: impl Drop for NodeLeaf
