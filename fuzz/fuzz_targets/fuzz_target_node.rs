#![no_main]
use fuzz_common::NodeOperation;
use libfuzzer_sys::fuzz_target;
use umbrellart::{KVPair, Node, NodeRef};

use std::collections::HashMap;

// copied from node.rs/test
pub unsafe fn from_tagged_ptr(node_ref: &NodeRef) -> *mut KVPair {
    let ptr = **node_ref;
    debug_assert!(ptr as usize % 2 == 1);
    (ptr as usize - 1) as *mut usize as _
}

// fuzz_target!(|operations: Vec<NodeOperation>| {
//     let root = AtomicPtr::new(Node::make_node4() as *mut usize);
//     Node::init(&root, &[1], &[0]);
//     let mut answer = HashMap::new();

//     for operation in operations {
//         match operation {
//             NodeOperation::Insert { key, value } => {
//                 answer.insert(key.clone(), value.clone());
//                 let kvpair = KVPair::new(key.clone(), value).into_raw();
//                 Node::insert(&root, key.as_slice(), kvpair, 0).unwrap();
//             }
//             NodeOperation::Remove { remove_exist, key } => {
//                 let key = if remove_exist && !answer.is_empty() {
//                     answer.keys().next().unwrap().clone()
//                 } else {
//                     key
//                 };
//                 let expected = answer.remove(&key);
//                 let result = Node::remove(&root, &key, 0)
//                     .map(|ptr| unsafe { &*(ptr as *mut KVPair) })
//                     .map(|kvpair| kvpair.value.clone());
//                 assert_eq!(&result, &expected);
//             }
//         }
//     }
// });

// Only test insert & search.
fuzz_target!(|operations: Vec<NodeOperation>| {
    let root = NodeRef::default();
    let mut answers = HashMap::new();

    for operation in operations {
        let (k, kvpair_ptr) = match operation {
            NodeOperation::Insert { key, value } => {
                if key.len() == 0 || value.len() == 0 {
                    continue;
                }
                (
                    key.clone(),
                    KVPair::new(key.clone(), value.clone()).into_raw(),
                )
            }
            NodeOperation::Remove {
                remove_exist: _,
                key,
            } => {
                if key.len() == 0 {
                    continue;
                }
                (
                    key.clone(),
                    KVPair::new(key.clone(), key.clone()).into_raw(),
                )
            }
        };
        // answer.insert()
        Node::insert(&root, &k, kvpair_ptr, 0).unwrap();
        answers.insert(k, kvpair_ptr);
    }

    for (k, answer) in answers {
        let result = Node::search(&root.refer(), &k, 0).unwrap();
        unsafe { assert_eq!(*from_tagged_ptr(&result), *answer) };
    }
});
