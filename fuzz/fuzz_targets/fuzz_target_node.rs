#![no_main]
use fuzz_common::NodeOperation;
use libfuzzer_sys::fuzz_target;
use umbrellart::{KVPair, Node};

use std::collections::HashMap;
use std::sync::atomic::AtomicPtr;

fuzz_target!(|operations: Vec<NodeOperation>| {
    let root = AtomicPtr::new(Node::make_node4() as *mut usize);
    Node::init(&root, &[1], &[0]);
    let mut answer = HashMap::new();

    for operation in operations {
        match operation {
            NodeOperation::Insert { key, value } => {
                answer.insert(key.clone(), value.clone());
                let kvpair = KVPair::new(key.clone(), value).into_raw();
                Node::insert(&root, key.as_slice(), kvpair, 0).unwrap();
            }
            NodeOperation::Remove { remove_exist, key } => {
                let key = if remove_exist && !answer.is_empty() {
                    answer.keys().next().unwrap().clone()
                } else {
                    key
                };
                let expected = answer.remove(&key);
                let result = Node::remove(&root, &key, 0)
                    .map(|ptr| unsafe { &*(ptr as *mut KVPair) })
                    .map(|kvpair| kvpair.value.clone());
                assert_eq!(&result, &expected);
            }
        }
    }
});
