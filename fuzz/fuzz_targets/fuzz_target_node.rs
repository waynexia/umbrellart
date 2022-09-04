#![no_main]
use std::collections::HashMap;

use fuzz_common::NodeOperation;
use libfuzzer_sys::fuzz_target;
use umbrellart::Art;

fn convert_key(key: Vec<u8>) -> Vec<u8> {
    let mut key: Vec<u8> = key.into_iter().filter(|byte| *byte != 0).collect();
    key.push(0);
    key
}

// Only test insert & search.
fuzz_target!(|operations: Vec<NodeOperation>| {
    let mut art = Art::new();
    let mut answers = HashMap::new();

    for operation in operations {
        match operation {
            NodeOperation::Insert { key, value } => {
                let key = convert_key(key);
                if key.len() <= 1 {
                    continue;
                }

                if answers.contains_key(&key) {
                    // todo: ignore duplicate keys for now.
                    continue;
                }
                let answer = answers.insert(key.clone(), value);
                let result = art.insert(&key, value);
                assert_eq!(answer, result);
            }
            NodeOperation::Remove { remove_exist, key } => {
                let key = if remove_exist {
                    if answers.is_empty() {
                        continue;
                    }
                    answers.keys().next().unwrap().to_owned()
                } else {
                    convert_key(key)
                };
                if key.len() <= 1 {
                    continue;
                }

                let answer = answers.remove(&key);
                let result = art.remove(&key);
                assert_eq!(answer, result);
            }
        }
    }

    for (k, answer) in answers {
        let result = art.get(&k).unwrap();
        assert_eq!(*result, answer);
    }
});
