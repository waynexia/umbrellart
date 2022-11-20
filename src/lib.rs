#![feature(box_into_inner)]
#![feature(pointer_is_aligned)]
#![feature(strict_provenance)]

mod dynamic_node;
mod leaf;
mod node;
mod node_256;
mod node_48;
mod tree;
mod utils;

pub use tree::Art;

#[cfg(test)]
mod test {
    #[global_allocator]
    static UNKAI: UnkaiGlobalAlloc<System> = UnkaiGlobalAlloc::new(System {}, 99, 0, 5, 8);

    use std::alloc::System;
    use std::collections::{BTreeMap, HashMap};

    use rand::Rng;
    use unkai::UnkaiGlobalAlloc;

    use crate::Art;

    fn make_corpus(number: usize, size: usize) -> Vec<Vec<u8>> {
        let mut rng = rand::thread_rng();
        let mut result = Vec::with_capacity(number);

        for _ in 0..number {
            let mut item = Vec::with_capacity(size);
            for _ in 1..size {
                item.push(rng.gen());
            }
            result.push(item);
        }

        result
    }

    #[test]
    fn space_efficiency_umbrellart() {
        let corpus = make_corpus(1024_000, 64);
        let mut art = Art::new();
        for item in corpus {
            art.insert(&item, ());
        }

        for (bt, count) in UNKAI.report_symbol() {
            println!("{} bytes are allocated from:", count);
            println!("{}", bt);
        }
    }

    #[test]
    fn space_efficiency_hashmap() {
        let corpus = make_corpus(1024_000, 64);
        let mut map = HashMap::new();
        for item in corpus {
            map.insert(item, ());
        }

        for (bt, count) in UNKAI.report_symbol() {
            println!("{} bytes are allocated from:", count);
            println!("{}", bt);
        }
    }

    #[test]
    fn space_efficiency_btreemap() {
        let corpus = make_corpus(1024_000, 64);
        let mut map = BTreeMap::new();
        for item in corpus {
            map.insert(item, ());
        }

        for (bt, count) in UNKAI.report_symbol() {
            println!("{} bytes are allocated from:", count);
            println!("{}", bt);
        }
    }

    #[test]
    fn space_efficiency_corpus() {
        let _corpus = make_corpus(1024_000, 64);

        for (bt, count) in UNKAI.report_symbol() {
            println!("{} bytes are allocated from:", count);
            println!("{}", bt);
        }
    }
}
