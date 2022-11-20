use std::collections::{BTreeMap, HashMap};
use std::fs::File;
use std::io::{BufRead, BufReader};

use criterion::{criterion_group, criterion_main, Criterion};
use umbrellart::Art;

const CORPUS_PATH: &str = "./target/corpus.txt";

pub fn umbrellart(c: &mut Criterion) {
    let corpus = read_corpus();
    let mut art = Art::new();
    for (index, item) in corpus.iter().enumerate() {
        art.insert(item, index);
    }
    c.bench_function("sequence get umbrellart", |b| {
        b.iter(|| {
            for item in &corpus {
                let _ = art.get(item);
            }
        })
    });
}

pub fn hashmap(c: &mut Criterion) {
    let corpus = read_corpus();
    let mut map = HashMap::new();
    for (index, item) in corpus.iter().enumerate() {
        map.insert(item.clone(), index);
    }
    c.bench_function("sequence get hashmap", |b| {
        b.iter(|| {
            for item in &corpus {
                let _ = map.get(item);
            }
        })
    });
}

pub fn btreemap(c: &mut Criterion) {
    let corpus = read_corpus();
    let mut map = BTreeMap::new();
    for (index, item) in corpus.iter().enumerate() {
        map.insert(item.clone(), index);
    }
    c.bench_function("sequence get btreemap", |b| {
        b.iter(|| {
            for item in &corpus {
                let _ = map.get(item);
            }
        })
    });
}

fn read_corpus() -> Vec<Vec<u8>> {
    let file = File::open(CORPUS_PATH).unwrap();
    BufReader::new(file)
        .lines()
        .map(|text| {
            text.map(|t| {
                let mut bytes = t.into_bytes();
                bytes.push(0);
                bytes
            })
        })
        .collect::<Result<Vec<_>, _>>()
        .unwrap()
}

criterion_group!(benches, umbrellart, hashmap, btreemap);
criterion_main!(benches);
