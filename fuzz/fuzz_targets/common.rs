use libfuzzer_sys::arbitrary::Arbitrary;

#[derive(Arbitrary, Debug)]
pub enum NodeOperation {
    Insert { key: Vec<u8>, value: u64 },
    Remove { remove_exist: bool, key: Vec<u8> },
}
