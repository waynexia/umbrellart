use libfuzzer_sys::arbitrary::Arbitrary;

#[derive(Arbitrary, Debug)]
// #[derive(Clone, Debug, arbitrary::Arbitrary)]
// #[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub enum NodeOperation {
    Insert { key: Vec<u8>, value: Vec<u8> },
    Remove { remove_exist: bool, key: Vec<u8> },
}
