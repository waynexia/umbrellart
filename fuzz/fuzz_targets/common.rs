use libfuzzer_sys::arbitrary::Arbitrary;

#[derive(Arbitrary)]
pub enum NodeOperation {
    Insert { key: Vec<u8>, value: u64 },
    Remove { remove_exist: bool, key: Vec<u8> },
}

impl NodeOperation {
    fn convert_key(key: &[u8]) -> Vec<u8> {
        let mut key: Vec<u8> = key.iter().filter(|byte| **byte != 0).copied().collect();
        key.push(0);
        key
    }

    pub fn canonicalize(&self) -> Vec<u8> {
        match self {
            NodeOperation::Insert { key, .. } => Self::convert_key(key),
            NodeOperation::Remove { key, .. } => Self::convert_key(key),
        }
    }
}

impl std::fmt::Debug for NodeOperation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("art.")?;
        let key = self.canonicalize();

        match self {
            NodeOperation::Insert { value, .. } => {
                f.write_fmt(format_args!("insert(&{:?}, {});", key.as_slice(), value))?;
            }
            NodeOperation::Remove { remove_exist, .. } => {
                if *remove_exist {
                    f.write_fmt(format_args!("remove(&{:?});", key.as_slice()))?;
                } else {
                    f.write_fmt(format_args!("remove(&[]);"))?;
                }
            }
        }

        Ok(())
    }
}
