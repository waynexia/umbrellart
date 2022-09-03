/// Calculate the common prefix's length of two slices
pub(crate) fn compare_slices(lhs: &[u8], rhs: &[u8]) -> usize {
    let valid = lhs.len().min(rhs.len());

    for i in 0..valid {
        if lhs[i] != rhs[i] {
            return i;
        }
    }

    valid
}
