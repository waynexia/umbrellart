use std::marker::PhantomData;

#[repr(u8)]
enum NodeType {
    Node4,
    Node16,
}

struct TinyNode<const CAP: usize, OverflowTo, UnderflowTo> {
    children: [*const (); CAP],
    _overflow_to: PhantomData<OverflowTo>,
    _underflow_to: PhantomData<UnderflowTo>,
}
