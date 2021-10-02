#[cfg(loom)]
crate use loom::sync::atomic::AtomicPtr;
#[cfg(not(loom))]
crate use std::sync::atomic::AtomicPtr;

#[cfg(loom)]
crate use loom::sync::atomic::AtomicUsize;
#[cfg(not(loom))]
crate use std::sync::atomic::AtomicUsize;

#[cfg(loom)]
crate use loom::sync::Mutex;
#[cfg(not(loom))]
crate use std::sync::Mutex;

#[cfg(loom)]
crate use loom::sync::MutexGuard;
#[cfg(not(loom))]
crate use std::sync::MutexGuard;

#[cfg(loom)]
crate use loom::sync::atomic::Ordering;
#[cfg(not(loom))]
crate use std::sync::atomic::Ordering;

#[cfg(loom)]
crate use loom::sync::Arc;
#[cfg(not(loom))]
crate use std::sync::Arc;
