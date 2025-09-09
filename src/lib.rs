#![no_std]
extern crate alloc;

#[cfg(feature = "std")]
extern crate std;

mod seq_bytes;
pub use seq_bytes::{SeqBytes, SeqBytesIter, SeqBytesIterMut};

mod seq_str;
pub use seq_str::SeqStr;
