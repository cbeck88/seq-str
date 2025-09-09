# seq-str

[![Crates.io](https://img.shields.io/crates/v/conf?style=flat-square)](https://crates.io/crates/seq-str)
[![Crates.io](https://img.shields.io/crates/d/conf?style=flat-square)](https://crates.io/crates/seq-str)
[![License](https://img.shields.io/badge/license-MIT%202.0-blue?style=flat-square)](LICENSE)

`seq-str` provides alternatives to `Vec<String>` and `Vec<Vec<u8>>` which store
all the data in contiguous memory. The types `SeqStr` and `SeqBytes` can often
be drop-in replacements, for improved memory locality and fewer memory allocations.

These types also support "`emplace`"-like APIs such as `in_place_writer`, which
allow writing the next element directly into the contiguous buffer.

`SeqStr::from_display_iter` allows you to collect any iterator of `impl Display`,
where all formatting takes place directly in the contiguous buffer.

## See also

* [flatcontainer](https://github.com/antiguru/flatcontainer) with similar motivation
  but a more ambitious approach
