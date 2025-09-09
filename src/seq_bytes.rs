use alloc::vec::Vec;
use core::fmt;

/// A sequence of `&[u8]`, stored contiguously
///
/// This can be used as a drop-in replacement for `Vec<Vec<u8>>` in some cases,
/// with better memory locality and fewer memory allocations.
///
/// When using `SeqBytes` instead of `Vec<Vec<u8>>`, the individual byte strings
/// cannot be resized, but when this isn't needed there isn't much downside otherwise.
///
/// The container also supports "emplace"-style APIs like `in_place_writer`, which allow you to
/// write the next element directly into the contiguous buffer with minimal overhead.
#[derive(Clone, Default, Eq, PartialEq, Hash)]
pub struct SeqBytes {
    data: Vec<u8>,
    offsets: Vec<usize>,
}

impl SeqBytes {
    /// Create a new SeqBytes
    pub fn new() -> Self {
        Self::default()
    }

    /// Check if the sequence is empty
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Get the number of slices in the sequence
    pub fn len(&self) -> usize {
        self.offsets.len()
    }

    /// Reserve capacity for more slices
    pub fn reserve(&mut self, extra: usize) {
        self.offsets.reserve(extra);
        // Guess how much data to reserve based on existing usage
        if !self.is_empty() && extra > 0 {
            let a = extra * 4;
            let b = self.data.len() * 4;
            // estimate data.len * extra / offsets.len
            let c = (self.data.len() * extra)
                >> ((usize::BITS - 1) - self.offsets.len().leading_zeros());

            #[allow(clippy::collapsible_else_if)]
            let median = if a <= b {
                if a <= c { core::cmp::min(b, c) } else { a }
            } else {
                if a <= c { a } else { core::cmp::max(b, c) }
            };

            self.data.reserve(median);
        } else {
            self.data.reserve(4 * extra);
        }
    }

    /// Shrink container to fit the current data
    pub fn shrink_to_fit(&mut self) {
        self.data.shrink_to_fit();
        self.offsets.shrink_to_fit();
    }

    /// Get the sum of the lengths of the byte strings
    pub fn num_bytes(&self) -> usize {
        self.data.len()
    }

    /// Get the i'th element of the sequence in a checked manner
    pub fn get(&self, idx: usize) -> Option<&[u8]> {
        let first = self.offsets.get(idx)?;
        match self.offsets.get(idx + 1) {
            Some(second) => Some(&self.data[*first..*second]),
            None => Some(&self.data[*first..]),
        }
    }

    /// Get the i'th element of the sequence in a checked manner
    pub fn get_mut(&mut self, idx: usize) -> Option<&mut [u8]> {
        let first = self.offsets.get(idx)?;
        match self.offsets.get(idx + 1) {
            Some(second) => Some(&mut self.data[*first..*second]),
            None => Some(&mut self.data[*first..]),
        }
    }

    /// Check if the sequence contains a particular element
    pub fn contains(&self, s: impl AsRef<[u8]>) -> bool {
        let s = s.as_ref();
        self.iter().any(|b| b == s)
    }

    /// Push a &[u8] onto the sequence
    pub fn push(&mut self, s: impl AsRef<[u8]>) {
        self.offsets.push(self.data.len());
        self.data.extend(s.as_ref().iter());
    }

    /// Get the last &[u8] of the sequence
    pub fn last(&self) -> Option<&[u8]> {
        match self.offsets.last() {
            Some(o) => Some(&self.data[*o..]),
            None => None,
        }
    }

    /// Pop the last element of the container
    /// Note that we can't return it because of lifetimes, so call [last] before popping.
    pub fn pop(&mut self) {
        if let Some(o) = self.offsets.pop() {
            self.data.truncate(o);
        }
    }

    /// Iterate over the sequence of &[u8]
    pub fn iter(&self) -> SeqBytesIter<'_> // impl ExactSizeIterator<Item = &[u8]>
    {
        SeqBytesIter {
            data: &self.data[..],
            offsets: &self.offsets[..],
        }
    }

    /// Iterate over the sequence of &mut [u8]
    pub fn iter_mut(&mut self) -> SeqBytesIterMut<'_> // impl ExactSizeIterator<Item = &mut[u8]>
    {
        SeqBytesIterMut {
            data: &mut self.data[..],
            offsets: &self.offsets[..],
        }
    }

    // Helper to convert range bounds object to a range
    fn range_bounds_to_range(
        &self,
        range_bounds: impl core::ops::RangeBounds<usize>,
    ) -> (usize, usize) {
        use core::ops::Bound;

        let start_idx = match range_bounds.start_bound() {
            Bound::Included(s) => *s,
            Bound::Excluded(s) => s + 1,
            Bound::Unbounded => 0,
        };

        let end_idx = match range_bounds.end_bound() {
            Bound::Included(e) => e + 1,
            Bound::Excluded(e) => *e,
            Bound::Unbounded => self.offsets.len(),
        };

        (start_idx, end_idx)
    }

    /// Iterate over a range of the sequence of `&[u8]`
    ///
    /// This resembles [std::collections::BTreeMap::range], and is needed becuase like `BTreeMap`,
    /// we can't implement `Deref` or `SliceIndex<Range>` and produce a slice of our contents.
    /// See also [as_vec].
    pub fn range(&self, range_bounds: impl core::ops::RangeBounds<usize>) -> SeqBytesIter<'_> {
        let (start_idx, end_idx) = self.range_bounds_to_range(range_bounds);
        let data_end = self
            .offsets
            .get(end_idx)
            .cloned()
            .unwrap_or(self.data.len());

        SeqBytesIter {
            data: &self.data[0..data_end],
            offsets: &self.offsets[start_idx..end_idx],
        }
    }

    /// Iterate over a range of the sequence of `&mut [u8]`
    pub fn range_mut(
        &mut self,
        range_bounds: impl core::ops::RangeBounds<usize>,
    ) -> SeqBytesIterMut<'_> {
        let (start_idx, end_idx) = self.range_bounds_to_range(range_bounds);
        let data_end = self
            .offsets
            .get(end_idx)
            .cloned()
            .unwrap_or(self.data.len());

        SeqBytesIterMut {
            data: &mut self.data[0..data_end],
            offsets: &self.offsets[start_idx..end_idx],
        }
    }

    /// Truncate to at most the first n slices
    pub fn truncate(&mut self, new_size: usize) {
        if let Some(off) = self.offsets.get(new_size) {
            self.data.truncate(*off);
            self.offsets.truncate(new_size);
        }
    }

    /// Resize to contain only the first n `&[u8]`, or pad up to n slices, with empty slices added
    pub fn resize(&mut self, new_size: usize) {
        if let Some(off) = self.offsets.get(new_size) {
            self.data.truncate(*off);
            self.offsets.truncate(new_size);
        } else {
            // Push empty slices until offsets has length new_size
            let d = new_size - self.offsets.len();
            self.offsets.reserve(d);
            for _ in 0..d {
                self.offsets.push(self.data.len());
            }
        }
    }

    /// Retain only those slices satisfying a predicate.
    /// The slices are always visited in order, similar to [std::vec::Vec::retain].
    pub fn retain(&mut self, mut pred: impl FnMut(&[u8]) -> bool) {
        self.retain_mut(|elem| pred(elem))
    }

    /// Retain only those slices satisfying a predicate.
    /// The slices are always visited in order, similar to [std::vec::Vec::retain_mut].
    pub fn retain_mut(&mut self, mut pred: impl FnMut(&mut [u8]) -> bool) {
        let (data, offsets) = (&mut self.data, &mut self.offsets);

        let mut offset_write_idx = 0;
        let mut kept_bytes = 0;

        // Invariant:
        // Offsets is not reduced in length during this loop
        // Data is not reduced in length during this loop
        for offset_idx in 0..offsets.len() {
            let start = offsets[offset_idx];
            let end = offsets.get(offset_idx + 1).cloned().unwrap_or(data.len());

            let outcome = pred(&mut data[start..end]);
            if outcome {
                // We will preserve kept_len additional bytes,
                // write their starting offset first.
                let kept_len = end - start;
                offsets[offset_write_idx] = kept_bytes;
                offset_write_idx += 1;

                // Move from data[start..end] to
                // data[kept_bytes, kept_bytes + kept_len]
                // if start == kept bytes we don't have to do anything
                if kept_bytes != start {
                    for byte_idx in 0..kept_len {
                        data[kept_bytes + byte_idx] = data[start + byte_idx];
                    }
                }
                kept_bytes += kept_len;
            }
        }
        drop(pred);

        // Truncate both offsets and data to what was actually retained
        offsets.truncate(offset_write_idx);
        data.truncate(kept_bytes);
    }

    /// Get an `impl std::io::Write` which can be used to write the next slice
    /// directly into the buffer without copying.
    #[cfg(feature = "std")]
    pub fn in_place_writer(&mut self) -> impl std::io::Write {
        // Correctness:
        // If we push a new offset on, then we have conceptually added a new string.
        // If the only thing that happens after that is that data is appended to self.data,
        // then the final state is correct and offsets doesn't need further adjusting.
        //
        // The only thing they can do with std::io::Write is push more bytes.
        // And no other changes can be made to SeqBytes until that writer is dropped,
        // because it captures &mut self.
        //
        // So we don't need to return an object with a Drop impl, we will always end
        // up in the correct state.
        self.offsets.push(self.data.len());
        &mut self.data
    }

    /// Version of `in_place_writer` that doesn't require `std::io::Write` trait
    ///
    /// Any bytes passed to the result of this function get concatenated to produce the
    /// newest byte string in the sequence. The new item is final when the writer is dropped.
    pub fn in_place_writer_no_std(&mut self) -> impl FnMut(&[u8]) {
        self.offsets.push(self.data.len());

        let dat = &mut self.data;

        move |b: &[u8]| {
            dat.extend(b);
        }
    }

    /// Express as a Vec<&[u8]>. The main reason that this may be useful is that there are
    /// useful methods on slice types `&[&[u8]]`, for example, [core::slice::binary_search],
    /// but `SeqBytes` itself doesn't implement `Deref` the way that `Vec` does and can
    /// only produce such a slice by allocating.
    ///
    /// Note: The trade-offs are that we would need more memory and `in_place_writer` would have
    /// to be more complicated and slower if we wanted our internal representation of the offsets
    /// to be a `Vec<&[u8]>`, which would allow such a `Deref` implementation.
    /// The direction we've taken is to add useful functions from `Vec` and slice
    /// as needed directly to this type instead, if they can't be obtained in a simpler way.
    pub fn as_vec(&self) -> Vec<&[u8]> {
        self.iter().collect()
    }

    /// Concatenate the `&[u8]` in the sequence into one `&[u8]`
    pub fn concat(&self) -> &[u8] {
        &self.data[..]
    }
}

impl core::ops::Index<usize> for SeqBytes {
    type Output = [u8];

    fn index(&self, index: usize) -> &[u8] {
        let first = self.offsets[index];
        match self.offsets.get(index + 1) {
            Some(second) => &self.data[first..*second],
            None => &self.data[first..],
        }
    }
}

impl core::ops::IndexMut<usize> for SeqBytes {
    fn index_mut(&mut self, index: usize) -> &mut [u8] {
        let first = self.offsets[index];
        match self.offsets.get(index + 1) {
            Some(second) => &mut self.data[first..*second],
            None => &mut self.data[first..],
        }
    }
}

impl fmt::Debug for SeqBytes {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

/// An iterator over a SeqBytes object
#[derive(Clone)]
pub struct SeqBytesIter<'a> {
    data: &'a [u8],
    offsets: &'a [usize],
}

impl<'a> Iterator for SeqBytesIter<'a> {
    type Item = &'a [u8];

    fn next(&mut self) -> Option<&'a [u8]> {
        let first = self.offsets.first()?;
        self.offsets = &self.offsets[1..];

        let second = self.offsets.first().cloned().unwrap_or(self.data.len());
        Some(&self.data[*first..second])
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.offsets.len();
        (remaining, Some(remaining))
    }
}

impl<'a> ExactSizeIterator for SeqBytesIter<'a> {}

impl<'a> DoubleEndedIterator for SeqBytesIter<'a> {
    fn next_back(&mut self) -> Option<&'a [u8]> {
        let last = *self.offsets.last()?;
        self.offsets = &self.offsets[..self.offsets.len() - 1];

        let (left, right) = self.data.split_at(last);
        self.data = left;

        Some(right)
    }
}

/// A mutable iterator over a SeqBytes object
pub struct SeqBytesIterMut<'a> {
    data: &'a mut [u8],
    offsets: &'a [usize],
}

impl<'a> Iterator for SeqBytesIterMut<'a> {
    type Item = &'a mut [u8];

    fn next(&mut self) -> Option<&'a mut [u8]> {
        let first = self.offsets.first()?;
        self.offsets = &self.offsets[1..];

        let second = self.offsets.first().cloned().unwrap_or(self.data.len());

        // Some(&mut self.data[*first..second])
        // Work around borrow checker issue
        let slice = unsafe {
            let start = self.data.as_mut_ptr().add(*first);
            core::slice::from_raw_parts_mut(start, second - first)
        };

        Some(slice)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.offsets.len();
        (remaining, Some(remaining))
    }
}

impl<'a> ExactSizeIterator for SeqBytesIterMut<'a> {}

impl<'a> DoubleEndedIterator for SeqBytesIterMut<'a> {
    fn next_back(&mut self) -> Option<&'a mut [u8]> {
        let last = *self.offsets.last()?;
        self.offsets = &self.offsets[..self.offsets.len() - 1];

        let (left, right) = self.data.split_at_mut(last);
        // Work around borrow checker issue
        self.data = unsafe {
            let len = left.len();
            let ptr = left.as_mut_ptr();
            core::slice::from_raw_parts_mut(ptr, len)
        };

        // Work around borrow checker issue
        let slice = unsafe {
            let len = right.len();
            let ptr = right.as_mut_ptr();
            core::slice::from_raw_parts_mut(ptr, len)
        };

        Some(slice)
    }
}

impl<A: AsRef<[u8]>> Extend<A> for SeqBytes {
    fn extend<T>(&mut self, iter: T)
    where
        T: IntoIterator<Item = A>,
    {
        let iter = iter.into_iter();
        self.reserve(iter.size_hint().0);
        for item in iter {
            self.push(item);
        }
    }
}

impl<A: AsRef<[u8]>> FromIterator<A> for SeqBytes {
    // Required method
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = A>,
    {
        let mut result = SeqBytes::default();
        result.extend(iter);
        result
    }
}

// IntoIterator can only be implemented for &'a SeqBytes,
// otherwise the buffer doesn't live long enough.
impl<'a> IntoIterator for &'a SeqBytes {
    type Item = &'a [u8];
    type IntoIter = SeqBytesIter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::{borrow::ToOwned, vec};

    #[test]
    fn vec_slice_conversions() {
        let vec_b = vec![b"1", b"2", b"3"];

        let seq_b: SeqBytes = vec_b.into_iter().collect();

        assert_eq!(seq_b.len(), 3);
        assert_eq!(&seq_b[0], b"1");
        assert_eq!(&seq_b[1], b"2");
        assert_eq!(&seq_b[2], b"3");

        let vec_str2 = seq_b.iter().map(ToOwned::to_owned).collect::<Vec<_>>();

        assert_eq!(vec_str2.len(), 3);
        assert_eq!(vec_str2[0], b"1");
        assert_eq!(vec_str2[1], b"2");
        assert_eq!(vec_str2[2], b"3");
    }

    #[test]
    fn vec_vec_b_conversions() {
        let vec_string = vec![b"1".to_owned(), b"2".to_owned(), b"3".to_owned()];

        let seq_b: SeqBytes = vec_string.into_iter().collect();

        assert_eq!(seq_b.len(), 3);
        assert_eq!(&seq_b[0], b"1");
        assert_eq!(&seq_b[1], b"2");
        assert_eq!(&seq_b[2], b"3");

        let vec_str2 = seq_b.iter().map(ToOwned::to_owned).collect::<Vec<_>>();

        assert_eq!(vec_str2.len(), 3);
        assert_eq!(vec_str2[0], b"1");
        assert_eq!(vec_str2[1], b"2");
        assert_eq!(vec_str2[2], b"3");
    }

    #[test]
    fn iter_rev() {
        let vec_b = vec![b"1", b"2", b"3"];

        let seq_b: SeqBytes = vec_b.into_iter().collect();

        assert_eq!(seq_b.len(), 3);
        assert_eq!(&seq_b[0], b"1");
        assert_eq!(&seq_b[1], b"2");
        assert_eq!(&seq_b[2], b"3");

        let seq_b2: SeqBytes = seq_b.into_iter().rev().collect();

        assert_eq!(seq_b2.len(), 3);
        assert_eq!(&seq_b2[0], b"3");
        assert_eq!(&seq_b2[1], b"2");
        assert_eq!(&seq_b2[2], b"1");
    }

    #[test]
    fn contains() {
        let vec_b: Vec<&[u8]> = vec![b"123", b"45", b"6", b"", b"7", b"89"];
        let seq_b: SeqBytes = vec_b.iter().collect();

        assert!(seq_b.contains(b"123"));
        assert!(!seq_b.contains(b"12"));
        assert!(!seq_b.contains(b"1"));
        assert!(seq_b.contains(b""));
        assert!(seq_b.contains(b"6"));
    }

    #[test]
    fn iter_mut() {
        let vec_b: Vec<&[u8]> = vec![b"123", b"45", b"6", b"", b"7", b"89"];
        let mut seq_b: SeqBytes = vec_b.iter().collect();

        for b in seq_b.iter_mut() {
            if b.len() > 0 {
                b[0] = b"a"[0];
            }
        }

        assert_eq!(seq_b.len(), 6);
        assert_eq!(&seq_b[0], b"a23");
        assert_eq!(&seq_b[1], b"a5");
        assert_eq!(&seq_b[2], b"a");
        assert_eq!(&seq_b[3], b"");
        assert_eq!(&seq_b[4], b"a");
        assert_eq!(&seq_b[5], b"a9");
    }

    #[test]
    fn retain() {
        let vec_b: Vec<&[u8]> = vec![b"123", b"45", b"6", b"", b"7", b"89"];
        let mut seq_b: SeqBytes = vec_b.iter().collect();

        assert_eq!(seq_b.len(), 6);
        assert_eq!(&seq_b[0], b"123");
        assert_eq!(&seq_b[1], b"45");
        assert_eq!(&seq_b[2], b"6");
        assert_eq!(&seq_b[3], b"");
        assert_eq!(&seq_b[4], b"7");
        assert_eq!(&seq_b[5], b"89");

        seq_b.retain(|b| !b.is_empty());

        assert_eq!(seq_b.len(), 5);
        assert_eq!(&seq_b[0], b"123");
        assert_eq!(&seq_b[1], b"45");
        assert_eq!(&seq_b[2], b"6");
        assert_eq!(&seq_b[3], b"7");
        assert_eq!(&seq_b[4], b"89");

        seq_b.retain(|b| b.len() >= 2);

        assert_eq!(seq_b.len(), 3);
        assert_eq!(&seq_b[0], b"123");
        assert_eq!(&seq_b[1], b"45");
        assert_eq!(&seq_b[2], b"89");

        seq_b.retain(|b| b.len() <= 2);

        assert_eq!(seq_b.len(), 2);
        assert_eq!(&seq_b[0], b"45");
        assert_eq!(&seq_b[1], b"89");

        seq_b.push(b"123");

        assert_eq!(seq_b.len(), 3);
        assert_eq!(&seq_b[0], b"45");
        assert_eq!(&seq_b[1], b"89");
        assert_eq!(&seq_b[2], b"123");

        seq_b.retain(|b| b.len() >= 3);

        assert_eq!(seq_b.len(), 1);
        assert_eq!(&seq_b[0], b"123");

        seq_b.resize(3);

        assert_eq!(seq_b.len(), 3);
        assert_eq!(&seq_b[0], b"123");
        assert_eq!(&seq_b[1], b"");
        assert_eq!(&seq_b[2], b"");

        seq_b.truncate(5);

        assert_eq!(seq_b.len(), 3);
        assert_eq!(&seq_b[0], b"123");
        assert_eq!(&seq_b[1], b"");
        assert_eq!(&seq_b[2], b"");

        seq_b.truncate(2);

        assert_eq!(seq_b.len(), 2);
        assert_eq!(&seq_b[0], b"123");
        assert_eq!(&seq_b[1], b"");
    }
}
