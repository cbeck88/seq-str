use crate::{SeqBytes, SeqBytesIter, SeqBytesIterMut};
use alloc::{string::String, vec::Vec};
use core::fmt;

/// A sequence of &str, stored contiguously
///
/// This can be used as a drop-in replacement for `Vec<String>` in some cases,
/// with better memory locality and fewer memory allocations.
///
/// When using `SeqBytes` instead of `Vec<String>`, the individual strings
/// cannot be resized, but when this isn't needed there isn't much downside otherwise.
///
/// The container also supports "emplace"-style APIs like `in_place_writer`, which allow you to
/// write the next element directly into the contiguous buffer with minimal overhead.
///
/// `SeqStr::from_display_iter` allows you to collect an iterator of `impl Display` items,
/// formatting them directly into the contiguous buffer.
#[derive(Clone, Default, Eq, PartialEq, Hash)]
pub struct SeqStr {
    inner: SeqBytes,
}

impl SeqStr {
    /// Create a new SeqStr
    pub fn new() -> Self {
        Self::default()
    }

    /// Check if the sequence is empty
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Get the number of str in the sequence
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Reserve capacity for more str's
    pub fn reserve(&mut self, extra: usize) {
        self.inner.reserve(extra);
    }

    /// Shrink container to fit the current data
    pub fn shrink_to_fit(&mut self) {
        self.inner.shrink_to_fit();
    }

    /// Get the i'th element of the sequence in a checked manner
    pub fn get(&self, idx: usize) -> Option<&str> {
        self.inner
            .get(idx)
            .map(|b| unsafe { str::from_utf8_unchecked(b) })
    }

    /// Get the i'th element of the sequence in a checked manner
    pub fn get_mut(&mut self, idx: usize) -> Option<&mut str> {
        self.inner
            .get_mut(idx)
            .map(|b| unsafe { str::from_utf8_unchecked_mut(b) })
    }

    /// Check if the sequence contains a particular string
    pub fn contains(&self, s: impl AsRef<str>) -> bool {
        self.inner.contains(s.as_ref().as_bytes())
    }

    /// Push a `&str` onto the sequence
    pub fn push(&mut self, s: impl AsRef<str>) {
        self.inner.push(s.as_ref().as_bytes());
    }

    /// Get the last `str` of the sequence
    pub fn last(&self) -> Option<&str> {
        self.inner
            .last()
            .map(|b| unsafe { str::from_utf8_unchecked(b) })
    }

    /// Pop the last element of the container
    /// Note that we can't return it because of lifetimes, so call [last] before popping.
    pub fn pop(&mut self) {
        self.inner.pop()
    }

    /// Iterate over a range of the sequence of `&str`
    ///
    /// This resembles [std::collections::BTreeMap::range], and is needed becuase like `BTreeMap`,
    /// we can't implement `Deref` or `SliceIndex<Range>` and produce a slice of our contents.
    /// See also [as_vec].
    pub fn range(
        &self,
        range_bounds: impl core::ops::RangeBounds<usize>,
    ) -> core::iter::Map<SeqBytesIter<'_>, fn(&[u8]) -> &str> {
        fn helper(b: &[u8]) -> &str {
            unsafe { str::from_utf8_unchecked(b) }
        }

        self.inner.range(range_bounds).map(helper)
    }

    /// Iterate over a range of the sequence of &mut [u8]
    pub fn range_mut(
        &mut self,
        range_bounds: impl core::ops::RangeBounds<usize>,
    ) -> core::iter::Map<SeqBytesIterMut<'_>, fn(&mut [u8]) -> &mut str> {
        fn helper(b: &mut [u8]) -> &mut str {
            unsafe { str::from_utf8_unchecked_mut(b) }
        }

        self.inner.range_mut(range_bounds).map(helper)
    }

    /// Iterate over the sequence of `&str`
    pub fn iter(&self) -> core::iter::Map<SeqBytesIter<'_>, fn(&[u8]) -> &str> {
        fn helper(b: &[u8]) -> &str {
            unsafe { str::from_utf8_unchecked(b) }
        }

        self.inner.iter().map(helper)
    }

    /// Iterate over the sequence of `&mut str`
    pub fn iter_mut(&mut self) -> core::iter::Map<SeqBytesIterMut<'_>, fn(&mut [u8]) -> &mut str> {
        fn helper(b: &mut [u8]) -> &mut str {
            unsafe { str::from_utf8_unchecked_mut(b) }
        }

        self.inner.iter_mut().map(helper)
    }

    /// Truncate to at most the first n `str`
    pub fn truncate(&mut self, new_size: usize) {
        self.inner.truncate(new_size)
    }

    /// Resize to contain only the first n `str`, or pad up to n `str`, with empty `str` added
    pub fn resize(&mut self, new_size: usize) {
        self.inner.resize(new_size)
    }

    /// Retain only those `str` satisfying a predicate.
    /// The `str` are always visited in order, similar to [std::vec::Vec::retain].
    pub fn retain(&mut self, mut pred: impl FnMut(&str) -> bool) {
        self.inner
            .retain(move |b| pred(unsafe { str::from_utf8_unchecked(b) }));
    }

    /// Retain only those `str` satisfying a predicate.
    /// The `str` are always visited in order, similar to [std::vec::Vec::retain_mut].
    pub fn retain_mut(&mut self, mut pred: impl FnMut(&mut str) -> bool) {
        self.inner
            .retain_mut(move |b| pred(unsafe { str::from_utf8_unchecked_mut(b) }));
    }

    /// Get an `impl std::fmt::Write` which can be used to write the next slice
    /// directly into the buffer without copying.
    pub fn in_place_writer(&mut self) -> impl core::fmt::Write {
        // Wrapper for return
        struct Sink<T: FnMut(&[u8])>(pub T);

        impl<T: FnMut(&[u8])> core::fmt::Write for Sink<T> {
            fn write_str(&mut self, s: &str) -> std::fmt::Result {
                (self.0)(s.as_bytes());
                Ok(())
            }
        }

        Sink(self.inner.in_place_writer_no_std())
    }

    /// Construct `SeqStr` from any items that implement `Display`,
    /// formatting them directly into the contiguous buffer.
    pub fn from_display_iter<T: core::fmt::Display, I: Iterator<Item = T>>(it: I) -> Self {
        use core::fmt::Write;

        let mut result = Self::default();
        result.reserve(it.size_hint().0);
        for item in it {
            // Note: This error is okay to unwrap, because our destination buffer is unlimited size.
            // This is the same as what that `ToString::to_string` does with these errors in the stdlib.
            write!(result.in_place_writer(), "{item}")
                .expect("a Display implementation returned an error unexpectedly");
        }
        result
    }

    /// Express as a Vec<&str>. The main reason that this may be useful is that there are
    /// useful methods on slice types `&[&str]`, for example, [core::slice::binary_search],
    /// but `SeqStr` itself doesn't implement `Deref` the way that `Vec` does and can
    /// only produce such a slice by allocating.
    ///
    /// See [SeqBytes::as_vec] for more discussion of tradeoffs.
    pub fn as_vec(&self) -> Vec<&str> {
        self.iter().collect()
    }

    /// Concatenate the `str` in the sequence into one string
    pub fn concat(&self) -> &str {
        unsafe { core::str::from_utf8_unchecked(self.inner.concat()) }
    }

    /// Join the `str` in the sequence into one string, placing a separator between them
    pub fn join(&self, separator: &str) -> String {
        let mut result = String::with_capacity(self.inner.num_bytes() + self.inner.len().saturating_sub(1) * separator.len());
        let mut first = true;

        for s in self.iter() {
            if first {
                first = false;
            } else {
                result += separator;
            }
            result += s;
        }
        result
    }
}

impl core::ops::Index<usize> for SeqStr {
    type Output = str;

    fn index(&self, index: usize) -> &str {
        unsafe { str::from_utf8_unchecked(self.inner.index(index)) }
    }
}

impl core::ops::IndexMut<usize> for SeqStr {
    fn index_mut(&mut self, index: usize) -> &mut str {
        unsafe { str::from_utf8_unchecked_mut(self.inner.index_mut(index)) }
    }
}

impl fmt::Debug for SeqStr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<A: AsRef<str>> Extend<A> for SeqStr {
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

impl<A: AsRef<str>> FromIterator<A> for SeqStr {
    // Required method
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = A>,
    {
        let mut result = SeqStr::default();
        result.extend(iter);
        result
    }
}

// IntoIterator can only be implemented for &'a SeqStr,
// otherwise the buffer doesn't live long enough.
impl<'a> IntoIterator for &'a SeqStr {
    type Item = &'a str;
    type IntoIter = core::iter::Map<SeqBytesIter<'a>, fn(&[u8]) -> &str>;

    fn into_iter(self) -> Self::IntoIter {
        fn helper(b: &[u8]) -> &str {
            unsafe { core::str::from_utf8_unchecked(b) }
        }

        self.inner.iter().map(helper)
    }
}

#[cfg(feature = "serde")]
mod serde_impls {
    use super::*;
    use ::serde::{
        Deserialize, Serialize,
        de::{Deserializer, SeqAccess, Visitor},
        ser::{SerializeSeq, Serializer},
    };

    impl Serialize for SeqStr {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            let mut seq = serializer.serialize_seq(Some(self.len()))?;
            for e in self {
                seq.serialize_element(e)?;
            }
            seq.end()
        }
    }

    impl<'de> Deserialize<'de> for SeqStr {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            deserializer.deserialize_seq(SeqStrVis {})
        }
    }

    struct SeqStrVis {}

    impl<'de> Visitor<'de> for SeqStrVis {
        type Value = SeqStr;

        fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            formatter.write_str("a sequence of strings")
        }

        fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
        where
            A: SeqAccess<'de>,
        {
            let mut result = SeqStr::default();

            if let Some(size) = seq.size_hint() {
                result.reserve(size);
            }

            loop {
                let maybe_next_str: Option<&str> = seq.next_element()?;
                if let Some(next_str) = maybe_next_str {
                    result.push(next_str);
                } else {
                    return Ok(result);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::{borrow::ToOwned, vec, vec::Vec};

    #[test]
    fn vec_str_conversions() {
        let vec_str = vec!["1", "2", "3"];

        let seq_str: SeqStr = vec_str.into_iter().collect();

        assert_eq!(seq_str.len(), 3);
        assert_eq!(&seq_str[0], "1");
        assert_eq!(&seq_str[1], "2");
        assert_eq!(&seq_str[2], "3");

        let vec_str2 = seq_str.iter().map(ToOwned::to_owned).collect::<Vec<_>>();

        assert_eq!(vec_str2.len(), 3);
        assert_eq!(vec_str2[0], "1");
        assert_eq!(vec_str2[1], "2");
        assert_eq!(vec_str2[2], "3");
    }

    #[test]
    fn vec_string_conversions() {
        let vec_string = vec!["1".to_owned(), "2".to_owned(), "3".to_owned()];

        let seq_str: SeqStr = vec_string.into_iter().collect();

        assert_eq!(seq_str.len(), 3);
        assert_eq!(&seq_str[0], "1");
        assert_eq!(&seq_str[1], "2");
        assert_eq!(&seq_str[2], "3");

        let vec_str2 = seq_str.iter().map(ToOwned::to_owned).collect::<Vec<_>>();

        assert_eq!(vec_str2.len(), 3);
        assert_eq!(vec_str2[0], "1");
        assert_eq!(vec_str2[1], "2");
        assert_eq!(vec_str2[2], "3");
    }

    #[test]
    fn from_display_iter() {
        let v = vec![1, 2, 3, 45, 67];

        let seq_str = SeqStr::from_display_iter(v.into_iter());

        assert_eq!(seq_str.len(), 5);
        assert_eq!(&seq_str[0], "1");
        assert_eq!(&seq_str[1], "2");
        assert_eq!(&seq_str[2], "3");
        assert_eq!(&seq_str[3], "45");
        assert_eq!(&seq_str[4], "67");
    }

    #[test]
    fn range() {
        let v = vec![1, 2, 3, 45, 67];

        let seq_str = SeqStr::from_display_iter(v.into_iter());

        let seq_str2: SeqStr = seq_str.range(1..4).collect();
        assert_eq!(seq_str2.len(), 3);
        assert_eq!(&seq_str2[0], "2");
        assert_eq!(&seq_str2[1], "3");
        assert_eq!(&seq_str2[2], "45");

        let seq_str2: SeqStr = seq_str.range(3..).collect();
        assert_eq!(seq_str2.len(), 2);
        assert_eq!(&seq_str2[0], "45");
        assert_eq!(&seq_str2[1], "67");

        let seq_str2: SeqStr = seq_str.range(..3).collect();
        assert_eq!(seq_str2.len(), 3);
        assert_eq!(&seq_str2[0], "1");
        assert_eq!(&seq_str2[1], "2");
        assert_eq!(&seq_str2[2], "3");

        let seq_str2: SeqStr = seq_str.range(..).collect();
        assert_eq!(seq_str2.len(), 5);
        assert_eq!(&seq_str2[0], "1");
        assert_eq!(&seq_str2[1], "2");
        assert_eq!(&seq_str2[2], "3");
        assert_eq!(&seq_str2[3], "45");
        assert_eq!(&seq_str2[4], "67");
    }

    #[test]
    fn iter_mut() {
        let mut seq_str = SeqStr::from_iter(["asdf", "jkl;", ""]);

        assert_eq!(seq_str.len(), 3);
        assert_eq!(&seq_str[0], "asdf");
        assert_eq!(&seq_str[1], "jkl;");
        assert_eq!(&seq_str[2], "");

        for s in seq_str.iter_mut() {
            s.make_ascii_uppercase();
        }

        assert_eq!(seq_str.len(), 3);
        assert_eq!(&seq_str[0], "ASDF");
        assert_eq!(&seq_str[1], "JKL;");
        assert_eq!(&seq_str[2], "");
    }

    #[test]
    fn test_serde() {
        let seq_str: SeqStr = serde_json::from_str("[\"asdf\", \"jkl;\", \"\"]").unwrap();

        assert_eq!(seq_str.len(), 3);
        assert_eq!(&seq_str[0], "asdf");
        assert_eq!(&seq_str[1], "jkl;");
        assert_eq!(&seq_str[2], "");

        let ser = serde_json::to_string(&seq_str).unwrap();

        let seq_str2: SeqStr = serde_json::from_str(&ser).unwrap();

        assert_eq!(seq_str, seq_str2);
    }

    #[test]
    fn test_join() {
        let seq_str = SeqStr::from_iter(["asdf", "jkl;", "", ":)"]);

        assert_eq!(seq_str.concat(), "asdfjkl;:)");
        assert_eq!(seq_str.join(", "), "asdf, jkl;, , :)");    
    }
}
