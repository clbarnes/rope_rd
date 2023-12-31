//! Utilities for interspersing real data with filler bytes.
//!
//! The [`Spacer`] represents these filler bytes.
//! The [`Part`] represents something which can either be real data or a [`Spacer`].
use std::fmt::Debug;
use std::io;
use std::io::{Read, Seek, SeekFrom};

use crate::util::abs_position;
use crate::Node;

/// [`Read`]able, [`Seek`]able [`Iterator`] with a given length and fill value.
///
/// Implements [`Into`] for [`Node`](crate::Node)s.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Spacer {
    length: u64,
    fill: u8,
    position: u64,
}

impl Iterator for Spacer {
    type Item = u8;

    fn next(&mut self) -> Option<Self::Item> {
        if self.position >= self.length {
            None
        } else {
            self.position += 1;
            Some(self.fill)
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let rem = self.remaining() as usize;
        (rem, Some(rem))
    }
}

impl Spacer {
    /// Create a new spacer with the given length, and default fill value.
    pub fn new(length: u64) -> Self {
        Self::with_fill(length, Default::default())
    }

    /// Create a new spacer with the given length and fill value.
    pub fn with_fill(length: u64, fill: u8) -> Self {
        Self {
            length,
            fill,
            position: 0,
        }
    }

    /// Number of bytes remaining in the spacer.
    ///
    /// The position can be changed by iteration, reading, or seeking.
    pub fn remaining(&self) -> u64 {
        self.length - self.position.min(self.length)
    }
}

impl Read for Spacer {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let mut idx = 0;
        for (el, val) in buf.iter_mut().zip(self) {
            *el = val;
            idx += 1;
        }
        Ok(idx)
    }
}

impl Seek for Spacer {
    fn seek(&mut self, pos: SeekFrom) -> io::Result<u64> {
        self.position = abs_position(self.position, self.length, pos)?;
        Ok(self.position)
    }
}

/// Enum representing part of a readable which may be full or empty.
///
/// If empty, it is filled by a [`Spacer`];
/// if full, by some other [`Read`] & [`Seek`]able.
///
/// Implements [`TryInto`] for [`Node`](crate::Node)s.
pub enum Part<F: Read + Seek> {
    Full(F),
    Empty(Spacer),
}

impl<F: Read + Seek + Debug> Debug for Part<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Full(arg0) => f.debug_tuple("Full").field(arg0).finish(),
            Self::Empty(arg0) => f.debug_tuple("Empty").field(arg0).finish(),
        }
    }
}

impl<F: Read + Seek> Part<F> {
    /// Create an empty part with the given length and the default fill.
    pub fn empty(length: u64) -> Self {
        Spacer::new(length).into()
    }

    /// Create an empty part with the given length and fill.
    pub fn empty_with_fill(length: u64, fill: u8) -> Self {
        Spacer::with_fill(length, fill).into()
    }
}

impl<F: Read + Seek> Read for Part<F> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        match self {
            Part::Full(r) => r.read(buf),
            Part::Empty(r) => r.read(buf),
        }
    }
}

impl<F: Read + Seek> Seek for Part<F> {
    fn seek(&mut self, pos: SeekFrom) -> io::Result<u64> {
        match self {
            Part::Full(s) => s.seek(pos),
            Part::Empty(s) => s.seek(pos),
        }
    }
}

impl<F: Read + Seek> From<Spacer> for Part<F> {
    fn from(val: Spacer) -> Self {
        Part::Empty(val)
    }
}

impl<F: Read + Seek> TryInto<Node<Part<F>>> for Part<F> {
    fn try_into(self) -> Result<Node<Part<F>>, Self::Error> {
        Node::leaf(self)
    }

    type Error = io::Error;
}

impl<F: Read + Seek> From<Spacer> for Node<Part<F>> {
    fn from(val: Spacer) -> Self {
        let len = val.length;
        Node::leaf_with_length(val.into(), len)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn iter() {
        let len = 100;
        let s = Spacer::new(len);
        let v: Vec<_> = s.collect();
        assert_eq!(v, vec![0; len as usize])
    }

    #[test]
    fn read() {
        let len = 100;
        let mut s = Spacer::new(len);
        let mut v = Vec::default();
        s.read_to_end(&mut v).unwrap();
        assert_eq!(v, vec![0; len as usize])
    }

    #[test]
    fn seek() {
        let len = 100;
        let mut s = Spacer::new(len);
        let mut v = Vec::default();
        s.seek(SeekFrom::Start(50)).unwrap();
        s.read_to_end(&mut v).unwrap();
        assert_eq!(v, vec![0; len as usize - 50])
    }
}
