use std::fmt::Debug;
use std::io;
use std::io::{Read, Seek, SeekFrom};

use crate::util::{abs_position, stream_len, stream_len_fast};

/// Data in a [`Node::Leaf`], which knows its own width and contains something [`Read`]/[`Seek`]able.
///
/// Should not be created directly, but via a [`Node`].
pub struct Leaf<F: Read + Seek> {
    width: u64,
    part: F,
}

impl<F: Read + Seek + Debug> Debug for Leaf<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Leaf")
            .field("width", &self.width)
            .field("part", &self.part)
            .finish()
    }
}

impl<F: Read + Seek> Read for Leaf<F> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        self.part.read(buf)
    }
}

impl<F: Read + Seek> Seek for Leaf<F> {
    fn seek(&mut self, pos: SeekFrom) -> io::Result<u64> {
        self.part.seek(pos)
    }
}

/// Data in a [`Node::Branch`], which contains two child [`Node`]s and knows their widths.
///
/// Should not be created directly, but via a [`Node`].
pub struct Branch<F: Read + Seek> {
    width: u64,
    split: u64,
    left: Box<Node<F>>,
    right: Box<Node<F>>,
    position: u64,
}

impl<F: Read + Seek + Debug> Debug for Branch<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Branch")
            .field("width", &self.width)
            .field("split", &self.split)
            .field("left", &self.left)
            .field("right", &self.right)
            .field("position", &self.position)
            .finish()
    }
}

impl<F: Read + Seek> Branch<F> {
    fn new(left: Node<F>, right: Node<F>) -> Self {
        let lwid = left.width();
        let rwid = right.width();
        Self::new_with_widths(left, lwid, right, rwid)
    }

    fn new_with_widths(left: Node<F>, left_width: u64, right: Node<F>, right_width: u64) -> Self {
        Self {
            left: Box::new(left),
            split: left_width,
            right: Box::new(right),
            width: left_width + right_width,
            position: 0,
        }
    }

    fn set_position(&mut self, pos: u64) {
        self.position = pos;
        if pos < self.split {
            match self.left.as_mut() {
                Node::Leaf(lf) => {
                    lf.seek(SeekFrom::Start(pos)).unwrap();
                }
                Node::Branch(b) => b.set_position(pos),
            }
        } else {
            let pos = pos - self.split;
            match self.right.as_mut() {
                Node::Leaf(lf) => {
                    lf.seek(SeekFrom::Start(pos)).unwrap();
                }
                Node::Branch(b) => b.set_position(pos),
            }
        }
    }
}

impl<F: Read + Seek> Read for Branch<F> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let mut tmp_buf = &mut buf[..];
        let mut total_read = 0;
        let mut from_left = false;
        if self.position < self.split {
            let left = self.left.as_mut();
            total_read += left.read(tmp_buf)?;
            tmp_buf = &mut tmp_buf[total_read..];
            self.position += total_read as u64;
            from_left = true;
        }
        if self.position >= self.split {
            let right = self.right.as_mut();
            if from_left {
                right.seek(SeekFrom::Start(0))?;
            }
            let n_read = right.read(tmp_buf)?;
            total_read += n_read;
            self.position += n_read as u64;
        }
        Ok(total_read)
    }
}

impl<F: Read + Seek> Seek for Branch<F> {
    fn stream_position(&mut self) -> io::Result<u64> {
        Ok(self.position)
    }

    fn seek(&mut self, pos: SeekFrom) -> io::Result<u64> {
        let new_pos = abs_position(self.position, self.width, pos)?;
        self.set_position(new_pos);
        Ok(new_pos)
    }
}

/// Node in a rope; may be the root.
pub enum Node<F: Read + Seek> {
    Leaf(Leaf<F>),
    Branch(Branch<F>),
}

impl<F: Read + Seek + Debug> Debug for Node<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Leaf(arg0) => f.debug_tuple("Leaf").field(arg0).finish(),
            Self::Branch(arg0) => f.debug_tuple("Branch").field(arg0).finish(),
        }
    }
}

impl<F: Read + Seek> Node<F> {
    /// Create a leaf node with a given [`Read`]/[`Seek`]able.
    ///
    /// Requires 2 seek operations:
    /// [`Node::leaf_with_length`] is much more efficient
    /// unless seeks are very fast (e.g. in-memory).
    ///
    /// Leaf will be seeked to the start.
    pub fn leaf(mut part: F) -> io::Result<Self> {
        let width = stream_len_fast(&mut part)?;
        part.seek(SeekFrom::Start(0))?;
        Ok(Self::leaf_with_length(part, width))
    }

    /// Create a leaf with a known length.
    ///
    /// Leaf should already be seeked to the start.
    pub fn leaf_with_length(part: F, length: u64) -> Self {
        Self::Leaf(Leaf {
            width: length,
            part,
        })
    }

    /// Create a branch node containing two child nodes.
    pub fn branch(left: Node<F>, right: Node<F>) -> Self {
        Self::Branch(Branch::new(left, right))
    }

    /// Create a rope from a [`Vec`] of `(start, item)` pairs.
    ///
    /// Items must be [`Read`]/[`Seek`]able, sorted, and consecutive (one starts where the previous ends, or at 0 if it's first).
    /// The rope will be organised to partition the full length of the stream as well as possible, to optimise random seeks.
    ///
    /// Panics when given zero parts.
    pub fn partition_with_starts(mut start_parts: Vec<(u64, F)>, total_length: u64) -> Self {
        match start_parts.len() {
            0 => panic!("Empty partition"),
            1 => Self::leaf_with_length(start_parts.pop().unwrap().1, total_length),
            2 => {
                let r_pair = start_parts.pop().unwrap();
                let l_pair = start_parts.pop().unwrap();

                let left = Self::leaf_with_length(l_pair.1, r_pair.0);
                let right = Self::leaf_with_length(r_pair.1, total_length - r_pair.0);
                Self::branch(left, right)
            }
            n => {
                let split_goal = total_length / 2;
                let mut total = 0;
                let mut idx = 1;
                for (start, _) in start_parts.iter() {
                    total += start;
                    if total > split_goal {
                        break;
                    }
                    idx += 1;
                }
                // ensure that neither side has 0 parts
                idx = idx.clamp(1, n - 1);

                let right = start_parts.split_off(idx);
                let initial = right[0].0;
                let new_right = right.into_iter().map(|(st, p)| (st - initial, p)).collect();
                Self::branch(
                    Self::partition_with_starts(start_parts, initial),
                    Self::partition_with_starts(new_right, total_length - initial),
                )
            }
        }
    }

    /// Create a rope from a [`Vec`] of items.
    ///
    /// Items must be [`Read`]/[`Seek`]able.
    /// The rope will be organised to partition the full length of the stream as well as possible, to optimise random seeks.
    ///
    /// Item lengths will be determined by their stream length,
    /// which takes multiple seeks to compute.
    /// If you know their offsets already, use [`Node::partition_with_starts`].
    ///
    /// Raises an error when given zero parts.
    pub fn partition(mut parts: Vec<F>) -> io::Result<Self> {
        match parts.len() {
            0 => Err(io::Error::new(io::ErrorKind::Other, "empty partition")),
            1 => Self::leaf(parts.pop().unwrap()),
            2 => {
                let right = Self::leaf(parts.pop().unwrap())?;
                let left = Self::leaf(parts.pop().unwrap())?;
                Ok(Self::branch(left, right))
            }
            _ => {
                let mut total = 0;
                let mut len_parts = Vec::with_capacity(parts.len());
                for mut part in parts {
                    let start = total;
                    total += stream_len(&mut part)?;
                    len_parts.push((start, part));
                }
                Ok(Self::partition_with_starts(len_parts, total))
            }
        }
    }
}

impl<F: Read + Seek> From<Leaf<F>> for Node<F> {
    fn from(value: Leaf<F>) -> Self {
        Self::Leaf(value)
    }
}

impl<F: Read + Seek> From<Branch<F>> for Node<F> {
    fn from(value: Branch<F>) -> Self {
        Self::Branch(value)
    }
}

impl<F: Read + Seek> Read for Node<F> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        match self {
            Node::Leaf(lf) => lf.read(buf),
            Node::Branch(b) => b.read(buf),
        }
    }
}

impl<F: Read + Seek> Seek for Node<F> {
    fn stream_position(&mut self) -> io::Result<u64> {
        match self {
            Node::Leaf(lf) => lf.stream_position(),
            Node::Branch(b) => b.stream_position(),
        }
    }

    fn seek(&mut self, pos: SeekFrom) -> io::Result<u64> {
        match self {
            Node::Leaf(lf) => lf.seek(pos),
            Node::Branch(b) => b.seek(pos),
        }
    }
}

impl<F: Read + Seek> Node<F> {
    fn width(&self) -> u64 {
        match self {
            Node::Leaf(n) => n.width,
            Node::Branch(n) => n.width,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    fn make_leaf(values: &[u8]) -> Node<Cursor<Vec<u8>>> {
        let v: Vec<_> = values.iter().cloned().collect();
        Node::leaf(Cursor::new(v)).unwrap()
    }

    fn make_branch(left: &[u8], right: &[u8]) -> Node<Cursor<Vec<u8>>> {
        Node::branch(make_leaf(left), make_leaf(right))
    }

    #[test]
    fn branch_read() {
        let mut node = make_branch(&[1; 6], &[2; 6]);

        assert_eq!(node.width(), 12);
        let mut buf = vec![0; 4];

        let mut rd = node.read(buf.as_mut()).unwrap();
        assert_eq!(buf, [1, 1, 1, 1]);
        assert_eq!(rd, 4);

        rd = node.read(buf.as_mut()).unwrap();
        assert_eq!(buf, [1, 1, 2, 2]);
        assert_eq!(rd, 4);

        rd = node.read(buf.as_mut()).unwrap();
        assert_eq!(buf, [2, 2, 2, 2]);
        assert_eq!(rd, 4);

        rd = node.read(buf.as_mut()).unwrap();
        assert_eq!(rd, 0);
    }

    #[test]
    fn branch_seek() {
        let mut node = make_branch(&[1; 6], &[2; 6]);
        node.seek(SeekFrom::Start(4)).unwrap();
        let mut buf = vec![0; 4];
        let rd = node.read(buf.as_mut()).unwrap();
        assert_eq!(buf, [1, 1, 2, 2]);
        assert_eq!(rd, 4);
    }
}
