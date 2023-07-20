use std::fmt::Debug;
use std::io;
use std::io::{Read, Seek, SeekFrom};

use crate::util::{abs_position, stream_len_fast};

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
                Node::Null => (),
            }
        } else {
            let pos = pos - self.split;
            match self.right.as_mut() {
                Node::Leaf(lf) => {
                    lf.seek(SeekFrom::Start(pos)).unwrap();
                }
                Node::Branch(b) => b.set_position(pos),
                Node::Null => (),
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
    Null,
}

impl<F: Read + Seek + Debug> Debug for Node<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Leaf(arg0) => f.debug_tuple("Leaf").field(arg0).finish(),
            Self::Branch(arg0) => f.debug_tuple("Branch").field(arg0).finish(),
            Self::Null => write!(f, "Empty"),
        }
    }
}

impl<F: Read + Seek> Node<F> {
    /// Get the width of the node (number of bytes).
    fn width(&self) -> u64 {
        match self {
            Node::Leaf(n) => n.width,
            Node::Branch(n) => n.width,
            Node::Null => 0,
        }
    }

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

    /// Create a rope from a [`Vec<Node>`].
    ///
    /// Nodes are expected to be sorted and consecutive.
    /// The rope will be organised to partition the full length of the stream as well as possible, to optimise random seeks.
    pub fn partition_nodes(mut nodes: Vec<Self>) -> Self {
        match nodes.len() {
            0 => Self::Null,
            1 => nodes.pop().unwrap(),
            2 => {
                let mut it = nodes.into_iter();
                Self::branch(it.next().unwrap(), it.next().unwrap())
            }
            n => {
                let mut cumu = Vec::with_capacity(nodes.len() + 1);
                cumu.push(0);
                let cumu = nodes.iter().fold(cumu, |mut accum, el| {
                    accum.push(el.width());
                    accum
                });
                let split_goal = cumu.last().unwrap() / 2;
                let mut split_idx = match cumu.binary_search(&split_goal) {
                    // exactly on the boundary, keep this split
                    Ok(idx) => idx,
                    // idx comes under the boundary, so take the next one
                    Err(idx) => idx + 1,
                };
                // because indices are left-inclusive, we don't need to transform to nodes vec (fences) to cumu vec (fenceposts)

                // don't want one partition to have 0 nodes in it
                split_idx = split_idx.clamp(1, n - 1);

                let right = nodes.split_off(split_idx);

                Self::branch(Self::partition_nodes(nodes), Self::partition_nodes(right))
            }
        }
    }

    /// Create a rope from a [`Vec`] of items.
    ///
    /// Items must be [`Read`]/[`Seek`]able.
    /// The rope will be organised to partition the full length of the stream as well as possible, to optimise random seeks.
    ///
    /// Item widths will be determined by their stream length,
    /// which takes multiple seeks to compute.
    /// If you know their widths already, convert them into (leaf) [`Node`]s and use [`Node::partition_nodes`].
    ///
    /// Raises an error when given zero parts, or when node length cannot be determined from stream.
    pub fn partition(parts: Vec<F>) -> io::Result<Self> {
        let nodes_res: Result<Vec<Node<F>>, _> = parts.into_iter().map(|p| Self::leaf(p)).collect();
        nodes_res.map(|n| Self::partition_nodes(n))
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
            Node::Null => Ok(0),
        }
    }
}

impl<F: Read + Seek> Seek for Node<F> {
    fn stream_position(&mut self) -> io::Result<u64> {
        match self {
            Node::Leaf(lf) => lf.stream_position(),
            Node::Branch(b) => b.stream_position(),
            Node::Null => Ok(0),
        }
    }

    fn seek(&mut self, pos: SeekFrom) -> io::Result<u64> {
        match self {
            Node::Leaf(lf) => lf.seek(pos),
            Node::Branch(b) => b.seek(pos),
            Node::Null => {
                abs_position(0, 0, pos)?;
                Ok(0)
            }
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
