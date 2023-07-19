//! A rope data structure which implements [`std::io::Read`] and [`std::io::Seek`] by delegating to its leaf nodes.
//!
//! ```rust
//! use std::io::{Cursor, Read};
//! use rope_rd::Node;
//!
//! let mut rope = Node::branch(
//!     Node::leaf(Cursor::new(vec![1, 2, 3])).unwrap(),
//!     Node::leaf_with_length(Cursor::new(vec![4, 5, 6]), 3),
//! );
//!
//! let mut out = Vec::default();
//! rope.read_to_end(&mut out).unwrap();
//! ```
//!
//! This rope does not allow insertions into the middle of the tree,
//! or any removals.
mod rope;
pub mod sparse;
pub mod util;

pub use rope::Node;
