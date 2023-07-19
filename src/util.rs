//! General utilities for working with streams.

use std::{
    cmp::Ordering,
    io::{self, Seek, SeekFrom},
};

/// Given the current absolute position and the length of the stream, determine the absolute position of a given possibly-relative seek.
///
/// Like [Seek], fails if the seed would be before the start of the stream,
/// but allows seeks after the end.
pub fn abs_position(curr_position: u64, length: u64, seek: SeekFrom) -> io::Result<u64> {
    let out = match seek {
        SeekFrom::Start(p) => p,
        SeekFrom::End(p) => match p.cmp(&0) {
            Ordering::Less => {
                let pabs = p.unsigned_abs();
                if pabs > length {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "Tried to seek before start",
                    ));
                } else {
                    length - pabs
                }
            }
            Ordering::Equal => length,
            Ordering::Greater => length + p as u64,
        },
        SeekFrom::Current(p) => match p.cmp(&0) {
            Ordering::Less => {
                let pabs = p.unsigned_abs();
                if pabs > curr_position {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "Tried to seek before start",
                    ));
                } else {
                    curr_position - pabs
                }
            }
            Ordering::Equal => curr_position,
            Ordering::Greater => curr_position + p as u64,
        },
    };
    Ok(out)
}

/// Finds the stream length with up to 3 seeks.
///
/// Returns to the original position.
pub fn stream_len(s: &mut impl Seek) -> io::Result<u64> {
    let curr = s.stream_position()?;
    let end = stream_len_fast(s)?;
    if curr != end {
        s.seek(SeekFrom::Start(curr))?;
    }
    Ok(end)
}

/// Finds the stream length with 1 seek, but does not return to the original position.
pub fn stream_len_fast(s: &mut impl Seek) -> io::Result<u64> {
    s.seek(SeekFrom::End(0))
}
