//! blean, the binary export format.
//!
//! [`MAGIC`], then every [`Record`] in order, postcard encoded, each expression record
//! followed by its [`Info`], ending with [`Record::End`]. Strings decode without copying,
//! so a memory-mapped file is read in place.
//!
//! Version 2 ([`MAGIC_V2`]), written when the meta declares format 3.2.0 or later, also
//! follows each inductive record with one byte per type: 0 for no flags, else `0x20` or'd
//! with [`IndFlags::bits`]. Otherwise the two versions agree.

use crate::{
    error::{corrupt, Result},
    info::{Info, Tracker},
    record::{Counts, Decl, IndFlags, IndType, Record, Sink, Table},
};
use std::{io::Write, mem};

/// File signature; the final byte is the format version.
pub const MAGIC: [u8; 8] = *b"BLEAN\0\0\x01";

/// The signature of a file that carries inductive flags.
pub const MAGIC_V2: [u8; 8] = *b"BLEAN\0\0\x02";

const HAS_FLAGS: u8 = 0x20;

/// Whether a `meta` object declares format 3.2.0 or later.
fn flagged(meta: &str) -> bool {
    let v: serde_json::Value = serde_json::from_str(meta).unwrap_or_default();
    let mut parts = v["format"]["version"]
        .as_str()
        .unwrap_or_default()
        .split('.')
        .map(|p| p.parse::<u32>().unwrap_or(0));
    let major = parts.next().unwrap_or(0);
    let minor = parts.next().unwrap_or(0);
    (major, minor) >= (3, 2)
}

fn flag_byte(t: &IndType) -> u8 {
    t.flags.map_or(0, |f| HAS_FLAGS | f.bits())
}

/// Writes records as blean.
#[derive(Debug)]
pub struct Blean<W: Write> {
    out: W,
    buf: Vec<u8>,
    info: Tracker,
    started: bool,
    v2: bool,
}

impl<W: Write> Blean<W> {
    pub fn new(out: W) -> Self {
        Self {
            out,
            buf: Vec::new(),
            info: Tracker::new(),
            started: false,
            v2: false,
        }
    }
}

impl<W: Write> Sink for Blean<W> {
    type Output = W;

    fn record(&mut self, _: Option<u32>, r: &Record<'_>) -> Result<()> {
        if !self.started {
            self.v2 = matches!(r, Record::Meta(m) if flagged(m));
            self.out
                .write_all(if self.v2 { &MAGIC_V2 } else { &MAGIC })?;
            self.started = true;
        }
        let mut buf = postcard::to_extend(r, mem::take(&mut self.buf))?;
        if let Some(info) = self.info.observe(r)? {
            buf = postcard::to_extend(&info, buf)?;
        }
        if let Record::Decl(Decl::Inductive { types, .. }) = r {
            if self.v2 {
                buf.extend(types.iter().map(flag_byte));
            } else if types.iter().any(|t| t.flags.is_some()) {
                return Err(corrupt(
                    "inductive flags in an export whose meta predates format 3.2.0",
                ));
            }
        }
        self.out.write_all(&buf)?;
        buf.clear();
        self.buf = buf;
        Ok(())
    }

    fn finish(mut self) -> Result<W> {
        self.out.flush()?;
        Ok(self.out)
    }
}

/// Whether `bytes` starts like a blean file.
#[must_use]
pub fn sniff(bytes: &[u8]) -> bool {
    bytes.starts_with(&MAGIC) || bytes.starts_with(&MAGIC_V2)
}

/// The table sizes a complete blean file declares in its last 12 bytes, for presizing
/// before reading. [`entries`] checks them against the records.
pub fn counts(bytes: &[u8]) -> Result<Counts> {
    let tail = bytes
        .len()
        .checked_sub(12)
        .filter(|_| sniff(bytes))
        .map(|at| &bytes[at..])
        .ok_or_else(|| corrupt("not a blean file"))?;
    Ok(postcard::from_bytes(tail)?)
}

/// The records of a complete blean file with each expression's info.
///
/// Strings borrow from `bytes`. Fails on a missing signature, a truncated stream, bytes
/// after the end, or end counts that disagree with the records before them.
pub fn entries(bytes: &[u8]) -> Result<Entries<'_>> {
    let (rest, v2) = match bytes.strip_prefix(&MAGIC_V2) {
        Some(rest) => (rest, true),
        None => (
            bytes
                .strip_prefix(&MAGIC)
                .ok_or_else(|| corrupt("not a blean file"))?,
            false,
        ),
    };
    Ok(Entries {
        rest,
        next: Counts::default(),
        done: false,
        v2,
    })
}

/// Iterator returned by [`entries`].
#[derive(Debug)]
pub struct Entries<'b> {
    rest: &'b [u8],
    next: Counts,
    done: bool,
    v2: bool,
}

impl<'b> Entries<'b> {
    fn step(&mut self) -> Result<(Record<'b>, Option<Info>)> {
        let (mut r, rest) = postcard::take_from_bytes::<Record<'b>>(self.rest)?;
        self.rest = rest;
        if let (true, Record::Decl(Decl::Inductive { types, .. })) = (self.v2, &mut r) {
            let (bytes, rest) = self
                .rest
                .split_at_checked(types.len())
                .ok_or_else(|| corrupt("blean: truncated inductive flags"))?;
            for (t, &b) in types.iter_mut().zip(bytes) {
                t.flags = match b {
                    0 => None,
                    0x20..=0x3f => IndFlags::from_bits(b ^ HAS_FLAGS),
                    _ => return Err(corrupt("blean: bad inductive flags")),
                };
            }
            self.rest = rest;
        }
        if let Record::End(counts) = r {
            self.done = true;
            if counts != self.next || !rest.is_empty() {
                return Err(corrupt("blean: bad end record"));
            }
            return Ok((r, None));
        }
        self.next.assign(&r);
        let info = if r.table() == Some(Table::Exprs) {
            let (info, rest) = postcard::take_from_bytes::<Info>(self.rest)?;
            self.rest = rest;
            Some(info)
        } else {
            None
        };
        Ok((r, info))
    }
}

impl<'b> Iterator for Entries<'b> {
    type Item = Result<(Record<'b>, Option<Info>)>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }
        let r = self.step();
        self.done |= r.is_err();
        Some(r)
    }
}

/// Replay a complete blean file into `sink`.
pub fn read<S: Sink>(bytes: &[u8], mut sink: S) -> Result<S::Output> {
    let mut next = Counts::default();
    for e in entries(bytes)? {
        let r = e?.0;
        sink.record(next.assign(&r), &r)?;
    }
    sink.finish()
}
