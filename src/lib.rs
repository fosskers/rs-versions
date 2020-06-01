//! A library for parsing and comparing software version numbers.
//!
//! We like to give version numbers to our software in a myriad of different
//! ways. Some ways follow strict guidelines for incrementing and comparison.
//! Some follow conventional wisdom and are generally self-consistent. Some are
//! just plain asinine. This library provides a means of parsing and comparing
//! *any* style of versioning, be it a nice Semantic Version like this:
//!
//! > 1.2.3-r1+git123
//!
//! ...or a monstrosity like this:
//!
//! > 2:10.2+0.0093r3+1-1
//!
//! # Usage
//!
//! If you're parsing version numbers that don't follow a single scheme (say, as
//! in system packages), then use the [`Versioning`](enum.Versioning.html) type
//! and its parser `foo`. TODO

#![doc(html_root_url = "https://docs.rs/versions/1.0.0")]

use nom::character::complete::char;
use nom::combinator::opt;
use nom::IResult;
use std::cmp::Ordering;
mod parsers;

// TODO
// - Just the main structs, a parser for each subtype, and a parser for the
//   combined `Versioning`.
// - A lot of the convenience functions in the Haskell version can be made into methods.
// - Use `Display` for pretty-printing.
// - NOT exposing the parsers.
// - No PVP support.
// - No need to worry about lenses :)

/// An (Ideal) version number that conforms to Semantic Versioning.
///
/// This is a *prescriptive* parser, meaning that it follows the [SemVer
/// standard][semver].
///
/// Legal semvers are of the form: MAJOR.MINOR.PATCH-PREREL+META
///
/// Example: `1.2.3-r1+commithash`
///
/// # Extra Rules
///
/// 1. Pre-release versions have *lower* precedence than normal versions.
/// 2. Build metadata does not affect version precedence.
/// 3. PREREL and META strings may only contain ASCII alphanumerics.
///
/// # Examples
///
/// ```
/// use versions::SemVer;
///
/// let attempt = SemVer::new("1.2.3");
/// let expected = SemVer { major: 1, minor: 2, patch: 3, pre_rel: vec![], meta: vec![] };
///
/// assert_eq!(Some(expected), attempt);
/// ```
///
/// [semver]: http://semver.org
#[derive(Debug, Eq, Hash, Clone)]
pub struct SemVer {
    pub major: u32,
    pub minor: u32,
    pub patch: u32,
    pub pre_rel: Chunks,
    pub meta: Chunks,
}

impl SemVer {
    pub fn new(s: &str) -> Option<SemVer> {
        SemVer::parse(s).ok().map(|pair| pair.1)
    }

    fn parse(i: &str) -> IResult<&str, SemVer> {
        let (i, major) = parsers::unsigned(i)?;
        let (i, _) = char('.')(i)?;
        let (i, minor) = parsers::unsigned(i)?;
        let (i, _) = char('.')(i)?;
        let (i, patch) = parsers::unsigned(i)?;
        let (i, pre_rel) = opt(SemVer::pre_rel)(i)?;
        let (i, meta) = opt(SemVer::meta)(i)?;

        let sv = SemVer {
            major,
            minor,
            patch,
            pre_rel: pre_rel.unwrap_or(Chunks::new()),
            meta: meta.unwrap_or(Chunks::new()),
        };

        Ok((i, sv))
    }

    fn pre_rel(i: &str) -> IResult<&str, Chunks> {
        let (i, _) = char('-')(i)?;
        Chunks::parse(i)
    }

    fn meta(i: &str) -> IResult<&str, Chunks> {
        let (i, _) = char('+')(i)?;
        Chunks::parse(i)
    }
}

/// Two SemVers are equal if all fields except metadata are equal.
impl PartialEq for SemVer {
    fn eq(&self, other: &Self) -> bool {
        self.major == other.major
            && self.minor == other.minor
            && self.patch == other.patch
            && self.pre_rel == other.pre_rel
    }
}

impl PartialOrd for SemVer {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Build metadata does not affect version precendence, and pre-release versions
/// have *lower* precedence than normal versions.
impl Ord for SemVer {
    fn cmp(&self, other: &Self) -> Ordering {
        let a = (self.major, self.minor, self.patch);
        let b = (other.major, other.minor, other.patch);
        match a.cmp(&b) {
            Ordering::Less => Ordering::Less,
            Ordering::Greater => Ordering::Greater,
            Ordering::Equal if self.pre_rel.0.is_empty() && other.pre_rel.0.is_empty() => {
                Ordering::Equal
            }
            Ordering::Equal if self.pre_rel.0.is_empty() => Ordering::Greater,
            Ordering::Equal if other.pre_rel.0.is_empty() => Ordering::Less,
            Ordering::Equal => self.pre_rel.cmp(&other.pre_rel),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Copy, Clone)]
pub struct Version;

#[derive(Debug, PartialEq, Eq, Hash, Copy, Clone)]
pub struct Mess;

/// A single unit of a version number. May be digits or a string of characters.
///
/// Groups of these are called `Chunk`s, and are the identifiers separated by
/// periods in the source.
///
/// Please avoid using the `Unit::String` constructor yourself. Instead consider
/// the [`from_string`](#method.from_string) method to verify the input.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum Unit {
    Digits(u32),
    String(String),
}

// TODO Add more examples.
/// A logical unit of a version number.
///
/// Can consist of multiple letters and numbers. Groups of these (i.e.
/// [`Chunks`](type.Chunks.html)) are separated by periods to form a full
/// version number.
///
/// # Examples
///
/// - `r3`
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Chunk(Vec<Unit>);

impl Chunk {
    pub fn new() -> Chunk {
        Chunk(Vec::new())
    }

    fn parse(i: &str) -> IResult<&str, Chunk> {
        Ok((i, Chunk::new()))
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Chunks(Vec<Chunk>);

impl Chunks {
    pub fn new() -> Chunks {
        Chunks(Vec::new())
    }

    fn parse(i: &str) -> IResult<&str, Chunks> {
        Ok((i, Chunks::new()))
    }
}

impl Unit {
    // TODO This can be made simpler once `bool::then_some` is merged into
    // stable Rust.
    /// Smart constructor for a `Unit` made of letters.
    pub fn from_string(s: String) -> Option<Unit> {
        match s.chars().all(|c| c.is_ascii_alphabetic()) {
            true => Some(Unit::String(s)),
            false => None,
        }
    }
}

/// A top-level Versioning type which acts as a wrapper for the more specific
/// types.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Versioning {
    Ideal(SemVer),
    General(Version),
    Complex(Mess),
}

impl Versioning {
    /// A short-hand for detecting an inner [`SemVer`](struct.SemVer.html).
    pub fn is_ideal(&self) -> bool {
        match self {
            Versioning::Ideal(_) => true,
            _ => false,
        }
    }

    /// A short-hand for detecting an inner [`Version`](struct.Version.html).
    pub fn is_general(&self) -> bool {
        match self {
            Versioning::General(_) => true,
            _ => false,
        }
    }

    /// A short-hand for detecting an inner [`Mess`](struct.Mess.html).
    pub fn is_complex(&self) -> bool {
        match self {
            Versioning::Complex(_) => true,
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_semver() {
        let attempt = SemVer::new("1.2.3-r1+git");
        let expected = SemVer {
            major: 1,
            minor: 2,
            patch: 3,
            pre_rel: Chunks::new(),
            meta: Chunks::new(),
        };

        assert_eq!(Some(expected), attempt);
    }
}
