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

use itertools::Itertools;
use nom::branch::alt;
use nom::character::complete::{alpha1, char};
use nom::combinator::opt;
use nom::multi::{many1, separated_nonempty_list};
use nom::IResult;
use std::cmp::Ordering;
use std::fmt;
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
/// - Simple Sample: `1.2.3`
/// - Full Sample: `1.2.3-alpha.2+a1b2c3.1`
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
/// let orig = "1.2.3-r1+git";
/// let attempt = SemVer::new(orig).unwrap();
///
/// assert_eq!(orig, format!("{}", attempt));
/// ```
///
/// [semver]: http://semver.org
#[derive(Debug, Eq, Hash, Clone)]
pub struct SemVer {
    pub major: u32,
    pub minor: u32,
    pub patch: u32,
    /// `Some` implies that the inner `Vec` of the `Chunks` is not empty.
    pub pre_rel: Option<Chunks>,
    /// `Some` implies that the inner `Vec` of the `Chunks` is not empty.
    pub meta: Option<Chunks>,
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
            pre_rel,
            meta,
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
            Ordering::Equal => match (&self.pre_rel, &other.pre_rel) {
                (None, None) => Ordering::Equal,
                (None, _) => Ordering::Greater,
                (_, None) => Ordering::Less,
                (Some(ap), Some(bp)) => ap.cmp(&bp),
            },
        }
    }
}

impl fmt::Display for SemVer {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let ma = self.major;
        let mi = self.minor;
        let pa = self.patch;
        match (&self.pre_rel, &self.meta) {
            (None, None) => write!(f, "{}.{}.{}", ma, mi, pa),
            (Some(p), None) => write!(f, "{}.{}.{}-{}", ma, mi, pa, p),
            (None, Some(m)) => write!(f, "{}.{}.{}+{}", ma, mi, pa, m),
            (Some(p), Some(m)) => write!(f, "{}.{}.{}-{}+{}", ma, mi, pa, p, m),
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
/// Please avoid using the `Unit::Letters` constructor yourself. Instead
/// consider the [`from_string`](#method.from_string) method to verify the
/// input.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum Unit {
    Digits(u32),
    Letters(String),
}

impl Unit {
    // TODO This can be made simpler once `bool::then_some` is merged into
    // stable Rust.
    /// Smart constructor for a `Unit` made of letters.
    pub fn from_string(s: String) -> Option<Unit> {
        match s.chars().all(|c| c.is_ascii_alphabetic()) {
            true => Some(Unit::Letters(s)),
            false => None,
        }
    }

    fn parse(i: &str) -> IResult<&str, Unit> {
        alt((Unit::digits, Unit::string))(i)
    }

    fn digits(i: &str) -> IResult<&str, Unit> {
        parsers::unsigned(i).map(|(i, x)| (i, Unit::Digits(x)))
    }

    fn string(i: &str) -> IResult<&str, Unit> {
        alpha1(i).map(|(i, s)| (i, Unit::Letters(s.to_string())))
    }
}

impl fmt::Display for Unit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Unit::Digits(ns) => write!(f, "{}", ns),
            Unit::Letters(cs) => write!(f, "{}", cs),
        }
    }
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
pub struct Chunk(pub Vec<Unit>);

impl Chunk {
    pub fn new() -> Chunk {
        Chunk(Vec::new())
    }

    fn parse(i: &str) -> IResult<&str, Chunk> {
        many1(Unit::parse)(i).map(|(i, cs)| (i, Chunk(cs)))
    }
}

impl fmt::Display for Chunk {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s: String = self.0.iter().map(|u| format!("{}", u)).collect();
        write!(f, "{}", s)
    }
}

/// Multiple [`Chunk`](struct.Chunk.html) values.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Chunks(pub Vec<Chunk>);

impl Chunks {
    pub fn new() -> Chunks {
        Chunks(Vec::new())
    }

    fn parse(i: &str) -> IResult<&str, Chunks> {
        let (i, cs) = separated_nonempty_list(char('.'), Chunk::parse)(i)?;
        Ok((i, Chunks(cs)))
    }
}

impl fmt::Display for Chunks {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s: String = self.0.iter().map(|c| format!("{}", c)).join(".");
        write!(f, "{}", s)
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
        let orig = "1.2.3-r1+git";
        let attempt = SemVer::new(orig).unwrap();

        assert_eq!(orig, format!("{}", attempt));
    }

    #[test]
    fn good_semvers() {
        let goods = vec![
            "0.1.0",
            "1.2.3",
            "1.2.3-1",
            "1.2.3-alpha",
            "1.2.3-alpha.2",
            "1.2.3+a1b2c3.1",
            "1.2.3-alpha.2+a1b2c3.1",
        ];

        goods.iter().for_each(|s| {
            assert_eq!(
                Some(s.to_string()),
                SemVer::new(s).map(|sv| format!("{}", sv))
            )
        });
    }

    #[test]
    fn bad_semvers() {
        let bads = vec![
            "1",
            "1.2",
            "1.2.3+a1b2bc3.1-alpha.2",
            "a.b.c",
            "1.01.1",
            "1.2.3+a1b!2c3.1",
        ];

        bads.iter().for_each(|s| assert_eq!(None, SemVer::new(s)));
    }
}
