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

use itertools::EitherOrBoth::{Both, Left, Right};
use itertools::Itertools;
use nom::branch::alt;
use nom::character::complete::alphanumeric1;
use nom::character::complete::{alpha1, char};
use nom::combinator::opt;
use nom::combinator::value;
use nom::multi::separated_list;
use nom::multi::{many1, separated_nonempty_list};
use nom::IResult;
use std::cmp::Ordering;
use std::fmt;

mod parsers;

/// An ideal version number that conforms to Semantic Versioning.
///
/// This is a *prescriptive* scheme, meaning that it follows the [SemVer
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
        match SemVer::parse(s) {
            Ok(("", sv)) => Some(sv),
            _ => None,
        }
    }

    fn parse(i: &str) -> IResult<&str, SemVer> {
        let (i, major) = parsers::unsigned(i)?;
        let (i, _) = char('.')(i)?;
        let (i, minor) = parsers::unsigned(i)?;
        let (i, _) = char('.')(i)?;
        let (i, patch) = parsers::unsigned(i)?;
        let (i, pre_rel) = opt(Chunks::pre_rel)(i)?;
        let (i, meta) = opt(Chunks::meta)(i)?;

        let sv = SemVer {
            major,
            minor,
            patch,
            pre_rel,
            meta,
        };

        Ok((i, sv))
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

/// A version number with decent structure and comparison logic.
///
/// This is a *descriptive* scheme, meaning that it encapsulates the most
/// common, unconscious patterns that developers use when assigning version
/// numbers to their software. If not [`SemVer`](struct.SemVer.html), most
/// version numbers found in the wild will parse as a `Version`. These generally
/// conform to the `x.x.x-x` pattern, and may optionally have an *epoch*.
///
/// # Epochs
///
/// Epochs are prefixes marked by a colon, like in `1:2.3.4`. When comparing two
/// `Version` values, epochs take precedent. So `2:1.0.0 > 1:9.9.9`. If one of
/// the given `Version`s has no epoch, its epoch is assumed to be `0`.
///
/// # Examples
///
/// ```
/// use versions::{SemVer, Version};
///
/// // None of these are SemVer, but can still be parsed and compared.
/// let vers = vec!["0.25-2", "8.u51-1", "20150826-1", "1:2.3.4"];
///
/// for v in vers {
///     assert!(SemVer::new(v).is_none());
///     assert!(Version::new(v).is_some());
/// }
/// ```
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Version {
    pub epoch: Option<u32>,
    pub chunks: Chunks,
    pub release: Option<Chunks>,
}

impl Version {
    pub fn new(s: &str) -> Option<Version> {
        match Version::parse(s) {
            Ok(("", v)) => Some(v),
            _ => None,
        }
    }

    fn parse(i: &str) -> IResult<&str, Version> {
        let (i, epoch) = opt(Version::epoch)(i)?;
        let (i, chunks) = Chunks::parse(i)?;
        let (i, release) = opt(Chunks::pre_rel)(i)?;

        let v = Version {
            epoch,
            chunks,
            release,
        };

        Ok((i, v))
    }

    fn epoch(i: &str) -> IResult<&str, u32> {
        let (i, epoch) = parsers::unsigned(i)?;
        let (i, _) = char(':')(i)?;

        Ok((i, epoch))
    }
}

impl PartialOrd for Version {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Version {
    /// If two epochs are equal, we need to compare their actual version
    /// numbers. Otherwise, the comparison of the epochs is the only thing that
    /// matters.
    fn cmp(&self, other: &Self) -> Ordering {
        let ae = self.epoch.unwrap_or(0);
        let be = other.epoch.unwrap_or(0);
        match ae.cmp(&be) {
            Ordering::Equal => match self.chunks.cmp(&other.chunks) {
                Ordering::Equal => self.release.cmp(&other.release),
                ord => ord,
            },
            ord => ord,
        }
    }
}

impl fmt::Display for Version {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match (&self.epoch, &self.release) {
            (None, None) => write!(f, "{}", self.chunks),
            (Some(e), None) => write!(f, "{}:{}", e, self.chunks),
            (None, Some(r)) => write!(f, "{}-{}", self.chunks, r),
            (Some(e), Some(r)) => write!(f, "{}:{}-{}", e, self.chunks, r),
        }
    }
}

/// A complex version number with no specific structure.
///
/// Like [`Version`](struct.Version.html) this is a *descriptive* scheme, but it
/// is based on examples of stupidly crafted, near-lawless version numbers used
/// in the wild. Versions like this are a considerable burden to package
/// management software.
///
/// With `Mess`, groups of letters/numbers are separated by a period, but can be
/// further separated by the symbols `_-+:`.
///
/// Unfortunately, [`Chunks`](struct.Chunks.html) cannot be used here, as some
/// developers have numbers like `1.003.04` which make parsers quite sad.
///
/// Some `Mess` values have a shape that is tantalizingly close to a
/// [`SemVer`](struct.SemVer.html). Example: `1.6.0a+2014+m872b87e73dfb-1`. For
/// values like these, we can extract the semver-compatible values out with
/// [`major`][major], etc.
///
/// In general this is not guaranteed to have well-defined ordering behaviour,
/// but existing tests show sufficient consistency. [`major`][major], etc., are
/// used internally where appropriate to enhance accuracy.
///
/// [major]: #method.major.html
///
/// # Examples
///
/// TODO
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Mess {
    pub chunk: Vec<String>,
    pub next: Option<(Sep, Box<Mess>)>,
}

impl Mess {
    pub fn new(s: &str) -> Option<Mess> {
        match Mess::parse(s) {
            Ok(("", m)) => Some(m),
            _ => None,
        }
    }

    fn parse(i: &str) -> IResult<&str, Mess> {
        let (i, cs) = separated_list(char('.'), alphanumeric1)(i)?;
        let (i, next) = opt(Mess::next)(i)?;

        let m = Mess {
            chunk: cs.iter().map(|s| s.to_string()).collect(),
            next: next.map(|(s, m)| (s, Box::new(m))),
        };

        Ok((i, m))
    }

    fn next(i: &str) -> IResult<&str, (Sep, Mess)> {
        let (i, sep) = Mess::sep(i)?;
        let (i, mess) = Mess::parse(i)?;

        Ok((i, (sep, mess)))
    }

    fn sep(i: &str) -> IResult<&str, Sep> {
        alt((
            value(Sep::Colon, char(':')),
            value(Sep::Hyphen, char('-')),
            value(Sep::Plus, char('+')),
            value(Sep::Underscore, char('_')),
        ))(i)
    }

    fn pretty(&self) -> String {
        let node = self.chunk.iter().join(".");
        let next = self.next.as_ref().map(|(sep, m)| format!("{}{}", sep, m));

        node + &next.unwrap_or("".to_string())
    }
}

impl fmt::Display for Mess {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.pretty())
    }
}

/// Symbols that separate groups of digits/letters in a version number.
///
/// These are:
///
/// - A colon (:). Often denotes an "epoch".
/// - A hyphen (-).
/// - A plus (+). Stop using this outside of metadata if you are. Example: `10.2+0.93+1-1`
/// - An underscore (_). Stop using this if you are.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Sep {
    Colon,
    Hyphen,
    Plus,
    Underscore,
}

impl fmt::Display for Sep {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let c = match self {
            Sep::Colon => ':',
            Sep::Hyphen => '-',
            Sep::Plus => '+',
            Sep::Underscore => '_',
        };
        write!(f, "{}", c)
    }
}

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
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Chunk(pub Vec<Unit>);

impl Chunk {
    pub fn new() -> Chunk {
        Chunk(Vec::new())
    }

    fn parse(i: &str) -> IResult<&str, Chunk> {
        many1(Unit::parse)(i).map(|(i, cs)| (i, Chunk(cs)))
    }
}
impl PartialOrd for Chunk {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// A custom implementation.
impl Ord for Chunk {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0
            .iter()
            .zip_longest(&other.0)
            .filter_map(|eob| match eob {
                // Different from the `Ord` instance of `Chunks`, if we've
                // iterated this far and one side has fewer chunks, it must be
                // the "greater" version. A Chunk break only occurs in a switch
                // from digits to letters and vice versa, so anything "extra"
                // must be an `rc` marking or similar. Consider `1.1` compared
                // to `1.1rc1`.
                Left(_) => Some(Ordering::Less),
                Right(_) => Some(Ordering::Greater),
                // The usual case where the `Unit` types match, as in `1.2.3.4`
                // vs `1.2.4.0`.
                Both(Unit::Digits(a), Unit::Digits(b)) => match a.cmp(b) {
                    Ordering::Equal => None,
                    ord => Some(ord),
                },
                Both(Unit::Letters(a), Unit::Letters(b)) => match a.cmp(b) {
                    Ordering::Equal => None,
                    ord => Some(ord),
                },
                // The arbitrary decision to prioritize Letters over Digits has
                // the effect of allowing this instance to work for `SemVer` as
                // well as `Version`.
                Both(Unit::Digits(_), Unit::Letters(_)) => Some(Ordering::Less),
                Both(Unit::Letters(_), Unit::Digits(_)) => Some(Ordering::Greater),
            })
            .next()
            .unwrap_or(Ordering::Equal)
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

    fn pre_rel(i: &str) -> IResult<&str, Chunks> {
        let (i, _) = char('-')(i)?;
        Chunks::parse(i)
    }

    fn meta(i: &str) -> IResult<&str, Chunks> {
        let (i, _) = char('+')(i)?;
        Chunks::parse(i)
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

    #[test]
    /// The exact example from http://semver.org
    fn semver_ord() {
        let svs = vec![
            "1.0.0-alpha",
            "1.0.0-alpha.1",
            "1.0.0-alpha.beta",
            "1.0.0-beta",
            "1.0.0-beta.2",
            "1.0.0-beta.11",
            "1.0.0-rc.1",
            "1.0.0",
        ];

        svs.iter().zip(&svs[1..]).for_each(|(a, b)| {
            let x = SemVer::new(a).unwrap();
            let y = SemVer::new(b).unwrap();

            assert!(x < y, "{} < {}", x, y);
        });
    }

    #[test]
    fn good_versions() {
        let goods = vec![
            "1",
            "1.2",
            "1.0rc0",
            "1.0rc1",
            "1.1rc1",
            "44.0.2403.157-1",
            "0.25-2",
            "8.u51-1",
            "21-2",
            "7.1p1-1",
            "20150826-1",
            "1:0.10.16-3",
        ];

        for s in goods {
            assert!(SemVer::new(s).is_none(), "Shouldn't be SemVer: {}", s);
            assert_eq!(
                Some(s.to_string()),
                Version::new(s).map(|v| format!("{}", v))
            )
        }
    }

    #[test]
    fn version_ord() {
        let vs = vec!["0.9.9.9", "1.0.0.0", "1.0.0.1", "2"];

        for (a, b) in vs.iter().zip(&vs[1..]) {
            cmp_versions(a, b);
        }

        cmp_versions("1.2-5", "1.2.3-1");
        cmp_versions("1.0rc1", "1.0");
        cmp_versions("1.0", "1:1.0");
        cmp_versions("1.1", "1:1.0");
        cmp_versions("1.1", "1:1.1");
    }

    fn cmp_versions(a: &str, b: &str) {
        let x = Version::new(a).unwrap();
        let y = Version::new(b).unwrap();

        assert!(x < y, "{} < {}", x, y);
    }

    #[test]
    fn good_messes() {
        let messes = vec!["10.2+0.93+1-1", "003.03-3", "002.000-7", "20.26.1_0-2"];

        for s in messes {
            let sv = SemVer::new(s);
            let vr = Version::new(s);
            assert!(sv.is_none(), "Shouldn't be SemVer: {} -> {:#?}", s, sv);
            assert!(vr.is_none(), "Shouldn't be Version: {} -> {:#?}", s, vr);
            assert_eq!(Some(s.to_string()), Mess::new(s).map(|v| format!("{}", v)));
        }
    }
}
