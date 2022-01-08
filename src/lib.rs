//! A library for parsing and comparing software version numbers.
//!
//! We like to give version numbers to our software in a myriad of different
//! ways. Some ways follow strict guidelines for incrementing and comparison.
//! Some follow conventional wisdom and are generally self-consistent. Some are
//! just plain asinine. This library provides a means of parsing and comparing
//! *any* style of versioning, be it a nice Semantic Version like this:
//!
//! > 1.2.3-r1
//!
//! ...or a monstrosity like this:
//!
//! > 2:10.2+0.0093r3+1-1
//!
//! # Usage
//!
//! If you're parsing several version numbers that don't follow a single scheme
//! (say, as in system packages), then use the [`Versioning`] type and its
//! parser [`Versioning::new`]. Otherwise, each main type - [`SemVer`],
//! [`Version`], or [`Mess`] - can be parsed on their own via the `new` method
//! (e.g. [`SemVer::new`]).
//!
//! # Examples
//!
//! ```
//! use versions::Versioning;
//!
//! let good = Versioning::new("1.6.0").unwrap();
//! let evil = Versioning::new("1.6.0a+2014+m872b87e73dfb-1").unwrap();
//!
//! assert!(good.is_ideal());   // It parsed as a `SemVer`.
//! assert!(evil.is_complex()); // It parsed as a `Mess`.
//! assert!(good > evil);       // We can compare them anyway!
//! ```
//!
//! # Usage with `nom`
//!
//! In constructing your own [`nom`](https://lib.rs/nom) parsers, you can
//! integrate the parsers used for the types in this crate via
//! [`SemVer::parse`], [`Version::parse`], and [`Mess::parse`].
//!
//! # Features
//!
//! You can enable [`Serde`](https://serde.rs/) support for serialization and
//! deserialization with the `serde` feature.

#![allow(clippy::clippy::many_single_char_names)]
#![warn(missing_docs)]
#![doc(html_root_url = "https://docs.rs/versions/3.0.3")]

use itertools::EitherOrBoth::{Both, Left, Right};
use itertools::Itertools;
use nom::branch::alt;
use nom::bytes::complete::tag;
use nom::character::complete::{alphanumeric1, char, digit1};
use nom::combinator::{fail, map, map_res, opt, peek, recognize, value};
use nom::multi::separated_list1;
use nom::IResult;
use parsers::{alphanums, hyphenated_alphanums, unsigned};
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
use std::cmp::Ordering;
use std::cmp::Ordering::{Equal, Greater, Less};
use std::hash::{Hash, Hasher};

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
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, Eq, Clone, Default)]
pub struct SemVer {
    /// The major version.
    pub major: u32,
    /// The minor version.
    pub minor: u32,
    /// The patch version.
    pub patch: u32,
    /// `Some` implies that the inner `Vec` of the `Chunks` is not empty.
    pub pre_rel: Option<Release>,
    /// `Some` implies that the inner `String` is not empty.
    pub meta: Option<String>,
}

impl SemVer {
    /// Parse a `SemVer` from some input.
    pub fn new(s: &str) -> Option<SemVer> {
        match SemVer::parse(s) {
            Ok(("", sv)) => Some(sv),
            _ => None,
        }
    }

    /// A lossless conversion from `SemVer` to [`Version`].
    ///
    /// ```
    /// use versions::SemVer;
    ///
    /// let orig = "1.2.3-r1+git123";
    /// let ver = SemVer::new(orig).unwrap().to_version();
    ///
    /// assert_eq!("1.2.3-r1+git123", format!("{}", ver));
    /// ```
    pub fn to_version(&self) -> Version {
        let chunks = VChunks(vec![
            Chank::Numeric(self.major),
            Chank::Numeric(self.minor),
            Chank::Numeric(self.patch),
        ]);

        Version {
            epoch: None,
            chunks,
            meta: self.meta.clone(),
            release: self.pre_rel.clone(),
        }
    }

    /// A lossless conversion from `SemVer` to [`Mess`].
    ///
    /// ```
    /// use versions::SemVer;
    ///
    /// let orig = "1.2.3-r1+git123";
    /// let mess = SemVer::new(orig).unwrap().to_mess();
    ///
    /// assert_eq!(orig, format!("{}", mess));
    /// ```
    pub fn to_mess(&self) -> Mess {
        let chunks = vec![
            MChunk::Digits(self.major, self.major.to_string()),
            MChunk::Digits(self.minor, self.minor.to_string()),
            MChunk::Digits(self.patch, self.patch.to_string()),
        ];
        let next = self.pre_rel.as_ref().map(|pr| {
            let chunks = pr.0.iter().map(|c| c.mchunk()).collect();
            let next = self.meta.as_ref().map(|meta| {
                let chunks = vec![MChunk::Plain(meta.clone())];
                (Sep::Plus, Box::new(Mess { chunks, next: None }))
            });

            (Sep::Hyphen, Box::new(Mess { chunks, next }))
        });

        Mess { chunks, next }
    }

    /// Analyse the `Version` as if it's a `SemVer`.
    ///
    /// `nth_lenient` pulls a leading digit from the `Version`'s chunk if it
    /// could. If it couldn't, that chunk is some string (perhaps a git hash)
    /// and is considered as marking a beta/prerelease version. It is thus
    /// considered less than the `SemVer`.
    fn cmp_version(&self, other: &Version) -> Ordering {
        // A `Version` with a non-zero epoch value is automatically greater than
        // any `SemVer`.
        match other.epoch {
            Some(n) if n > 0 => Less,
            _ => match other.nth_lenient(0).map(|x| self.major.cmp(&x)) {
                None => Greater,
                Some(Greater) => Greater,
                Some(Less) => Less,
                Some(Equal) => match other.nth_lenient(1).map(|x| self.minor.cmp(&x)) {
                    None => Greater,
                    Some(Greater) => Greater,
                    Some(Less) => Less,
                    Some(Equal) => match other.nth_lenient(2).map(|x| self.patch.cmp(&x)) {
                        None => Greater,
                        Some(Greater) => Greater,
                        Some(Less) => Less,
                        // By this point, the major/minor/patch positions have
                        // all been equal. If there is a fourth position, its
                        // type, not its value, will determine which overall
                        // version is greater.
                        Some(Equal) => match other.chunks.0.get(3) {
                            // 1.2.3 > 1.2.3.git
                            Some(Chank::Alphanum(_)) => Greater,
                            // 1.2.3 < 1.2.3.0
                            Some(Chank::Numeric(_)) => Less,
                            None => self.pre_rel.cmp(&other.release),
                        },
                    },
                },
            },
        }
    }

    /// Do our best to compare a `SemVer` and a [`Mess`].
    ///
    /// If we're lucky, the `Mess` will be well-formed enough to pull out
    /// SemVer-like values at each position, yielding sane comparisons.
    /// Otherwise we're forced to downcast the `SemVer` into a `Mess` and let
    /// the String-based `Ord` instance of `Mess` handle things.
    fn cmp_mess(&self, other: &Mess) -> Ordering {
        match other.nth(0).map(|x| self.major.cmp(&x)) {
            None => self.to_mess().cmp(other),
            Some(Greater) => Greater,
            Some(Less) => Less,
            Some(Equal) => match other.nth(1).map(|x| self.minor.cmp(&x)) {
                None => self.to_mess().cmp(other),
                Some(Greater) => Greater,
                Some(Less) => Less,
                Some(Equal) => match other.nth(2).map(|x| self.patch.cmp(&x)) {
                    Some(Greater) => Greater,
                    Some(Less) => Less,
                    // If they've been equal up to this point, the `Mess` will
                    // by definition have more to it, meaning that it's more
                    // likely to be newer, despite its poor shape.
                    Some(Equal) => self.to_mess().cmp(other),
                    // Even if we weren't able to extract a standalone patch
                    // number, we might still be able to find a number at the
                    // head of the `Chunk` in that position.
                    None => match other.nth_chunk(2).and_then(|c| c.single_digit_lenient()) {
                        // We were very close, but in the end the `Mess` had a
                        // nonsensical value in its patch position.
                        None => self.to_mess().cmp(other),
                        Some(p) => match self.patch.cmp(&p) {
                            Greater => Greater,
                            Less => Less,
                            // This follows SemVer's rule that pre-releases have
                            // lower precedence.
                            Equal => Greater,
                        },
                    },
                },
            },
        }
    }

    /// The raw `nom` parser for [`SemVer`]. Feel free to use this in
    /// combination with other general `nom` parsers.
    pub fn parse(i: &str) -> IResult<&str, SemVer> {
        let (i, major) = parsers::unsigned(i)?;
        let (i, _) = char('.')(i)?;
        let (i, minor) = parsers::unsigned(i)?;
        let (i, _) = char('.')(i)?;
        let (i, patch) = parsers::unsigned(i)?;
        let (i, pre_rel) = opt(Release::parse)(i)?;
        let (i, meta) = opt(parsers::meta)(i)?;

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

/// For Rust, it is a Law that the following must hold:
///
/// > k1 == k2 -> hash(k1) == hash(k2)
///
/// And so this is hand-implemented, since `PartialEq` also is.
impl Hash for SemVer {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.major.hash(state);
        self.minor.hash(state);
        self.patch.hash(state);
        self.pre_rel.hash(state);
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
            Less => Less,
            Greater => Greater,
            Equal => match (&self.pre_rel, &other.pre_rel) {
                (None, None) => Equal,
                (None, _) => Greater,
                (_, None) => Less,
                (Some(ap), Some(bp)) => ap.cmp(&bp),
            },
        }
    }
}

impl std::fmt::Display for SemVer {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}.{}.{}", self.major, self.minor, self.patch)?;

        if let Some(p) = &self.pre_rel {
            write!(f, "-{}", p)?;
        }

        if let Some(m) = &self.meta {
            write!(f, "+{}", m)?;
        }

        Ok(())
    }
}

/// A version number with decent structure and comparison logic.
///
/// This is a *descriptive* scheme, meaning that it encapsulates the most
/// common, unconscious patterns that developers use when assigning version
/// numbers to their software. If not [`SemVer`], most version numbers found in
/// the wild will parse as a `Version`. These generally conform to the `x.x.x-x`
/// pattern, and may optionally have an *epoch*.
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
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, PartialEq, Eq, Hash, Clone, Default)]
pub struct Version {
    /// An optional prefix that marks that some paradigm shift in versioning has
    /// occurred between releases of some software.
    pub epoch: Option<u32>,
    /// The main sections of the `Version`. Unlike [`SemVer`], these sections
    /// are allowed to contain letters.
    pub chunks: VChunks,
    /// This either indicates a prerelease like [`SemVer`], or a "release"
    /// revision for software packages. In the latter case, a version like
    /// `1.2.3-2` implies that the software itself hasn't changed, but that this
    /// is the second bundling/release (etc.) of that particular package.
    pub release: Option<Release>,
    /// Some extra metadata that doesn't factor into comparison.
    pub meta: Option<String>,
}

impl Version {
    /// Parse a `Version` from some input.
    pub fn new(s: &str) -> Option<Version> {
        match Version::parse(s) {
            Ok(("", v)) => Some(v),
            _ => None,
        }
    }

    /// Try to extract a position from the `Version` as a nice integer, as if it
    /// were a [`SemVer`].
    ///
    /// ```
    /// use versions::Version;
    ///
    /// let mess = Version::new("1:2.a.4.5.6.7-r1").unwrap();
    /// assert_eq!(Some(2), mess.nth(0));
    /// assert_eq!(None, mess.nth(1));
    /// assert_eq!(Some(4), mess.nth(2));
    /// ```
    pub fn nth(&self, n: usize) -> Option<u32> {
        self.chunks.0.get(n).and_then(Chank::single_digit)
    }

    /// Like `nth`, but pulls a number even if it was followed by letters.
    pub fn nth_lenient(&self, n: usize) -> Option<u32> {
        self.chunks.0.get(n).and_then(Chank::single_digit_lenient)
    }

    /// A lossless conversion from `Version` to [`Mess`].
    ///
    /// ```
    /// use versions::Version;
    ///
    /// let orig = "1:1.2.3-r1";
    /// let mess = Version::new(orig).unwrap().to_mess();
    ///
    /// assert_eq!(orig, format!("{}", mess));
    /// ```
    pub fn to_mess(&self) -> Mess {
        match self.epoch {
            None => self.to_mess_continued(),
            Some(e) => {
                let chunks = vec![MChunk::Digits(e, e.to_string())];
                let next = Some((Sep::Colon, Box::new(self.to_mess_continued())));
                Mess { chunks, next }
            }
        }
    }

    /// Convert to a `Mess` without considering the epoch.
    fn to_mess_continued(&self) -> Mess {
        let chunks = self.chunks.0.iter().map(|c| c.mchunk()).collect();
        let next = self.release.as_ref().map(|cs| {
            let chunks = cs.0.iter().map(|c| c.mchunk()).collect();
            (Sep::Hyphen, Box::new(Mess { chunks, next: None }))
        });
        Mess { chunks, next }
    }

    /// If we're lucky, we can pull specific numbers out of both inputs and
    /// accomplish the comparison without extra allocations.
    fn cmp_mess(&self, other: &Mess) -> Ordering {
        match self.epoch {
            Some(e) if e > 0 && other.chunks.len() == 1 => match &other.next {
                // A near-nonsense case where a `Mess` is comprised of a single
                // digit and nothing else. In this case its epoch would be
                // considered 0.
                None => Greater,
                Some((Sep::Colon, m)) => match other.nth(0) {
                    // The Mess's epoch is a letter, etc.
                    None => Greater,
                    Some(me) => match e.cmp(&me) {
                        Equal => Version::cmp_mess_continued(self, &m),
                        ord => ord,
                    },
                },
                // Similar nonsense, where the Mess had a single *something*
                // before some non-colon separator. We then consider the epoch
                // to be 0.
                Some(_) => Greater,
            },
            // The `Version` has an epoch but the `Mess` doesn't. Or if it does,
            // it's malformed.
            Some(e) if e > 0 => Greater,
            _ => Version::cmp_mess_continued(self, &other),
        }
    }

    /// It's assumed the epoch check has already been done, and we're comparing
    /// the main parts of each version now.
    fn cmp_mess_continued(&self, other: &Mess) -> Ordering {
        (0..)
            .find_map(
                |n| match self.nth(n).and_then(|x| other.nth(n).map(|y| x.cmp(&y))) {
                    // Sane values can't be extracted from one or both of the
                    // arguments.
                    None => Some(self.to_mess().cmp(other)),
                    Some(Greater) => Some(Greater),
                    Some(Less) => Some(Less),
                    // Continue to the next position.
                    Some(Equal) => None,
                },
            )
            .unwrap_or_else(|| self.to_mess().cmp(other))
    }

    /// The raw `nom` parser for [`Version`]. Feel free to use this in
    /// combination with other general `nom` parsers.
    pub fn parse(i: &str) -> IResult<&str, Version> {
        let (i, epoch) = opt(Version::epoch)(i)?;
        let (i, chunks) = VChunks::parse(i)?;
        let (i, release) = opt(Release::parse)(i)?;
        let (i, meta) = opt(parsers::meta)(i)?;

        let v = Version {
            epoch,
            chunks,
            meta,
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
            Equal => match self.chunks.cmp(&other.chunks) {
                Equal => self.release.cmp(&other.release),
                ord => ord,
            },
            ord => ord,
        }
    }
}

impl std::fmt::Display for Version {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if let Some(e) = self.epoch {
            write!(f, "{}:", e)?;
        }

        write!(f, "{}", self.chunks)?;

        if let Some(r) = &self.release {
            write!(f, "-{}", r)?;
        }

        if let Some(m) = &self.meta {
            write!(f, "+{}", m)?;
        }

        Ok(())
    }
}

/// A complex version number with no specific structure.
///
/// Like [`Version`] this is a *descriptive* scheme, but it is based on examples
/// of stupidly crafted, near-lawless version numbers used in the wild. Versions
/// like this are a considerable burden to package management software.
///
/// With `Mess`, groups of letters/numbers are separated by a period, but can be
/// further separated by the symbols `_-+:`.
///
/// Unfortunately, [`Chunks`] cannot be used here, as some developers have
/// numbers like `1.003.04` which make parsers quite sad.
///
/// Some `Mess` values have a shape that is tantalizingly close to a [`SemVer`].
/// Example: `1.6.0a+2014+m872b87e73dfb-1`. For values like these, we can
/// extract the SemVer-compatible values out with [`Mess::nth`].
///
/// In general this is not guaranteed to have well-defined ordering behaviour,
/// but existing tests show sufficient consistency. [`Mess::nth`] is used
/// internally where appropriate to enhance accuracy.
///
/// # Examples
///
/// ```
/// use versions::{Mess, SemVer, Version};
///
/// let mess = "20.0026.1_0-2+0.93";
///
/// let s = SemVer::new(mess);
/// let v = Version::new(mess);
/// let m = Mess::new(mess);
///
/// assert!(s.is_none());
/// assert!(v.is_none());
/// assert_eq!(Some(mess.to_string()), m.map(|v| format!("{}", v)));
/// ```
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, PartialEq, Eq, Hash, Clone, Default)]
pub struct Mess {
    /// The first section of a `Mess`.
    pub chunks: Vec<MChunk>,
    /// The rest of the `Mess`.
    pub next: Option<(Sep, Box<Mess>)>,
}

impl Mess {
    /// Parse a `Mess` from some input.
    pub fn new(s: &str) -> Option<Mess> {
        match Mess::parse(s) {
            Ok(("", m)) => Some(m),
            _ => None,
        }
    }

    /// Try to extract a position from the `Mess` as a nice integer, as if it
    /// were a [`SemVer`].
    ///
    /// ```
    /// use versions::Mess;
    ///
    /// let mess = Mess::new("1.6a.0+2014+m872b87e73dfb-1").unwrap();
    /// assert_eq!(Some(1), mess.nth(0));
    /// assert_eq!(None, mess.nth(1));
    /// assert_eq!(Some(0), mess.nth(2));
    /// ```
    pub fn nth(&self, x: usize) -> Option<u32> {
        self.chunks.get(x).and_then(|chunk| match chunk {
            MChunk::Digits(i, _) => Some(*i),
            _ => None,
        })
    }

    /// Like [`Mess::nth`], but tries to parse out a full [`Chunk`] instead.
    fn nth_chunk(&self, x: usize) -> Option<Chank> {
        let chunk = self.chunks.get(x)?.text();
        let (i, c) = Chank::parse_without_hyphens(chunk).ok()?;
        match i {
            "" => Some(c),
            _ => None,
        }
    }

    /// The raw `nom` parser for [`Mess`]. Feel free to use this in combination
    /// with other general `nom` parsers.
    pub fn parse(i: &str) -> IResult<&str, Mess> {
        let (i, chunks) = separated_list1(char('.'), MChunk::parse)(i)?;
        let (i, next) = opt(Mess::next)(i)?;

        let m = Mess {
            chunks,
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
}

impl PartialOrd for Mess {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Build metadata does not affect version precendence, and pre-release versions
/// have *lower* precedence than normal versions.
impl Ord for Mess {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.chunks.cmp(&other.chunks) {
            Equal => {
                let an = self.next.as_ref().map(|(_, m)| m);
                let bn = other.next.as_ref().map(|(_, m)| m);
                an.cmp(&bn)
            }
            ord => ord,
        }
    }
}

impl std::fmt::Display for Mess {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.chunks.iter().join("."))?;

        if let Some((sep, m)) = &self.next {
            write!(f, "{}{}", sep, m)?;
        }

        Ok(())
    }
}

/// Possible values of a section of a [`Mess`].
///
/// A numeric value is extracted if it could be, alongside the original text it
/// came from. This preserves both `Ord` and `Display` behaviour for versions
/// like `1.003.0`.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum MChunk {
    /// A nice numeric value.
    Digits(u32, String),
    /// A numeric value preceeded by an `r`, indicating a revision.
    Rev(u32, String),
    /// Anything else.
    Plain(String),
}

impl MChunk {
    /// Extract the original `String`, no matter which variant it parsed into.
    pub fn text(&self) -> &str {
        match self {
            MChunk::Digits(_, s) => s,
            MChunk::Rev(_, s) => s,
            MChunk::Plain(s) => s,
        }
    }

    fn parse(i: &str) -> IResult<&str, MChunk> {
        alt((MChunk::digits, MChunk::rev, MChunk::plain))(i)
    }

    fn digits(i: &str) -> IResult<&str, MChunk> {
        let (i, (u, s)) = map_res(recognize(digit1), |s: &str| {
            s.parse::<u32>().map(|u| (u, s))
        })(i)?;
        let (i, _) = alt((peek(recognize(char('.'))), peek(recognize(Mess::sep))))(i)?;
        let chunk = MChunk::Digits(u, s.to_string());
        Ok((i, chunk))
    }

    fn rev(i: &str) -> IResult<&str, MChunk> {
        let (i, _) = tag("r")(i)?;
        let (i, (u, s)) = map_res(recognize(digit1), |s: &str| {
            s.parse::<u32>().map(|u| (u, s))
        })(i)?;
        let (i, _) = alt((peek(recognize(char('.'))), peek(recognize(Mess::sep))))(i)?;
        let chunk = MChunk::Rev(u, format!("r{}", s));
        Ok((i, chunk))
    }

    fn plain(i: &str) -> IResult<&str, MChunk> {
        let (i, s) = alphanumeric1(i)?;
        let chunk = MChunk::Plain(s.to_string());
        Ok((i, chunk))
    }
}

impl PartialOrd for MChunk {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for MChunk {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            // Normal cases.
            (MChunk::Digits(a, _), MChunk::Digits(b, _)) => a.cmp(b),
            (MChunk::Rev(a, _), MChunk::Rev(b, _)) => a.cmp(b),
            // If I'm a concrete number and you're just a revision, then I'm greater no matter what.
            (MChunk::Digits(_, _), MChunk::Rev(_, _)) => Greater,
            (MChunk::Rev(_, _), MChunk::Digits(_, _)) => Less,
            // There's no sensible pairing, so we fall back to String-based comparison.
            (a, b) => a.text().cmp(b.text()),
        }
    }
}

impl std::fmt::Display for MChunk {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            MChunk::Digits(_, s) => write!(f, "{}", s),
            MChunk::Rev(_, s) => write!(f, "{}", s),
            MChunk::Plain(s) => write!(f, "{}", s),
        }
    }
}

/// Symbols that separate groups of digits/letters in a version number. Used in
/// the [`Mess`].
///
/// These are:
///
/// - A colon (:). Often denotes an "epoch".
/// - A hyphen (-).
/// - A plus (+). Stop using this outside of metadata if you are. Example: `10.2+0.93+1-1`
/// - An underscore (_). Stop using this if you are.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Sep {
    /// `:`
    Colon,
    /// `-`
    Hyphen,
    /// `+`
    Plus,
    /// `_`
    Underscore,
}

impl std::fmt::Display for Sep {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let c = match self {
            Sep::Colon => ':',
            Sep::Hyphen => '-',
            Sep::Plus => '+',
            Sep::Underscore => '_',
        };
        write!(f, "{}", c)
    }
}

/// [`Chunk`]s that have comparison behaviour according to SemVer's rules for
/// prereleases.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Release(pub Vec<Chank>);

impl Release {
    fn parse(i: &str) -> IResult<&str, Release> {
        let (i, _) = char('-')(i)?;
        map(separated_list1(char('.'), Chank::parse), Release)(i)
    }
}

impl PartialOrd for Release {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Release {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0
            .iter()
            .zip_longest(&other.0)
            .find_map(|eob| match eob {
                Both(a, b) => match a.cmp_semver(&b) {
                    Less => Some(Less),
                    Greater => Some(Greater),
                    Equal => None,
                },
                // From the Semver spec: A larger set of pre-release fields has
                // a higher precedence than a smaller set, if all the preceding
                // identifiers are equal.
                Left(_) => Some(Greater),
                Right(_) => Some(Less),
            })
            .unwrap_or(Equal)
    }
}

impl std::fmt::Display for Release {
    // FIXME Fri Jan  7 11:44:50 2022
    //
    // Use `itersperse` here once it stabilises.
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self.0.as_slice() {
            [] => Ok(()),
            [c] => write!(f, "{}", c),
            [c, rest @ ..] => {
                write!(f, "{}", c)?;

                for r in rest {
                    write!(f, ".{}", r)?;
                }

                Ok(())
            }
        }
    }
}

/// [`Chunk`]s that have a comparison behaviour specific to [`Version`].
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, PartialEq, Eq, Hash, Clone, Default)]
pub struct VChunks(pub Vec<Chank>);

impl VChunks {
    // Intended for parsing a `Version`.
    fn parse(i: &str) -> IResult<&str, VChunks> {
        map(
            separated_list1(char('.'), Chank::parse_without_hyphens),
            VChunks,
        )(i)
    }
}

impl PartialOrd for VChunks {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for VChunks {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0
            .iter()
            .zip_longest(&other.0)
            .find_map(|eob| match eob {
                Both(a, b) => match a.cmp_lenient(&b) {
                    Less => Some(Less),
                    Greater => Some(Greater),
                    Equal => None,
                },
                // From the Semver spec: A larger set of pre-release fields has
                // a higher precedence than a smaller set, if all the preceding
                // identifiers are equal.
                Left(_) => Some(Greater),
                Right(_) => Some(Less),
            })
            .unwrap_or(Equal)
    }
}

impl std::fmt::Display for VChunks {
    // FIXME Fri Jan  7 11:44:50 2022
    //
    // Use `itersperse` here once it stabilises.
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self.0.as_slice() {
            [] => Ok(()),
            [c] => write!(f, "{}", c),
            [c, rest @ ..] => {
                write!(f, "{}", c)?;

                for r in rest {
                    write!(f, ".{}", r)?;
                }

                Ok(())
            }
        }
    }
}

/// A logical unit of a version number.
///
/// Either entirely numerical (with no leading zeroes) or entirely
/// alphanumerical (with a free mixture of numbers, letters, and hyphens).
///
/// Groups of these (i.e. [`Chunks`]) are separated by periods to form a full
/// section of a version number.
///
/// # Examples
///
/// - `1`
/// - `20150826`
/// - `r3`
/// - `0rc1-abc3`
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Chank {
    /// A nice, pure number.
    Numeric(u32),
    /// A mixture of letters, numbers, and hyphens.
    Alphanum(String),
}

impl Chank {
    /// If this `Chunk` is made up of a single digit, then pull out the inner
    /// value.
    ///
    /// ```
    /// use versions::{Chunk, Unit};
    ///
    /// let v = Chunk(vec![Unit::Digits(1)]);
    /// assert_eq!(Some(1), v.single_digit());
    ///
    /// let v = Chunk(vec![Unit::Letters("abc".to_string())]);
    /// assert_eq!(None, v.single_digit());
    ///
    /// let v = Chunk(vec![Unit::Digits(1), Unit::Letters("abc".to_string())]);
    /// assert_eq!(None, v.single_digit());
    /// ```
    pub fn single_digit(&self) -> Option<u32> {
        match self {
            Chank::Numeric(n) => Some(*n),
            Chank::Alphanum(_) => None,
        }
    }

    /// Like [`Chunk::single_digit`], but will grab a leading `u32` even if
    /// followed by letters.
    ///
    /// ```
    /// use versions::{Chunk, Unit};
    ///
    /// let v = Chunk(vec![Unit::Digits(1)]);
    /// assert_eq!(Some(1), v.single_digit_lenient());
    ///
    /// let v = Chunk(vec![Unit::Letters("abc".to_string())]);
    /// assert_eq!(None, v.single_digit_lenient());
    ///
    /// let v = Chunk(vec![Unit::Digits(0), Unit::Letters("a".to_string())]);
    /// assert_eq!(Some(0), v.single_digit_lenient());
    /// ```
    pub fn single_digit_lenient(&self) -> Option<u32> {
        match self {
            Chank::Numeric(n) => Some(*n),
            Chank::Alphanum(s) => unsigned(s).ok().map(|(_, n)| n),
        }
    }

    fn parse(i: &str) -> IResult<&str, Chank> {
        alt((Chank::alphanum, Chank::numeric))(i)
    }

    fn parse_without_hyphens(i: &str) -> IResult<&str, Chank> {
        alt((Chank::alphanum_without_hyphens, Chank::numeric))(i)
    }

    // A clever interpretation of the grammar of "alphanumeric identifier".
    // Instead of having a big, composed parser that structurally accounts for
    // the presence of a "non-digit", we just check for one after the fact.
    fn alphanum(i: &str) -> IResult<&str, Chank> {
        let (i2, ids) = hyphenated_alphanums(i)?;

        if ids.contains(|c: char| c.is_ascii_alphabetic() || c == '-') {
            Ok((i2, Chank::Alphanum(ids.to_string())))
        } else {
            fail(i)
        }
    }

    fn alphanum_without_hyphens(i: &str) -> IResult<&str, Chank> {
        let (i2, ids) = alphanums(i)?;

        if ids.contains(|c: char| c.is_ascii_alphabetic()) {
            Ok((i2, Chank::Alphanum(ids.to_string())))
        } else {
            fail(i)
        }
    }

    fn numeric(i: &str) -> IResult<&str, Chank> {
        map(unsigned, Chank::Numeric)(i)
    }

    fn mchunk(&self) -> MChunk {
        // FIXME Fri Jan  7 12:34:24 2022
        //
        // Is there going to be an issue here, having not accounted for an `r`?
        match self {
            Chank::Numeric(n) => MChunk::Digits(*n, n.to_string()),
            Chank::Alphanum(s) => MChunk::Plain(s.clone()),
        }
        // match self.0.as_slice() {
        //     [] => None,
        //     [Unit::Digits(u)] => Some(MChunk::Digits(*u, u.to_string())),
        //     [Unit::Letters(s), Unit::Digits(u)] if s == "r" => {
        //         Some(MChunk::Rev(*u, format!("r{}", u)))
        //     }
        //     [Unit::Letters(s)] => Some(MChunk::Plain(s.clone())),
        //     _ => Some(MChunk::Plain(format!("{}", self))),
        // }
    }

    fn cmp_semver(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Chank::Numeric(a), Chank::Numeric(b)) => a.cmp(&b),
            (Chank::Numeric(_), Chank::Alphanum(_)) => Less,
            (Chank::Alphanum(_), Chank::Numeric(_)) => Greater,
            (Chank::Alphanum(a), Chank::Alphanum(b)) => a.cmp(&b),
        }
    }

    fn cmp_lenient(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Chank::Numeric(a), Chank::Numeric(b)) => a.cmp(&b),
            (a @ Chank::Alphanum(x), b @ Chank::Alphanum(y)) => {
                match (a.single_digit_lenient(), b.single_digit_lenient()) {
                    (Some(i), Some(j)) => i.cmp(&j),
                    _ => x.cmp(&y),
                }
            }
            (Chank::Numeric(n), b @ Chank::Alphanum(_)) => match b.single_digit_lenient() {
                None => Greater,
                Some(m) => match n.cmp(&m) {
                    // 1.2.0 > 1.2.0rc1
                    Equal => Greater,
                    c => c,
                },
            },
            (a @ Chank::Alphanum(_), Chank::Numeric(n)) => match a.single_digit_lenient() {
                None => Less,
                Some(m) => match m.cmp(&n) {
                    // 1.2.0rc1 < 1.2.0
                    Equal => Less,
                    c => c,
                },
            },
        }
    }
}

impl std::fmt::Display for Chank {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Chank::Numeric(n) => write!(f, "{}", n),
            Chank::Alphanum(a) => write!(f, "{}", a),
        }
    }
}

/// A top-level Versioning type which acts as a wrapper for the more specific
/// types.
///
/// # Examples
///
/// ```
/// use versions::Versioning;
///
/// let a = Versioning::new("1.2.3-1").unwrap();   // SemVer.
/// let b = Versioning::new("1.2.3r1").unwrap();   // Not SemVer but good enough.
/// let c = Versioning::new("000.007-1").unwrap(); // Garbage.
///
/// assert!(a.is_ideal());
/// assert!(b.is_general());
/// assert!(c.is_complex());
/// ```
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Versioning {
    /// Follows good parsing and comparison rules.
    Ideal(SemVer),
    /// A little more permissive than [`SemVer`].
    General(Version),
    /// Hope that you need not venture here.
    Complex(Mess),
}

impl Versioning {
    /// Create a `Versioning` by attempting to parse the input first as
    /// [`SemVer`], then as a [`Version`], and finally as a [`Mess`].
    pub fn new(s: &str) -> Option<Versioning> {
        SemVer::new(s)
            .map(Versioning::Ideal)
            .or_else(|| Version::new(s).map(Versioning::General))
            .or_else(|| Mess::new(s).map(Versioning::Complex))
    }

    /// A short-hand for detecting an inner [`SemVer`].
    pub fn is_ideal(&self) -> bool {
        matches!(self, Versioning::Ideal(_))
    }

    /// A short-hand for detecting an inner [`Version`].
    pub fn is_general(&self) -> bool {
        matches!(self, Versioning::General(_))
    }

    /// A short-hand for detecting an inner [`Mess`].
    pub fn is_complex(&self) -> bool {
        matches!(self, Versioning::Complex(_))
    }

    /// Try to extract a position from the `Versioning` as a nice integer, as if it
    /// were a [`SemVer`].
    ///
    /// ```
    /// use versions::Versioning;
    ///
    /// let semver = Versioning::new("1.2.3-r1+git123").unwrap();
    /// assert!(semver.is_ideal());
    /// assert_eq!(Some(1), semver.nth(0));
    /// assert_eq!(Some(2), semver.nth(1));
    /// assert_eq!(Some(3), semver.nth(2));
    ///
    /// let version = Versioning::new("1:2.a.4.5.6.7-r1").unwrap();
    /// assert!(version.is_general());
    /// assert_eq!(Some(2), version.nth(0));
    /// assert_eq!(None, version.nth(1));
    /// assert_eq!(Some(4), version.nth(2));
    ///
    /// let mess = Versioning::new("1.6a.0+2014+m872b87e73dfb-1").unwrap();
    /// assert!(mess.is_complex());
    /// assert_eq!(Some(1), mess.nth(0));
    /// assert_eq!(None, mess.nth(1));
    /// assert_eq!(Some(0), mess.nth(2));
    /// ```
    pub fn nth(&self, n: usize) -> Option<u32> {
        match self {
            Versioning::Ideal(s) if n == 0 => Some(s.major),
            Versioning::Ideal(s) if n == 1 => Some(s.minor),
            Versioning::Ideal(s) if n == 2 => Some(s.patch),
            Versioning::Ideal(_) => None,
            Versioning::General(v) => v.nth(n),
            Versioning::Complex(m) => m.nth(n),
        }
    }
}

impl PartialOrd for Versioning {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Versioning {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            // Obvious comparisons when the types are the same.
            (Versioning::Ideal(a), Versioning::Ideal(b)) => a.cmp(b),
            (Versioning::General(a), Versioning::General(b)) => a.cmp(b),
            (Versioning::Complex(a), Versioning::Complex(b)) => a.cmp(b),
            // SemVer and Version can compare nicely.
            (Versioning::Ideal(a), Versioning::General(b)) => a.cmp_version(b),
            (Versioning::General(a), Versioning::Ideal(b)) => b.cmp_version(a).reverse(),
            // If we're lucky, the `Mess` is well-formed enough to pull
            // SemVer-like values out of its initial positions. Otherwise we
            // need to downcast the `SemVer` into a `Mess` and hope for the
            // best.
            (Versioning::Ideal(a), Versioning::Complex(b)) => a.cmp_mess(b),
            (Versioning::Complex(a), Versioning::Ideal(b)) => b.cmp_mess(a).reverse(),
            // Same as above - we might get lucky, we might not.
            // The lucky fate means no extra allocations.
            (Versioning::General(a), Versioning::Complex(b)) => a.cmp_mess(b),
            (Versioning::Complex(a), Versioning::General(b)) => b.cmp_mess(a).reverse(),
        }
    }
}

impl std::fmt::Display for Versioning {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Versioning::Ideal(s) => write!(f, "{}", s),
            Versioning::General(v) => write!(f, "{}", v),
            Versioning::Complex(m) => write!(f, "{}", m),
        }
    }
}

impl Default for Versioning {
    fn default() -> Self {
        Self::Ideal(SemVer::default())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn chanks() {
        assert_eq!(Ok(("", Chank::Numeric(123))), Chank::parse("123"));
        assert_eq!(
            Ok(("", Chank::Alphanum("123a".to_string()))),
            Chank::parse("123a")
        );
        assert_eq!(
            Ok(("", Chank::Alphanum("123-456".to_string()))),
            Chank::parse("123-456")
        );
        assert_eq!(
            Ok(("", Chank::Alphanum("00a".to_string()))),
            Chank::parse("00a")
        );
    }

    #[test]
    fn official_semvers() {
        let goods = vec![
            "0.1.0",
            "1.2.3",
            "1.2.3-1",
            "1.2.3-alpha",
            "1.2.3-alpha.2",
            "1.2.3+a1b2c3.1",
            "1.2.3-alpha.2+a1b2c3.1",
            "1.0.0-x-y-z.-",
            "1.0.0-alpha+001",
            "1.0.0+21AF26D3---117B344092BD",
        ];

        for s in goods {
            assert_eq!(
                Some(s.to_string()),
                SemVer::new(s).map(|sv| format!("{}", sv))
            )
        }
    }

    #[test]
    fn good_semvers() {
        let goods = vec![
            "0.4.8-1",
            "7.42.13-4",
            "2.1.16102-2",
            "2.2.1-b05",
            "1.11.0+20200830-1",
        ];

        for s in goods {
            assert_eq!(
                Some(s.to_string()),
                SemVer::new(s).map(|sv| format!("{}", sv))
            )
        }
    }

    #[test]
    fn tricky_semvers() {
        let v = "1.2.2-00a";

        assert_eq!("", SemVer::parse(v).unwrap().0);
    }

    #[test]
    fn bad_semvers() {
        let bads = vec![
            "1",
            "1.2",
            "a.b.c",
            "1.01.1",
            "1.2.3+a1b!2c3.1",
            "",
            "1.2.3 ",
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

        for (a, b) in svs.iter().zip(&svs[1..]) {
            let x = SemVer::new(a).unwrap();
            let y = SemVer::new(b).unwrap();

            assert!(x < y, "{} < {}", x, y);
        }
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
            "8.64.0.81-1",
            "1:3.20-1",
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
    fn bad_versions() {
        let bads = vec!["", "1.2 "];

        bads.iter().for_each(|b| assert_eq!(None, Version::new(b)));
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
        let messes = vec![
            "10.2+0.93+1-1",
            "003.03-3",
            "002.000-7",
            "20.26.1_0-2",
            "1.6.0a+2014+m872b87e73dfb-1",
            "0.17.0+r8+gc41db5f1-1",
            "0.17.0+r157+g584760cf-1",
            "1.002.3+r003",
            "1.3.00.16851-1",
            "5.2.458699.0906-1",
        ];

        for s in messes {
            let sv = SemVer::new(s);
            let vr = Version::new(s);
            assert!(sv.is_none(), "Shouldn't be SemVer: {} -> {:#?}", s, sv);
            assert!(vr.is_none(), "Shouldn't be Version: {} -> {:#?}", s, vr);
            assert_eq!(Some(s.to_string()), Mess::new(s).map(|v| format!("{}", v)));
        }
    }

    #[test]
    fn bad_messes() {
        let bads = vec!["", "003.03-3 "];

        bads.iter().for_each(|b| assert_eq!(None, Mess::new(b)));
    }

    #[test]
    fn mess_ord() {
        let messes = vec![
            "10.2+0.93+1-1",
            "10.2+0.93+1-2",
            "10.2+0.93+2-1",
            "10.2+0.94+1-1",
            "10.3+0.93+1-1",
            "11.2+0.93+1-1",
            "12",
        ];

        for (a, b) in messes.iter().zip(&messes[1..]) {
            cmp_messes(a, b);
        }
    }

    fn cmp_messes(a: &str, b: &str) {
        let x = Mess::new(a).unwrap();
        let y = Mess::new(b).unwrap();

        assert!(x < y, "{} < {}", x, y);
    }

    #[test]
    fn equality() {
        let vers = vec![
            "1:3.20.1-1",
            "1.3.00.25560-1",
            "150_28-3",
            "1.0.r15.g3fc772c-5",
            "0.88-2",
        ];

        for v in vers {
            let x = Versioning::new(v).unwrap();

            assert_eq!(Equal, x.cmp(&x));
        }
    }

    #[test]
    fn mixed_comparisons() {
        cmp_versioning("1.2.3", "1.2.3.0");
        cmp_versioning("1.2.3.git", "1.2.3");
        cmp_versioning("1.2.2r1-1", "1.2.3-1");
        cmp_versioning("1.2.3-1", "1.2.4r1-1");
        cmp_versioning("1.2.3-1", "2+0007-1");
        cmp_versioning("1.2.3r1-1", "2+0007-1");
        cmp_versioning("1.2-5", "1.2.3-1");
        cmp_versioning("1.6.0a+2014+m872b87e73dfb-1", "1.6.0-1");
        cmp_versioning("1.11.0.git.20200404-1", "1.11.0+20200830-1");
        cmp_versioning("0.17.0+r8+gc41db5f1-1", "0.17.0+r157+g584760cf-1");
        cmp_versioning("2.2.3", "10e");
        cmp_versioning("e.2.3", "1.2.3");
        cmp_versioning("0.4.8-1", "0.4.9-1");
        cmp_versioning("2.1.16102-2", "2.1.17627-1");
        cmp_versioning("8.64.0.81-1", "8.65.0.78-1");
        cmp_versioning("1.3.00.16851-1", "1.3.00.25560-1");
        cmp_versioning("1:3.20-1", "1:3.20.1-1");
        cmp_versioning("5.2.458699.0906-1", "5.3.472687.1012-1");
        cmp_versioning("1.2.3", "1:1.2.0");
    }

    fn cmp_versioning(a: &str, b: &str) {
        let x = Versioning::new(a).unwrap();
        let y = Versioning::new(b).unwrap();

        assert!(
            x < y,
            "\nAttempted: {} < {}\nLesser: {:?}\nGreater: {:?}\nThinks: {:?}",
            x,
            y,
            x,
            y,
            x.cmp(&y)
        );
    }

    #[test]
    fn parsing_sanity() {
        assert_eq!(Ok(34), "0034".parse::<u32>())
    }
}
