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
//! (say, as in system packages), then use the
//! [`Versioning`](enum.Versioning.html) type and its parser
//! [`Versioning::new`](enum.Versioning.html#method.new). Otherwise, each main
//! type - [`SemVer`][semver], [`Version`][version], or [`Mess`][mess] - can be
//! parsed on their own via the `new` method (e.g.
//! [`SemVer::new`](struct.SemVer.html#method.new)).
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
//! [semver]: struct.SemVer.html
//! [version]: struct.Version.html
//! [mess]: struct.Mess.html

#![doc(html_root_url = "https://docs.rs/versions/1.0.1")]

use itertools::EitherOrBoth::{Both, Left, Right};
use itertools::Itertools;
use nom::branch::alt;
use nom::bytes::complete::tag;
use nom::character::complete::{alpha1, char};
use nom::combinator::{map, map_res, opt, value};
use nom::multi::{many1, separated_nonempty_list};
use nom::IResult;
use nonempty::NonEmpty;
use std::cmp::Ordering;
use std::cmp::Ordering::{Equal, Greater, Less};
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
    /// Parse a `SemVer` from some input.
    pub fn new(s: &str) -> Option<SemVer> {
        match SemVer::parse(s) {
            Ok(("", sv)) => Some(sv),
            _ => None,
        }
    }

    /// A lossy conversion from `SemVer` to [`Version`](struct.Version.html).
    ///
    /// **Note:** Drops `SemVer` metadata!
    ///
    /// ```
    /// use versions::SemVer;
    ///
    /// let orig = "1.2.3-r1+git123";
    /// let ver = SemVer::new(orig).unwrap().to_version();
    ///
    /// assert_eq!("1.2.3-r1", format!("{}", ver));
    /// ```
    pub fn to_version(&self) -> Version {
        let chunks = Chunks(vec![
            Chunk(vec![Unit::Digits(self.major)]),
            Chunk(vec![Unit::Digits(self.minor)]),
            Chunk(vec![Unit::Digits(self.patch)]),
        ]);

        Version {
            epoch: None,
            chunks,
            release: self.pre_rel.clone(),
        }
    }

    /// A lossless conversion from `SemVer` to [`Mess`](struct.Mess.html).
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
            MChunk::Digit(self.major, self.major.to_string()),
            MChunk::Digit(self.minor, self.minor.to_string()),
            MChunk::Digit(self.patch, self.patch.to_string()),
        ];
        let next = self.pre_rel.as_ref().map(|pr| {
            let chunks = pr.0.iter().map(|c| c.mchunk()).collect();
            let next = self.meta.as_ref().map(|meta| {
                let chunks = meta.0.iter().map(|m| m.mchunk()).collect();
                (Sep::Plus, Box::new(Mess { chunks, next: None }))
            });

            (Sep::Hyphen, Box::new(Mess { chunks, next }))
        });

        Mess { chunks, next }
    }

    /// We try our best to analyse the `Version` as if it's a `SemVer`. If we
    /// can't, we downcast the `SemVer` to a `Version` and restart the process.
    /// The downcast causes some allocation, and the casted value isn't reused.
    fn cmp_version(&self, other: &Version) -> Ordering {
        // A `Version` with a non-zero epoch value is automatically greater than
        // any `SemVer`.
        match other.epoch {
            Some(n) if n > 0 => Greater,
            _ => match other.nth(0).map(|x| self.major.cmp(&x)) {
                None => self.to_version().cmp(other),
                Some(Greater) => Greater,
                Some(Less) => Less,
                Some(Equal) => match other.nth(1).map(|x| self.minor.cmp(&x)) {
                    None => self.to_version().cmp(other),
                    Some(Greater) => Greater,
                    Some(Less) => Less,
                    Some(Equal) => match other.nth(2).map(|x| self.patch.cmp(&x)) {
                        None => self.to_version().cmp(other),
                        Some(Greater) => Greater,
                        Some(Less) => Less,
                        Some(Equal) => self.pre_rel.cmp(&other.release),
                    },
                },
            },
        }
    }

    /// Do our best to compare a `SemVer` and a [`Mess`](struct.Mess.html).
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
    /// Parse a `Version` from some input.
    pub fn new(s: &str) -> Option<Version> {
        match Version::parse(s) {
            Ok(("", v)) => Some(v),
            _ => None,
        }
    }

    /// Try to extract a position from the `Version` as a nice integer, as if it
    /// were a [`SemVer`](struct.SemVer.html).
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
        self.chunks.0.get(n).and_then(Chunk::single_digit)
    }

    /// A lossless conversion from `Version` to [`Mess`](struct.Mess.html).
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
                let chunks = vec![MChunk::Digit(e, e.to_string())];
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
            .filter_map(
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
            .next()
            .unwrap_or_else(|| self.to_mess().cmp(other))
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
            Equal => match self.chunks.cmp(&other.chunks) {
                Equal => self.release.cmp(&other.release),
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
/// values like these, we can extract the SemVer-compatible values out with
/// [`nth`][nth].
///
/// In general this is not guaranteed to have well-defined ordering behaviour,
/// but existing tests show sufficient consistency. [`nth`][nth] is used
/// internally where appropriate to enhance accuracy.
///
/// [nth]: #method.nth.html
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
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Mess {
    pub chunks: Vec<MChunk>,
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
    /// were a [`SemVer`](struct.SemVer.html).
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
            MChunk::Digit(i, _) => Some(*i),
            _ => None,
        })
    }

    /// Like [`nth`](#method.nth), but tries to parse out a full
    /// [`Chunk`](struct.Chunk.html) instead.
    fn nth_chunk(&self, x: usize) -> Option<Chunk> {
        let chunk = self.chunks.get(x)?.text();
        let (i, c) = Chunk::parse(chunk).ok()?;
        match i {
            "" => Some(c),
            _ => None,
        }
    }

    fn parse(i: &str) -> IResult<&str, Mess> {
        let (i, chunks) = separated_nonempty_list(char('.'), MChunk::parse)(i)?;
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

    fn pretty(&self) -> String {
        let node = self.chunks.iter().join(".");
        let next = self.next.as_ref().map(|(sep, m)| format!("{}{}", sep, m));

        node + &next.unwrap_or_else(|| "".to_string())
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

impl fmt::Display for Mess {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.pretty())
    }
}

/// Possible values of a section of a [`Mess`](struct.Mess.html).
///
/// A numeric value is extracted if it could be, alongside the original text it
/// came from. This preserves both `Ord` and `Display` behaviour for versions
/// like `1.003.0`.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum MChunk {
    /// A nice numeric value.
    Digit(u32, String),
    /// A numeric value preceeded by an `r`, indicating a revision.
    Rev(u32, String),
    /// Anything else.
    Plain(String),
}

impl MChunk {
    /// Extract the original `String`, no matter which variant it parsed into.
    pub fn text(&self) -> &str {
        match self {
            MChunk::Digit(_, s) => s,
            MChunk::Rev(_, s) => s,
            MChunk::Plain(s) => s,
        }
    }

    fn parse(i: &str) -> IResult<&str, MChunk> {
        alt((MChunk::digits, MChunk::rev, MChunk::plain))(i)
    }

    fn digits(i: &str) -> IResult<&str, MChunk> {
        todo!()
    }

    fn rev(i: &str) -> IResult<&str, MChunk> {
        todo!()
    }

    fn plain(i: &str) -> IResult<&str, MChunk> {
        todo!()
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
            (MChunk::Digit(a, _), MChunk::Digit(b, _)) => a.cmp(b),
            (MChunk::Rev(a, _), MChunk::Rev(b, _)) => a.cmp(b),
            // If I'm a concrete number and you're just a revision, then I'm greater no matter what.
            (MChunk::Digit(_, _), MChunk::Rev(_, _)) => Greater,
            (MChunk::Rev(_, _), MChunk::Digit(_, _)) => Less,
            // There's no sensible pairing, so we fall back to String-based comparison.
            (a, b) => a.text().cmp(b.text()),
        }
    }
}

impl fmt::Display for MChunk {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            MChunk::Digit(_, s) => write!(f, "{}", s),
            MChunk::Rev(_, s) => write!(f, "{}", s),
            MChunk::Plain(s) => write!(f, "{}", s),
        }
    }
}

/// Symbols that separate groups of digits/letters in a version number. Used in
/// the [`Mess`](struct.Mess.html) type.
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
        if s.chars().all(|c| c.is_ascii_alphabetic()) {
            Some(Unit::Letters(s))
        } else {
            None
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

    fn single_zero(i: &str) -> IResult<&str, Unit> {
        map_res(tag("0"), |s: &str| s.parse::<u32>().map(Unit::Digits))(i)
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

/// A logical unit of a version number.
///
/// Can consist of multiple letters and numbers. Groups of these (i.e.
/// [`Chunks`](type.Chunks.html)) are separated by periods to form a full
/// version number.
///
/// Defined as a newtype wrapper so that we can define custom parser and trait
/// methods.
///
/// # Examples
///
/// - `r3`
/// - `0rc1`
/// - `20150826`
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Chunk(pub Vec<Unit>);

impl Chunk {
    /// If this `Chunk` is made up of a single [`Unit::Digits`](enum.Unit.html),
    /// then pull out the inner value.
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
        match self.0.first() {
            Some(Unit::Digits(n)) if self.0.len() == 1 => Some(*n),
            _ => None,
        }
    }

    /// Like [`single_digit`](#method.single_digit), but will grab the `u32`
    /// even if there were more values in the `Chunk`.
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
        match self.0.first() {
            Some(Unit::Digits(n)) => Some(*n),
            _ => None,
        }
    }

    fn mchunk(&self) -> MChunk {
        todo!()
    }

    fn parse(i: &str) -> IResult<&str, Chunk> {
        map(Chunk::units, Chunk)(i)
    }

    /// Handling `0` is a bit tricky. We can't allow runs of zeros in a chunk,
    /// since a version like `1.000.1` would parse as `1.0.1`.
    fn units(i: &str) -> IResult<&str, Vec<Unit>> {
        alt((
            Chunk::zero_with_letters,
            map(Unit::single_zero, |u| vec![u]),
            many1(Unit::parse),
        ))(i)
    }

    fn zero_with_letters(i: &str) -> IResult<&str, Vec<Unit>> {
        let (i, z) = Unit::single_zero(i)?;
        let (i, s) = Unit::string(i)?;
        let (i, c) = opt(Chunk::units)(i)?;

        let mut us = vec![z, s];
        if let Some(x) = c {
            us.extend(x);
        }

        Ok((i, us))
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
                Left(_) => Some(Less),
                Right(_) => Some(Greater),
                // The usual case where the `Unit` types match, as in `1.2.3.4`
                // vs `1.2.4.0`.
                Both(Unit::Digits(a), Unit::Digits(b)) => match a.cmp(b) {
                    Equal => None,
                    ord => Some(ord),
                },
                Both(Unit::Letters(a), Unit::Letters(b)) => match a.cmp(b) {
                    Equal => None,
                    ord => Some(ord),
                },
                // The arbitrary decision to prioritize Letters over Digits has
                // the effect of allowing this instance to work for `SemVer` as
                // well as `Version`.
                Both(Unit::Digits(_), Unit::Letters(_)) => Some(Less),
                Both(Unit::Letters(_), Unit::Digits(_)) => Some(Greater),
            })
            .next()
            .unwrap_or(Equal)
    }
}

impl fmt::Display for Chunk {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s: String = self.0.iter().map(|u| format!("{}", u)).collect();
        write!(f, "{}", s)
    }
}

/// Multiple [`Chunk`](struct.Chunk.html) values.
///
/// Defined as a newtype wrapper so that we can define custom parser and trait
/// methods.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Chunks(pub Vec<Chunk>);

impl Chunks {
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
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Versioning {
    Ideal(SemVer),
    General(Version),
    Complex(Mess),
}

impl Versioning {
    /// Create a `Versioning` by attempting to parse the input first as
    /// [`SemVer`](struct.SemVer.html), then as a
    /// [`Version`](struct.Version.html), and finally as a
    /// [`Mess`](struct.Mess.html).
    pub fn new(s: &str) -> Option<Versioning> {
        SemVer::new(s)
            .map(Versioning::Ideal)
            .or_else(|| Version::new(s).map(Versioning::General))
            .or_else(|| Mess::new(s).map(Versioning::Complex))
    }

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

impl fmt::Display for Versioning {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Versioning::Ideal(s) => write!(f, "{}", s),
            Versioning::General(v) => write!(f, "{}", v),
            Versioning::Complex(m) => write!(f, "{}", m),
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
        let messes = vec!["10.2+0.93+1-1", "003.03-3", "002.000-7", "20.26.1_0-2"];

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
    fn mixed_comparisons() {
        cmp_versioning("1.2.2r1-1", "1.2.3-1");
        cmp_versioning("1.2.3-1", "1.2.4r1-1");
        cmp_versioning("1.2.3-1", "2+0007-1");
        cmp_versioning("1.2.3r1-1", "2+0007-1");
        cmp_versioning("1.2-5", "1.2.3-1");
        cmp_versioning("1.6.0a+2014+m872b87e73dfb-1", "1.6.0-1");
        // cmp_versioning("1.11.0.git.20200404-1", "1.11.0+20200830-1");
        cmp_versioning("0.17.0+r8+gc41db5f1-1", "0.17.0+r157+g584760cf-1");
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
}
