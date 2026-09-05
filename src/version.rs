//! Types and logic for handling general [`Version`]s.

use crate::parsers::unsigned;
use crate::{Chunk, Chunks, Error, MChunk, Mess, Release, Sep};
use nom::branch::alt;
use nom::bytes::complete::take_while1;
use nom::character::complete::char;
use nom::combinator::{eof, fail, opt};
use nom::{IResult, Parser};
use std::cmp::Ordering;
use std::cmp::Ordering::{Equal, Greater, Less};
use std::hash::Hash;
use std::str::FromStr;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// A version number with decent structure and comparison logic.
///
/// This is a *descriptive* scheme, meaning that it encapsulates the most
/// common, unconscious patterns that developers use when assigning version
/// numbers to their software. If not [`crate::SemVer`], most version numbers
/// found in the wild will parse as a `Version`. These generally conform to the
/// `x.x.x-x` pattern, and may optionally have an *epoch*.
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
    /// The main sections of the `Version`. Unlike [`crate::SemVer`], these
    /// sections are allowed to contain letters.
    pub chunks: Chunks,
    /// The last [`Chunk`], but parsed with extra rules to account for patterns
    /// like `3.7b` and `1.2.3rc2` for more accurate comparison.
    pub last: Last,
    /// This either indicates a prerelease like [`crate::SemVer`], or a
    /// "release" revision for software packages. In the latter case, a version
    /// like `1.2.3-2` implies that the software itself hasn't changed, but that
    /// this is the second bundling/release (etc.) of that particular package.
    pub release: Option<Release>,
    /// Some extra metadata that doesn't factor into comparison.
    pub meta: Option<String>,
}

impl Version {
    /// Parse a `Version` from some input.
    pub fn new<S>(s: S) -> Option<Version>
    where
        S: AsRef<str>,
    {
        match Version::parse(s.as_ref()) {
            Ok(("", v)) => Some(v),
            _ => None,
        }
    }

    /// Try to extract a position from the `Version` as a nice integer, as if it
    /// were a [`crate::SemVer`].
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
        if n == self.chunks.0.len() {
            match self.last {
                Last::Numeric(n) => Some(n),
                Last::Rc(n, _, _) => Some(n),
                Last::Post(n, _) => Some(n),
                Last::Alphanum(_) => None,
            }
        } else {
            self.chunks.0.get(n).and_then(Chunk::single_digit)
        }
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
        let mut chunks: Vec<_> = self.chunks.0.iter().map(|c| c.mchunk()).collect();
        chunks.push(self.last.mchunk());
        let next = self.release.as_ref().map(|cs| {
            let chunks = cs.0.iter().map(|c| c.mchunk()).collect();
            (Sep::Hyphen, Box::new(Mess { chunks, next: None }))
        });

        Mess { chunks, next }
    }

    /// Just compares the main `Chunks` and `Last` portions. Epoch and Release
    /// comparison is assumed to occur in the caller. See `Version::cmp`.
    fn cmp_with_last(longer: &Version, shorter: &Version) -> Ordering {
        let len_shorter = shorter.chunks.0.len();
        let (main, rest) = longer.chunks.0.split_at(len_shorter);

        // FIXME: 2026-09-05 Lazy cloning here.
        match Chunks(main.to_vec()).cmp(&shorter.chunks) {
            // FIXME: 2026-09-05 This indexing will panic if the `longer` isn't
            // actually longer.
            Equal => match Last::from(rest[0].clone()).cmp(&shorter.last) {
                Equal => Greater,
                ord => ord,
            },
            ord => ord,
        }
    }

    /// If we're lucky, we can pull specific numbers out of both inputs and
    /// accomplish the comparison without extra allocations.
    pub(crate) fn cmp_mess(&self, other: &Mess) -> Ordering {
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
                        Equal => Version::cmp_mess_continued(self, m),
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
            _ => Version::cmp_mess_continued(self, other),
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
        let (i, epoch) = opt(Version::epoch).parse(i)?;
        let (i, mut chunks) = Chunks::parse(i)?;
        let (i, release) = opt(Release::parse).parse(i)?;
        let (i, meta) = opt(crate::parsers::meta).parse(i)?;

        match chunks.0.pop() {
            // NOTE: 2026-09-01 This `None` branch should never trigger since
            // the parsers above would have succeeded by this point and so
            // `chunks` should always contain something. Even so, I'm not
            // willing to call `unwrap` ;)
            None => fail().parse(i),
            Some(last) => {
                let v = Version {
                    epoch,
                    chunks,
                    last: Last::from(last),
                    meta,
                    release,
                };

                Ok((i, v))
            }
        }
    }

    fn epoch(i: &str) -> IResult<&str, u32> {
        let (i, epoch) = crate::parsers::unsigned(i)?;
        let (i, _) = char(':')(i)?;

        Ok((i, epoch))
    }

    pub(crate) fn matches_tilde(&self, other: &Version) -> bool {
        if self.chunks.0.len() != other.chunks.0.len() {
            false
        } else {
            // Compare all but the final chunk.
            let inits_equal = self
                .chunks
                .0
                .iter()
                .rev()
                .skip(1)
                .rev()
                .zip(other.chunks.0.iter().rev().skip(1).rev())
                .all(|(a, b)| a == b);

            let last_good = match (self.chunks.0.last(), other.chunks.0.last()) {
                // TODO: Do our best with strings. Right now, the alpha patch version can be "less" than the
                // first one and this will still be true
                (Some(Chunk::Alphanum(_)), Some(Chunk::Alphanum(_))) => true,
                (Some(Chunk::Numeric(n1)), Some(Chunk::Numeric(n2))) => n2 >= n1,
                _ => false,
            };

            inits_equal && last_good
        }
    }

    // TODO 2024-01-11 Refactor this to be more functional-style.
    pub(crate) fn matches_caret(&self, other: &Version) -> bool {
        let mut got_first_nonzero = false;

        for (v1_chunk, v2_chunk) in self.chunks.0.iter().zip(other.chunks.0.iter()) {
            if !got_first_nonzero {
                if !v1_chunk.single_digit().is_some_and(|n| n == 0) {
                    got_first_nonzero = true;

                    if v1_chunk != v2_chunk {
                        return false;
                    }
                }
            } else if v2_chunk.cmp_lenient(v1_chunk).is_lt() {
                return false;
            }
        }

        true
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
            Equal => {
                let len_self = self.chunks.0.len();
                let len_othr = other.chunks.0.len();

                let body_ord = if len_self == len_othr {
                    match self.chunks.cmp(&other.chunks) {
                        Equal => self.last.cmp(&other.last),
                        ord => ord,
                    }
                } else if len_self > len_othr {
                    Version::cmp_with_last(self, other)
                } else {
                    Version::cmp_with_last(other, self).reverse()
                };

                match body_ord {
                    Equal => self.release.cmp(&other.release),
                    ord => ord,
                }
            }
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

        match self.chunks.0.as_slice() {
            [] => write!(f, "{}", self.last)?,
            _ => write!(f, ".{}", self.last)?,
        }

        if let Some(r) = &self.release {
            write!(f, "-{}", r)?;
        }

        if let Some(m) = &self.meta {
            write!(f, "+{}", m)?;
        }

        Ok(())
    }
}

impl FromStr for Version {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Version::new(s).ok_or_else(|| Error::IllegalVersion(s.to_string()))
    }
}

impl TryFrom<&str> for Version {
    type Error = Error;

    /// ```
    /// use versions::Version;
    ///
    /// let orig = "1.2.3.4";
    /// let prsd: Version = orig.try_into().unwrap();
    /// assert_eq!(orig, prsd.to_string());
    /// ```
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        Version::from_str(value)
    }
}

/// The final component of the main pieces of a [`Version`]. Often has
/// additional tag-like metadata appended to a number to indicate release
/// information, like `1.2.3rc1`.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Last {
    /// A nice, pure number.
    Numeric(u32),
    /// A special case of `Alphanum` which structurally represents the "RC
    /// pattern", or chunks like the last member of `1.2.3rc2`.
    Rc(u32, String, u32),
    /// Similar to `Rc`, but for numbers appended with a letter.
    ///
    /// - Tmux: `3.7b`
    Post(u32, String),
    /// Any other free mixture of letters and numbers.
    Alphanum(String),
}

impl Last {
    fn mchunk(&self) -> MChunk {
        // NOTE 2026-09-05 Unfortunate allocations here.
        match self {
            Last::Numeric(n) => MChunk::Digits(*n, n.to_string()),
            l @ Last::Rc(_, _, _) => MChunk::Plain(l.to_string()),
            l @ Last::Post(_, _) => MChunk::Plain(l.to_string()),
            Last::Alphanum(s) => MChunk::Plain(s.clone()),
        }
    }
}

impl PartialOrd for Last {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Last {
    /// ```
    /// use versions::Last;
    ///
    /// let a = Last::Rc(0, "rc".to_string(), 1);
    /// let b = Last::Numeric(0);
    /// assert!(a < b);
    ///
    /// let a = Last::Post(7, "alpha".to_string());
    /// let b = Last::Numeric(7);
    /// assert!(a < b);
    /// ```
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Last::Numeric(a), Last::Numeric(b)) => a.cmp(b),
            (Last::Numeric(a), Last::Rc(b, _, _)) => match a.cmp(b) {
                // RCs are always less than the true release.
                Equal => Greater,
                ord => ord,
            },
            (Last::Numeric(a), Last::Post(b, _)) => match a.cmp(b) {
                Equal => Greater,
                ord => ord,
            },
            // ARBITRARY: If the right side is garbage, the nice number is
            // always considered greater.
            (Last::Numeric(_), Last::Alphanum(_)) => Greater,
            (Last::Rc(a, s, b), Last::Rc(x, t, y)) => match a.cmp(x) {
                Equal => match s.cmp(t) {
                    Equal => b.cmp(y),
                    ord => ord,
                },
                ord => ord,
            },
            (Last::Rc(a, _, _), Last::Numeric(b)) => match a.cmp(b) {
                Equal => Less,
                ord => ord,
            },
            (Last::Rc(a, s, _), Last::Post(b, t)) => match a.cmp(b) {
                // NOTE: 2026-09-05 Perhaps weak.
                Equal => s.cmp(t),
                ord => ord,
            },
            // ARBITRARY
            (Last::Rc(_, _, _), Last::Alphanum(_)) => Greater,
            (Last::Post(a, _), Last::Numeric(b)) => match a.cmp(b) {
                Equal => Less,
                ord => ord,
            },
            (Last::Post(a, s), Last::Rc(b, t, _)) => match a.cmp(b) {
                Equal => s.cmp(t),
                ord => ord,
            },
            (Last::Post(a, s), Last::Post(b, t)) => match a.cmp(b) {
                Equal => s.cmp(t),
                ord => ord,
            },
            // ARBITRARY
            (Last::Post(_, _), Last::Alphanum(_)) => Greater,
            // ARBITRARY
            (Last::Alphanum(_), Last::Numeric(_)) => Less,
            // ARBITRARY
            (Last::Alphanum(_), Last::Rc(_, _, _)) => Less,
            // ARBITRARY
            (Last::Alphanum(_), Last::Post(_, _)) => Less,
            (Last::Alphanum(a), Last::Alphanum(b)) => a.cmp(b),
        }
    }
}

impl Default for Last {
    fn default() -> Self {
        Last::Numeric(0)
    }
}

impl std::fmt::Display for Last {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Last::Numeric(n) => write!(f, "{n}"),
            Last::Rc(a, s, b) => write!(f, "{a}{s}{b}"),
            Last::Post(n, s) => write!(f, "{n}{s}"),
            Last::Alphanum(s) => write!(f, "{s}"),
        }
    }
}

impl From<Chunk> for Last {
    /// ```
    /// use versions::Chunk;
    /// use versions::Last;
    ///
    /// let c = Chunk::Alphanum("1rc2".to_string());
    /// let l = Last::from(c);
    /// assert_eq!(l, Last::Rc(1, "rc".to_string(), 2));
    ///
    /// let c = Chunk::Alphanum("7b".to_string());
    /// let l = Last::from(c);
    /// assert_eq!(l, Last::Post(7, "b".to_string()));
    /// ```
    fn from(chunk: Chunk) -> Self {
        match chunk {
            Chunk::Numeric(n) => Last::Numeric(n),
            Chunk::Alphanum(s) => match last(&s) {
                Ok((_, l)) => l,
                Err(_) => Last::Alphanum(s),
            },
        }
    }
}

fn last(i: &str) -> IResult<&str, Last> {
    alt((rc, post)).parse(i)
}

fn rc(i: &str) -> IResult<&str, Last> {
    let (i, a) = unsigned(i)?;
    let (i, s) = take_while1(|c: char| c.is_ascii_alphabetic()).parse(i)?;
    let (i, b) = unsigned(i)?;
    let (_, _) = eof(i)?;

    Ok(("", Last::Rc(a, s.to_string(), b)))
}

fn post(i: &str) -> IResult<&str, Last> {
    let (i, u) = unsigned(i)?;
    let (i, s) = take_while1(|c: char| c.is_ascii_alphabetic()).parse(i)?;
    let (_, _) = eof(i)?;

    Ok(("", Last::Post(u, s.to_string())))
}
