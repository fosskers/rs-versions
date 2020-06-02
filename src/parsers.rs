//! Reusable parsers for the `versions` library.

use nom::branch::alt;
use nom::bytes::complete::tag;
use nom::character::complete::digit1;
use nom::combinator::map_res;
use nom::IResult;

/// Parse an unsigned integer.
pub fn unsigned(i: &str) -> IResult<&str, u32> {
    map_res(alt((tag("0"), digit1)), |s: &str| s.parse::<u32>())(i)
}
