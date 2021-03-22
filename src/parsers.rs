//! Reusable parsers for the `versions` library.

use nom::branch::alt;
use nom::bytes::complete::tag;
use nom::character::complete::digit1;
use nom::combinator::map_res;
use nom::IResult;

/// Parse an unsigned integer.
///
/// Should yield either be a zero on its own, or some other multi-digit number.
pub fn unsigned(i: &str) -> IResult<&str, u32> {
    map_res(alt((tag("0"), digit1)), |s: &str| s.parse::<u32>())(i)
}

#[test]
fn unsigned_test() {
    assert!(unsigned("0").is_ok());
    assert!(unsigned("123").is_ok());

    match unsigned("06") {
        Ok(("6", 0)) => {}
        Ok(_) => panic!("Parsed 06, but gave wrong output"),
        Err(_) => panic!("Couldn't parse 06"),
    }
}
