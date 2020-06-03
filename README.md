# Versions

[![Tests](https://github.com/fosskers/rs-versions/workflows/Tests/badge.svg)](https://github.com/fosskers/rs-versions/actions)
[![](https://img.shields.io/crates/v/versions.svg)](https://crates.io/crates/versions)

A library for parsing and comparing software version numbers.

We like to give version numbers to our software in a myriad of different ways.
Some ways follow strict guidelines for incrementing and comparison. Some follow
conventional wisdom and are generally self-consistent. Some are just plain
asinine. This library provides a means of parsing and comparing *any* style of
versioning, be it a nice Semantic Version like this:

> 1.2.3-r1

...or a monstrosity like this:

> 2:10.2+0.0093r3+1-1

For the Haskell version of this library, [see
here](http://hackage.haskell.org/package/versions).

### Examples

```rust
use versions::Versioning;

let good = Versioning::new("1.6.0").unwrap();
let evil = Versioning::new("1.6.0a+2014+m872b87e73dfb-1").unwrap();

assert!(good.is_ideal());   // It parsed as a `SemVer`.
assert!(evil.is_complex()); // It parsed as a `Mess`.
assert!(good > evil);       // We can compare them anyway!
```
