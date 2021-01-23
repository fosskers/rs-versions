# `versions` Changelog

## 2.0.2 (2021-01-23)

#### Changed

- Updated to `itertools-0.10`.

## 2.0.1 (2020-11-19)

#### Changed

- Updated to `nom-6.0`.
- Utilize new type linking in docstrings, thanks to the latest stable Rust.

## 2.0.0 (2020-10-21)

#### Changed

- **Breaking:** `Mess::chunk` renamed to `Mess::chunks` to match `Version`.
- **Breaking:** `Mess` now stores smarter `Vec<MChunk>` instead of `String`s.
- `SemVer::to_version` is no longer a lossy conversion, due to the new field in `Version` (see below).
- Most `Display` instances are more efficient.

#### Added

- **Breaking:** The `meta: Option<Chunks>` field for `Version`.
- The `MChunk` type which allows `Mess` to do smarter comparisons.

#### Fixed

- A number of comparison edge cases.

## 1.0.1 (2020-06-15)

#### Changed

- Performance and readability improvements.

## 1.0.0 (2020-06-03)

This is the initial release of the library.

#### Added

- All types, parsers, and tests.
