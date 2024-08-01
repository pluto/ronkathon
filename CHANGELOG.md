# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.1.0](https://github.com/pluto/ronkathon/releases/tag/v0.1.0) - 2024-07-31

### Added
- algebra ([#135](https://github.com/pluto/ronkathon/pull/135))
- cipher modes of operation ([#127](https://github.com/pluto/ronkathon/pull/127))
- AES decryption ([#124](https://github.com/pluto/ronkathon/pull/124))
- *(ciphers)* AES encryption ([#102](https://github.com/pluto/ronkathon/pull/102))
- stream cipher trait and chacha encryption ([#103](https://github.com/pluto/ronkathon/pull/103))
- DES encryption ([#101](https://github.com/pluto/ronkathon/pull/101))
- binary field ([#90](https://github.com/pluto/ronkathon/pull/90))
- poseidon hash ([#83](https://github.com/pluto/ronkathon/pull/83))
- merkle tree and merkle proof ([#88](https://github.com/pluto/ronkathon/pull/88))
- sha256 ([#86](https://github.com/pluto/ronkathon/pull/86))
- feat/reed-solomon code ([#79](https://github.com/pluto/ronkathon/pull/79))
- weil pairing ([#80](https://github.com/pluto/ronkathon/pull/80))
- ecdsa ([#77](https://github.com/pluto/ronkathon/pull/77))
- KZG commitment ([#69](https://github.com/pluto/ronkathon/pull/69))
- Tate pairing ([#67](https://github.com/pluto/ronkathon/pull/67))
- (mostly) generic fields ([#63](https://github.com/pluto/ronkathon/pull/63))
- Commit ([#61](https://github.com/pluto/ronkathon/pull/61))
- general extensions and documentation ([#58](https://github.com/pluto/ronkathon/pull/58))
- g2 curve interface ([#54](https://github.com/pluto/ronkathon/pull/54))
- discrete fourier transform + monomial mul ([#50](https://github.com/pluto/ronkathon/pull/50))
- basic polynomial arithmetic ([#48](https://github.com/pluto/ronkathon/pull/48))
- home-baked `FiniteField` trait ([#38](https://github.com/pluto/ronkathon/pull/38))
- add SageMath ([#24](https://github.com/pluto/ronkathon/pull/24))
- `PlutoField::primitive_root_of_unity()`

### Fixed
- fix lint.yaml ([#134](https://github.com/pluto/ronkathon/pull/134))
- lock
- dead code and added comments
- fix readme

### Other
- replace actions-rs with dtolnay/rust-toolchain ([#130](https://github.com/pluto/ronkathon/pull/130))
- usize -> enum ([#126](https://github.com/pluto/ronkathon/pull/126))
- release ([#112](https://github.com/pluto/ronkathon/pull/112))
- *(deps)* bump actions/checkout from 2 to 4 ([#118](https://github.com/pluto/ronkathon/pull/118))
- quadratic residue algo ([#114](https://github.com/pluto/ronkathon/pull/114))
- reuse .pow() code ([#113](https://github.com/pluto/ronkathon/pull/113))
- release ([#111](https://github.com/pluto/ronkathon/pull/111))
- cargo lock
- upgrade generic polynomials ([#110](https://github.com/pluto/ronkathon/pull/110))
- release-plz workflow ([#107](https://github.com/pluto/ronkathon/pull/107))
- Feat/dsl ([#60](https://github.com/pluto/ronkathon/pull/60))
- Update README.md
- run tests in CI ([#105](https://github.com/pluto/ronkathon/pull/105))
- fix doc attribute scope ([#104](https://github.com/pluto/ronkathon/pull/104))
- constant polynomial arithmetic ([#89](https://github.com/pluto/ronkathon/pull/89))
- Update README.md
- Update README.md
- Update README.md
- Update README.md
- Update README.md
- docs ([#84](https://github.com/pluto/ronkathon/pull/84))
- *(deps)* bump rstest from 0.19.0 to 0.21.0 ([#85](https://github.com/pluto/ronkathon/pull/85))
- Tiny rsa ([#68](https://github.com/pluto/ronkathon/pull/68))
- ---
- *(deps)* bump num-bigint from 0.4.4 to 0.4.5 ([#65](https://github.com/pluto/ronkathon/pull/65))
- *(deps)* bump serde from 1.0.200 to 1.0.201
- cleanup `curve` module ([#59](https://github.com/pluto/ronkathon/pull/59))
- refactor + cleanup ([#52](https://github.com/pluto/ronkathon/pull/52))
- Second curve group and some test ([#49](https://github.com/pluto/ronkathon/pull/49))
- readme ([#46](https://github.com/pluto/ronkathon/pull/46))
- Extension field ([#44](https://github.com/pluto/ronkathon/pull/44))
- curves in sage ([#39](https://github.com/pluto/ronkathon/pull/39))
- Bump anyhow from 1.0.82 to 1.0.83
- [wip] Add basic trusted setup and kzg ([#22](https://github.com/pluto/ronkathon/pull/22))
- montgomery arithmetic ([#23](https://github.com/pluto/ronkathon/pull/23))
- Colin/polynomials ([#19](https://github.com/pluto/ronkathon/pull/19))
- curve implementation updated ([#21](https://github.com/pluto/ronkathon/pull/21))
- Merge pull request [#14](https://github.com/pluto/ronkathon/pull/14) from pluto/colin/curves
- lint
- Merge branch 'main' into colin/curves
- Squashed commit of the following:
- Update curve.rs
- Squashed commit of the following:
- curve + point structs
- licensing and authorship
- rmv unnec
- init
- Initial commit

## [0.1.0](https://github.com/pluto/ronkathon/releases/tag/v0.1.0) - 2024-07-02

### Added
- *(ciphers)* AES encryption ([#102](https://github.com/pluto/ronkathon/pull/102))
- stream cipher trait and chacha encryption ([#103](https://github.com/pluto/ronkathon/pull/103))
- DES encryption ([#101](https://github.com/pluto/ronkathon/pull/101))
- binary field ([#90](https://github.com/pluto/ronkathon/pull/90))
- poseidon hash ([#83](https://github.com/pluto/ronkathon/pull/83))
- merkle tree and merkle proof ([#88](https://github.com/pluto/ronkathon/pull/88))
- sha256 ([#86](https://github.com/pluto/ronkathon/pull/86))
- feat/reed-solomon code ([#79](https://github.com/pluto/ronkathon/pull/79))
- weil pairing ([#80](https://github.com/pluto/ronkathon/pull/80))
- ecdsa ([#77](https://github.com/pluto/ronkathon/pull/77))
- KZG commitment ([#69](https://github.com/pluto/ronkathon/pull/69))
- Tate pairing ([#67](https://github.com/pluto/ronkathon/pull/67))
- (mostly) generic fields ([#63](https://github.com/pluto/ronkathon/pull/63))
- Commit ([#61](https://github.com/pluto/ronkathon/pull/61))
- general extensions and documentation ([#58](https://github.com/pluto/ronkathon/pull/58))
- g2 curve interface ([#54](https://github.com/pluto/ronkathon/pull/54))
- discrete fourier transform + monomial mul ([#50](https://github.com/pluto/ronkathon/pull/50))
- basic polynomial arithmetic ([#48](https://github.com/pluto/ronkathon/pull/48))
- home-baked `FiniteField` trait ([#38](https://github.com/pluto/ronkathon/pull/38))
- add SageMath ([#24](https://github.com/pluto/ronkathon/pull/24))
- `PlutoField::primitive_root_of_unity()`

### Fixed
- lock
- dead code and added comments
- fix readme

### Other
- *(deps)* bump actions/checkout from 2 to 4 ([#118](https://github.com/pluto/ronkathon/pull/118))
- quadratic residue algo ([#114](https://github.com/pluto/ronkathon/pull/114))
- reuse .pow() code ([#113](https://github.com/pluto/ronkathon/pull/113))
- release ([#111](https://github.com/pluto/ronkathon/pull/111))
- cargo lock
- upgrade generic polynomials ([#110](https://github.com/pluto/ronkathon/pull/110))
- release-plz workflow ([#107](https://github.com/pluto/ronkathon/pull/107))
- Feat/dsl ([#60](https://github.com/pluto/ronkathon/pull/60))
- Update README.md
- run tests in CI ([#105](https://github.com/pluto/ronkathon/pull/105))
- fix doc attribute scope ([#104](https://github.com/pluto/ronkathon/pull/104))
- constant polynomial arithmetic ([#89](https://github.com/pluto/ronkathon/pull/89))
- Update README.md
- Update README.md
- Update README.md
- Update README.md
- Update README.md
- docs ([#84](https://github.com/pluto/ronkathon/pull/84))
- *(deps)* bump rstest from 0.19.0 to 0.21.0 ([#85](https://github.com/pluto/ronkathon/pull/85))
- Tiny rsa ([#68](https://github.com/pluto/ronkathon/pull/68))
- ---
- *(deps)* bump num-bigint from 0.4.4 to 0.4.5 ([#65](https://github.com/pluto/ronkathon/pull/65))
- *(deps)* bump serde from 1.0.200 to 1.0.201
- cleanup `curve` module ([#59](https://github.com/pluto/ronkathon/pull/59))
- refactor + cleanup ([#52](https://github.com/pluto/ronkathon/pull/52))
- Second curve group and some test ([#49](https://github.com/pluto/ronkathon/pull/49))
- readme ([#46](https://github.com/pluto/ronkathon/pull/46))
- Extension field ([#44](https://github.com/pluto/ronkathon/pull/44))
- curves in sage ([#39](https://github.com/pluto/ronkathon/pull/39))
- Bump anyhow from 1.0.82 to 1.0.83
- [wip] Add basic trusted setup and kzg ([#22](https://github.com/pluto/ronkathon/pull/22))
- montgomery arithmetic ([#23](https://github.com/pluto/ronkathon/pull/23))
- Colin/polynomials ([#19](https://github.com/pluto/ronkathon/pull/19))
- curve implementation updated ([#21](https://github.com/pluto/ronkathon/pull/21))
- Merge pull request [#14](https://github.com/pluto/ronkathon/pull/14) from pluto/colin/curves
- lint
- Merge branch 'main' into colin/curves
- Squashed commit of the following:
- Update curve.rs
- Squashed commit of the following:
- curve + point structs
- licensing and authorship
- rmv unnec
- init
- Initial commit

## [0.1.0](https://github.com/pluto/ronkathon/releases/tag/v0.1.0) - 2024-07-01

### Added
- DES encryption ([#101](https://github.com/pluto/ronkathon/pull/101))
- binary field ([#90](https://github.com/pluto/ronkathon/pull/90))
- poseidon hash ([#83](https://github.com/pluto/ronkathon/pull/83))
- merkle tree and merkle proof ([#88](https://github.com/pluto/ronkathon/pull/88))
- sha256 ([#86](https://github.com/pluto/ronkathon/pull/86))
- feat/reed-solomon code ([#79](https://github.com/pluto/ronkathon/pull/79))
- weil pairing ([#80](https://github.com/pluto/ronkathon/pull/80))
- ecdsa ([#77](https://github.com/pluto/ronkathon/pull/77))
- KZG commitment ([#69](https://github.com/pluto/ronkathon/pull/69))
- Tate pairing ([#67](https://github.com/pluto/ronkathon/pull/67))
- (mostly) generic fields ([#63](https://github.com/pluto/ronkathon/pull/63))
- Commit ([#61](https://github.com/pluto/ronkathon/pull/61))
- general extensions and documentation ([#58](https://github.com/pluto/ronkathon/pull/58))
- g2 curve interface ([#54](https://github.com/pluto/ronkathon/pull/54))
- discrete fourier transform + monomial mul ([#50](https://github.com/pluto/ronkathon/pull/50))
- basic polynomial arithmetic ([#48](https://github.com/pluto/ronkathon/pull/48))
- home-baked `FiniteField` trait ([#38](https://github.com/pluto/ronkathon/pull/38))
- add SageMath ([#24](https://github.com/pluto/ronkathon/pull/24))
- `PlutoField::primitive_root_of_unity()`

### Fixed
- lock
- dead code and added comments
- fix readme

### Other
- cargo lock
- upgrade generic polynomials ([#110](https://github.com/pluto/ronkathon/pull/110))
- release-plz workflow ([#107](https://github.com/pluto/ronkathon/pull/107))
- Feat/dsl ([#60](https://github.com/pluto/ronkathon/pull/60))
- Update README.md
- run tests in CI ([#105](https://github.com/pluto/ronkathon/pull/105))
- fix doc attribute scope ([#104](https://github.com/pluto/ronkathon/pull/104))
- constant polynomial arithmetic ([#89](https://github.com/pluto/ronkathon/pull/89))
- Update README.md
- Update README.md
- Update README.md
- Update README.md
- Update README.md
- docs ([#84](https://github.com/pluto/ronkathon/pull/84))
- *(deps)* bump rstest from 0.19.0 to 0.21.0 ([#85](https://github.com/pluto/ronkathon/pull/85))
- Tiny rsa ([#68](https://github.com/pluto/ronkathon/pull/68))
- ---
- *(deps)* bump num-bigint from 0.4.4 to 0.4.5 ([#65](https://github.com/pluto/ronkathon/pull/65))
- *(deps)* bump serde from 1.0.200 to 1.0.201
- cleanup `curve` module ([#59](https://github.com/pluto/ronkathon/pull/59))
- refactor + cleanup ([#52](https://github.com/pluto/ronkathon/pull/52))
- Second curve group and some test ([#49](https://github.com/pluto/ronkathon/pull/49))
- readme ([#46](https://github.com/pluto/ronkathon/pull/46))
- Extension field ([#44](https://github.com/pluto/ronkathon/pull/44))
- curves in sage ([#39](https://github.com/pluto/ronkathon/pull/39))
- Bump anyhow from 1.0.82 to 1.0.83
- [wip] Add basic trusted setup and kzg ([#22](https://github.com/pluto/ronkathon/pull/22))
- montgomery arithmetic ([#23](https://github.com/pluto/ronkathon/pull/23))
- Colin/polynomials ([#19](https://github.com/pluto/ronkathon/pull/19))
- curve implementation updated ([#21](https://github.com/pluto/ronkathon/pull/21))
- Merge pull request [#14](https://github.com/pluto/ronkathon/pull/14) from pluto/colin/curves
- lint
- Merge branch 'main' into colin/curves
- Squashed commit of the following:
- Update curve.rs
- Squashed commit of the following:
- curve + point structs
- licensing and authorship
- rmv unnec
- init
- Initial commit
