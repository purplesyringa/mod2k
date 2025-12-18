# `mod2k`

![License](https://img.shields.io/crates/l/mod2k) [![Version](https://img.shields.io/crates/v/mod2k)](https://crates.io/crates/mod2k) [![docs.rs](https://img.shields.io/docsrs/mod2k)](https://docs.rs/mod2k) ![Tests](https://github.com/purplesyringa/mod2k/actions/workflows/ci.yml/badge.svg)

A `#![no_std]` Rust crate for fast arithmetic modulo `2^k`, `2^k - 1`, and `2^k - d`.

Modular arithmetic is useful for fast hashing, verification of polynomial operations, and as a ring balancing the cost of division with the cost of other operations.
Different moduli make different quality vs performance tradeoffs.
This crate provides a uniform interface for fast implementations of multiple moduli, allowing you to tune the balance without rewriting your code to adopt faster algorithms:

- "Big" primes: `2^8 - 5`, `2^16 - 15`, `2^32 - 5`, `2^64 - 59`. Slowest (~12 insn per multiplication, ~7 insn per addition, slow shifts and inversions), excellent quality.
- Primes: `2^7 - 1`, `2^13 - 1`, `2^31 - 1`, `2^61 - 1`. Medium performance (~10 insn per multiplication, ~5 insn per addition), excellent quality (but slightly fewer bits of precision compared to "big" primes).
- "Fast": `2^8 - 1`, `2^16 - 1`, `2^32 - 1`, `2^64 - 1`. Great performance (~4 insn per multiplication, ~2 insn per addition), medium quality (the moduli have relatively big prime factors).
- Powers of two: `2^8`, `2^16`, `2^32`, `2^64`. Fastest (1 insn per multiplication and addition), but [have seed-independent collisions](https://en.wikipedia.org/wiki/Thue%E2%80%93Morse_sequence#Hash_collisions) and do not support division by `2`.
