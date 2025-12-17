//! Fast arithmetic modulo `2^k`, `2^k - 1`, and `2^k - d`.
//!
//! Modular arithmetic is useful for fast hashing, verification of polynomial operations, and as
//! a ring balancing the cost of division with the cost of other operations. Different moduli make
//! different quality vs performance tradeoffs:
//!
//! 1. Large prime moduli have the best quality, but operations are quite slow due to the complexity
//!    of reduction, even if tricks like [Montgomery multiplication][montgomery] are used.
//! 2. Primes like `2^61 - 1` can be reduced significantly faster, but they are relatively rare, so
//!    you can lose several bits of precision compared to the largest prime fitting in the data
//!    type.
//! 3. Moduli like `2^64 - 1` support even faster implementations, but aren't prime. Still, their
//!    factorization is non-trivial and contains somewhat large primes, so their quality may be
//!    tolerable.
//! 4. Power-of-two moduli are the fastest, but [have seed-independent collisions][thue-morse] and
//!    do not support division by two.
//!
//! This crate provides a uniform interface to highly optimized implementations of all these moduli,
//! enabling you to easily try different options and find the best one. The supported moduli are:
//!
//! - ["Big" primes](big_prime): `2^8 - 5`, `2^16 - 15`, `2^32 - 5`, `2^64 - 59`.
//! - [Primes](prime): `2^7 - 1`, `2^13 - 1`, `2^31 - 1`, `2^61 - 1`.
//! - ["Fast"](fast): `2^8 - 1`, `2^16 - 1`, `2^32 - 1`, `2^64 - 1`.
//! - [Powers of two](power): `2^8`, `2^16`, `2^32`, `2^64`.
//!
//! Generally speaking, "fast" moduli pay a cost of 1-3 additional instructions per operation
//! compared to power-of-two moduli. Multiplication in `prime` is significantly slower than in
//! `fast`, and other operations are slightly slower. `big_prime` is the slowest of all, having slow
//! multiplication and shifts.
//!
//! [thue-morse]: https://en.wikipedia.org/wiki/Thue%E2%80%93Morse_sequence#Hash_collisions
//! [montgomery]: https://en.wikipedia.org/wiki/Montgomery_modular_multiplication
//! [num-modular]: https://docs.rs/num-modular/latest/num_modular/
//!
//!
//! ## API
//!
//! All types in this crate implement the [`Mod`] trait. With [`Mod`] and built-in operations, you
//! have access to most primitive operations:
//!
//! - `+`, `-` (both binary and unary), and `*` work straightforwardly.
//! - [`inverse`](Mod::inverse) computes the multiplicative inverse if it exists, i.e. if the
//!   argument `x` and the modulus are coprime.
//! - `x / y` computes the product of `x` and the multiplicative inverse of `y`. If `y` is not
//!   invertible, this operation panics. Note that computing inverses is slow, so they should
//!   ideally computed once and then reused.
//! - `pow` computes exponents.
//! - `<<` and `>>` correspond to multiplication and division by powers of two, respectively.
//!   Arbitrarily large and negative shift amounts are supported. (Division is not supported for
//!   `2^k` moduli.)
//! - `==` performs modular comparison.
//! - [`Display`](core::fmt::Display) and related traits print the remainder.
//!
//!
//! ## Bare metal support
//!
//! This is a `#![no_std]` crate.

// Funnel shifts are useful for prime moduli, but aren't stabilized yet.
// #![feature(funnel_shifts)]
#![no_std]
#![warn(clippy::cargo)]

#[cfg(test)]
extern crate std;

pub mod big_prime;
pub mod fast;
mod macros;
pub mod power;
pub mod prime;
mod traits;

pub use big_prime::*;
pub use fast::*;
pub use power::*;
pub use prime::*;
pub use traits::Mod;
