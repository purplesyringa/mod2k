//! Fast arithmetic modulo `2^k`, `2^k - 1`, and `2^k - d`.
//!
//! Modular arithmetic is useful for fast hashing, verification of polynomial operations, and as
//! a ring balancing the cost of division with the cost of other operations. Different moduli make
//! different quality vs performance tradeoffs:
//!
//! 1. Big prime moduli have the best quality, but operations are quite slow due to the complexity
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
//! 1. ["Big" primes](big_prime): `2^8 - 5`, `2^16 - 15`, `2^32 - 5`, `2^64 - 59`.
//! 2. [Primes](prime): `2^7 - 1`, `2^13 - 1`, `2^31 - 1`, `2^61 - 1`.
//! 3. ["Fast"](fast): `2^8 - 1`, `2^16 - 1`, `2^32 - 1`, `2^64 - 1`.
//! 4. [Powers of two](power): `2^8`, `2^16`, `2^32`, `2^64`.
//!
//! Generally speaking,
//!
//! - Power-of-two moduli are the fastest.
//! - "Fast" moduli are almost as fast, usually paying a cost of 1-3 additional instructions per
//!   operation compared to power-of-two moduli, but inversion is much slower. As an exception to
//!   the general rule that "fast" moduli are faster than primes, "fast" moduli also have the
//!   slowest implementation of `is_invertible`.
//! - Moduli in `prime` have significantly slower multiplication, but the rest of arithmetic is
//!   only slightly slower than that of "fast" moduli.
//! - Moduli in `big_prime` have even slower multiplication, and the performance of shifts is
//!   degraded to general-purpose multiplication.
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
//! ## Example
//!
//! ```rust
//! use mod2k::{Mod, Prime31}; // arithmetic modulo 2^31 - 1 = 2147483647
//!
//! assert_eq!(Prime31::new(5) + Prime31::new(7), Prime31::new(12));
//! assert_eq!((-Prime31::ONE) * (-Prime31::ONE), Prime31::ONE);
//! assert_eq!((-Prime31::ONE).remainder(), Prime31::MODULUS - 1);
//! ```
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
mod xgcd;

pub use big_prime::*;
pub use fast::*;
pub use power::*;
pub use prime::*;
pub use traits::Mod;
