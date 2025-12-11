//! Fast arithmetic modulo `2^k` and `2^k - 1`.
//!
//! Modular arithmetic is useful for fast hashing, verification of polynomial operations, and as
//! a field balancing the cost of division with the cost of other operations. Different moduli make
//! different quality vs performance tradeoffs:
//!
//! 1. Large prime moduli have the best quality, but operations are quite slow due to the complexity
//!    of reduction, even with [Montgomery multiplication][montgomery].
//! 2. Primes like `2^61 - 1` can be reduced significantly faster, but they are relatively rare, so
//!    you can lose several bits of precision compared to the largest prime fitting in the data
//!    type.
//! 3. Moduli like `2^64 - 1` support even faster implementations, but aren't prime. Still, their
//!    factorization is non-trivial and contains somewhat large primes, so their quality may be
//!    tolerable.
//! 4. Power-of-two moduli are the fastest, but [have seed-independent collisions][thue-morse] and
//!    do not support division by two.
//!
//! The general-purpose [num-modular] crate implements (1). This crate provides highly optimized
//! implementations of (2), (3), and (4) with uniform interface to allow you to play with different
//! options and choose the best one. The supported moduli are:
//!
//! - Primes: `2^7 - 1`, `2^13 - 1`, `2^31 - 1`, `2^61 - 1`.
//! - "Fast": `2^8 - 1`, `2^16 - 1`, `2^32 - 1`, `2^64 - 1`.
//! - Powers of two: `2^8`, `2^16`, `2^32`, `2^64`.
//!
//! Generally speaking, "fast" moduli pay a cost of 1-3 additional instructions per operation
//! compared to power-of-two moduli. Multiplication in `prime` is significantly slower than in
//! `fast`, and other operations are slightly slower.
//!
//! [thue-morse]: https://en.wikipedia.org/wiki/Thue%E2%80%93Morse_sequence#Hash_collisions
//! [montgomery]: https://en.wikipedia.org/wiki/Montgomery_modular_multiplication
//! [num-modular]: https://docs.rs/num-modular/latest/num_modular/
//!
//!
//! ## API
//!
//! Types in this crate implement most primitive operations:
//!
//! - `+`, `-` (both binary and unary), and `*` work straightforwardly.
//! - [`inverse`](fast::Mod64::inverse) computes the multiplicative inverse if it exists, i.e. if
//!   the argument `x` and the modulus are coprime.
//! - `x / y` computes the product of `x` and the multiplicative inverse of `y`. If `y` is not
//!   invertible, this operation panics. Note that computing inverses is slow, so they should
//!   ideally computed once and then reused.
//! - `pow` computes exponents.
//! - `<<` and `>>` correspond to multiplication and division by powers of two, respectively.
//!   Arbitrarily large and negative shift amounts are supported. (Division is not supported for
//!   `2^k` moduli.)
//! - `==` performs modular comparison.
//! - [`Display`](core::fmt::Display) and related traits print the remainder.

// #![feature(funnel_shifts)]
#![no_std]

#[cfg(test)]
extern crate std;

pub mod fast;
mod macros;
pub mod power;
pub mod prime;

// #[inline(never)]
// pub fn example(n: u64) -> u64 {
//     (n as u32 as u64) % 31
// }

#[inline(never)]
pub fn example(x: prime::Mod61, n: i64) -> prime::Mod61 {
    // x.pow(n)
    x << n
    // if n < 61 { Some(x << n) } else { None }
    // x.is_invertible()
    // x << (n & 3)
    // x >> (n & 3)
    // Some(x >> 2)
    // x - y
}
