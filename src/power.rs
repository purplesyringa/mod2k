//! Arithmetic modulo `2^8`, `2^16`, `2^32`, and `2^64`.
//!
//! Most combinations of operations are compiled as efficiently as possible. Note that these types
//! behave more like modular arithmetic than `uK`:
//!
//! - Left shifts are unbounded.
//! - Right shifts are not implemented because `2` is not invertible, and left shifts by negative
//!   amounts panic.
//! - Arithmetic doesn't panic on overflow in debug.
//! - Negation is implemented with wrapping semantics.

use super::Mod;
use core::ops::{Add, Mul, Neg, Shl, Sub};

macro_rules! define_type {
    (
        #[$meta:meta]
        $ty:ident as $native:ident, $signed:ident,
        test in $test_mod:ident
    ) => {
        // The `value` field stores the remainder.
        crate::macros::define_type_basics! {
            #[$meta]
            $ty as $native,
            shr = false
        }

        impl $ty {
            const CARMICHAEL: u64 = 1 << ($native::BITS - 2);
        }

        impl Mod for $ty {
            type Native = $native;
            const MODULUS: $native = 0;
            const ZERO: Self = Self { value: 0 };
            const ONE: Self = Self { value: 1 };

            #[inline]
            fn new(x: $native) -> Self {
                Self { value: x }
            }

            #[inline]
            unsafe fn new_unchecked(x: $native) -> Self {
                Self { value: x }
            }

            #[inline]
            fn remainder(self) -> $native {
                self.value
            }

            #[inline]
            fn to_raw(self) -> $native {
                self.value
            }

            #[inline]
            fn is<const C: u64>(self) -> bool {
                const {
                    assert!(C <= $native::MAX as u64, "constant out of bounds");
                }
                self.value == C as $native
            }

            #[inline]
            fn is_zero(&self) -> bool {
                self.value == 0
            }

            fn pow(self, mut n: u64) -> Self {
                if n >= Self::CARMICHAEL {
                    if self.value & 1 == 0 {
                        // `2^(big number) = 0 (mod 2^k)`.
                        return Self::ZERO;
                    }
                    // `x` is invertible, so `x^lambda = 1 (mod 2^k)`.
                    n %= Self::CARMICHAEL;
                }
                self.pow_internal(n, Self::ONE)
            }

            #[inline]
            fn is_invertible(&self) -> bool {
                self.value & 1 == 1
            }

            fn inverse(self) -> Option<Self> {
                if self.value & 1 == 0 {
                    return None;
                }
                let mut x = self;
                for _ in 0..$native::BITS.ilog2() {
                    x *= Self::new(2) - self * x;
                }
                Some(x)
            }
        }

        impl Add for $ty {
            type Output = Self;

            #[inline]
            fn add(self, other: Self) -> Self {
                Self::new(self.value.wrapping_add(other.value))
            }
        }

        impl Sub for $ty {
            type Output = Self;

            #[inline]
            fn sub(self, other: Self) -> Self {
                Self::new(self.value.wrapping_sub(other.value))
            }
        }

        impl Mul for $ty {
            type Output = Self;

            #[inline]
            #[allow(clippy::suspicious_arithmetic_impl, reason = "2^k mod (2^k - 1) = 1")]
            fn mul(self, other: Self) -> Self {
                Self::new(self.value.wrapping_mul(other.value))
            }
        }

        impl Neg for $ty {
            type Output = Self;

            #[inline]
            fn neg(self) -> Self {
                Self::new(self.value.wrapping_neg())
            }
        }

        impl Shl<i64> for $ty {
            type Output = Self;

            #[inline]
            fn shl(self, n: i64) -> Self {
                assert!(n >= 0, "shift by negative amount");
                self << (n as u64)
            }
        }

        impl Shl<u64> for $ty {
            type Output = Self;

            #[inline]
            fn shl(self, n: u64) -> Self {
                if n >= $native::BITS.into() {
                    Self::ZERO
                } else {
                    Self::new(self.value << n as u32)
                }
            }
        }

        impl PartialEq for $ty {
            #[inline]
            fn eq(&self, other: &$ty) -> bool {
                self.value == other.value
            }
        }

        #[cfg(test)]
        mod $test_mod {
            use super::{Mod, $ty};

            crate::macros::test_ty!($ty as $native, $signed, shr = false);
            crate::macros::test_exact_raw!($ty as $native);
        }
    };
}

define_type! {
    /// Arithmetic modulo `2^8 = 256`.
    Power8 as u8, i8, test in test8
}

define_type! {
    /// Arithmetic modulo `2^16 = 65536`.
    Power16 as u16, i16, test in test16
}

define_type! {
    /// Arithmetic modulo `2^32 = 4294967296`.
    Power32 as u32, i32, test in test32
}

define_type! {
    /// Arithmetic modulo `2^64 = 18446744073709551616`.
    Power64 as u64, i64, test in test64
}

#[cfg(doctest)]
#[allow(dead_code, reason = "ad-hoc compile-fail test")]
/// ```compile_fail
/// <mod2k::Power8 as mod2k::Mod>::ZERO >> 0;
/// ```
///
/// ```compile_fail
/// <mod2k::Power16 as mod2k::Mod>::ZERO >> 0;
/// ```
///
/// ```compile_fail
/// <mod2k::Power32 as mod2k::Mod>::ZERO >> 0;
/// ```
///
/// ```compile_fail
/// <mod2k::Power64 as mod2k::Mod>::ZERO >> 0;
/// ```
fn test_shr() {}
