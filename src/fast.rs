//! Arithmetic modulo `2^8 - 1`, `2^16 - 1`, `2^32 - 1`, and `2^64 - 1`.
//!
//! Most combinations of operations are compiled as efficiently as possible. A notable exception is
//! comparison with a constant: prefer `x.is::<C>()` over `x == ModK::new(C)`.

use core::ops::{Add, Mul, Neg, Shl, Shr, Sub};

macro_rules! define_type {
    (
        #[$meta:meta]
        $ty:ident as $native:ident, $signed:ident,
        test in $test_mod:ident,
        carmichael = $carmichael:literal
    ) => {
        #[$meta]
        ///
        /// See [module-level documentation](self) for more information.
        #[derive(Clone, Copy, Default)]
        pub struct $ty {
            /// Represents a zero remainder either as `0` or `T::MAX`, otherwise represents the
            /// remainder exactly.
            value: $native,
        }

        crate::macros::define_type_basics!($ty as $native);

        impl $ty {
            const MODULUS: $native = $native::MAX;
            const CARMICHAEL: u64 = $carmichael;
            const IS_PRIME: bool = false;

            /// Create a value corresponding to `x mod (2^k - 1)`.
            #[inline]
            pub const fn new(x: $native) -> Self {
                Self { value: x }
            }

            /// Create a value corresponding to `x`, assuming `x < 2^k - 1`.
            ///
            /// This function is present for compatibility with prime moduli, for which
            /// `from_remainder_unchecked` is faster than [`new`](Self::new). For fast moduli, the
            /// performance is equivalent.
            ///
            /// # Safety
            ///
            /// This function is only valid to call if `x < 2^k - 1`.
            #[inline]
            pub unsafe fn from_remainder_unchecked(x: $native) -> Self {
                debug_assert!(x < Self::MODULUS);
                Self { value: x }
            }

            /// Get the normalized residue `x mod (2^k - 1)`.
            #[inline]
            pub const fn remainder(self) -> $native {
                if self.value == $native::MAX {
                    0
                } else {
                    self.value
                }
            }

            /// Get the internal optimized representation of the number.
            ///
            /// This returns some value equivalent to `x` modulo `2^k - 1`, but not necessarily
            /// `x mod (2^k - 1)` itself. Specifically, a residue of `0` may be represented as
            /// either `0` or `2^k - 1`. Passing this value back to [`new`](Self::new) is guaranteed
            /// to produce the same value as `self`.
            #[inline]
            pub const fn to_raw(self) -> $native {
                self.value
            }

            /// Compare for equality with a constant.
            ///
            /// This is more efficient than `x == ModK::new(C)`. `C` must be a valid reminder, i.e.
            /// not be equal to `2^k - 1`.
            #[inline]
            pub const fn is<const C: $native>(self) -> bool {
                const {
                    assert!(C < Self::MODULUS, "constant out of bounds");
                }
                if C == 0 {
                    self.is_zero()
                } else {
                    self.value == C
                }
            }

            /// Compare for equality with zero.
            ///
            /// This is equialvent to `x.is::<0>()`.
            #[inline]
            pub const fn is_zero(self) -> bool {
                self.value == 0 || self.value == $native::MAX
            }

            /// Compute `x^n mod (2^k - 1)`.
            ///
            /// The current implementation uses iterative binary exponentiation, combining it with
            /// [the Carmichael function][1] to reduce exponents. It works in `O(log n)`.
            ///
            /// [1]: https://en.wikipedia.org/wiki/Carmichael_function#Exponential_cycle_length
            pub fn pow(self, n: u64) -> Self {
                if n == 0 {
                    return Self::ONE;
                }
                // The existence of non-square-free Fermat numbers is an open problem, which means
                // we can assume `2^k - 1` is square-free for all reasonable data types. A property
                // of the Carmichael function guarantees
                //     a^(n + lambda(m)) = a^n  (mod m)
                // for *all* `a`, even those not coprime with `m`, as long as `n` >= the largest
                // exponent in factorization (i.e. 1), which almost always allows us to take `n`
                // modulo `lambda(m)`.
                let new_n = if !Self::CARMICHAEL.is_power_of_two() && n <= Self::CARMICHAEL {
                    // Branching to avoid modulo is only useful for non-power-of-two moduli. LLVM
                    // can't infer that it's a no-op, so we enable it conditionally by hand.
                    n
                } else {
                    (n - 1) % Self::CARMICHAEL + 1
                };
                self.pow_internal(new_n)
            }

            /// Check if the value is invertible, i.e. if `x` is coprime with `2^k - 1`.
            ///
            /// The current implementation uses the binary Euclidian algorithm and works in `O(k)`.
            pub fn is_invertible(self) -> bool {
                // LLVM optimizes out the "extended" part of the Euclidian algorithm.
                self.inverse().is_some()
            }
        }

        impl Add for $ty {
            type Output = Self;

            #[inline]
            fn add(self, other: Self) -> Self {
                let (sum, carry) = self.value.overflowing_add(other.value);
                Self::new(sum.wrapping_add(carry as $native))
            }
        }

        impl Sub for $ty {
            type Output = Self;

            #[inline]
            fn sub(self, other: Self) -> Self {
                let (diff, borrow) = self.value.overflowing_sub(other.value);
                Self::new(diff.wrapping_sub(borrow as $native))
            }
        }

        impl Mul for $ty {
            type Output = Self;

            #[inline]
            #[allow(clippy::suspicious_arithmetic_impl, reason = "2^k mod (2^k - 1) = 1")]
            fn mul(self, other: Self) -> Self {
                let (low, high) = self.value.carrying_mul(other.value, 0);
                Self::new(low) + Self::new(high)
            }
        }

        impl Neg for $ty {
            type Output = Self;

            #[inline]
            fn neg(self) -> Self {
                Self::new(!self.value)
            }
        }

        impl Shl<i64> for $ty {
            type Output = Self;

            #[inline]
            fn shl(self, n: i64) -> Self {
                Self::new(self.value.rotate_left(n as u32))
            }
        }

        impl Shl<u64> for $ty {
            type Output = Self;

            #[inline]
            fn shl(self, n: u64) -> Self {
                Self::new(self.value.rotate_left(n as u32))
            }
        }

        impl Shr<i64> for $ty {
            type Output = Self;

            #[inline]
            fn shr(self, n: i64) -> Self {
                Self::new(self.value.rotate_right(n as u32))
            }
        }

        impl Shr<u64> for $ty {
            type Output = Self;

            #[inline]
            fn shr(self, n: u64) -> Self {
                Self::new(self.value.rotate_right(n as u32))
            }
        }

        impl PartialEq for $ty {
            #[inline]
            fn eq(&self, other: &$ty) -> bool {
                let (diff, borrow) = self.value.overflowing_sub(other.value);
                let diff = diff.wrapping_sub(borrow as $native);
                // Optimize comparison against a constant. This still produces suboptimal results
                // (`sub + sbb + sete` instead of `cmp + sete`) [1], but it's better than nothing.
                // [1]: github.com/llvm/llvm-project/issues/171676
                if other.value != 0 {
                    // SAFETY: If no overflow happened, `diff < self.value` and thus `diff < MAX`.
                    // If overflow happened, initially `diff != 0`, so subtracting 1 cannot give
                    // `diff == MAX`.
                    unsafe {
                        core::hint::assert_unchecked(diff != $native::MAX);
                    }
                }
                diff == 0 || diff == $native::MAX
            }
        }

        #[cfg(test)]
        mod $test_mod {
            use super::$ty;

            crate::macros::test_ty!($ty as $native, $signed);

            #[test]
            fn raw() {
                for x in -10..10 {
                    assert_eq!($ty::new(x as $native).to_raw(), x as $native);
                }
            }
        }
    };
}

define_type! {
    /// Arithmetic modulo `2^8 - 1 = 3 * 5 * 17`.
    Mod8 as u8, i8, test in test8, carmichael = 16
}

define_type! {
    /// Arithmetic modulo `2^16 - 1 = 3 * 5 * 17 * 257`.
    Mod16 as u16, i16, test in test16, carmichael = 256
}

define_type! {
    /// Arithmetic modulo `2^32 - 1 = 3 * 5 * 17 * 257 * 65537`.
    Mod32 as u32, i32, test in test32, carmichael = 65536
}

define_type! {
    /// Arithmetic modulo `2^64 - 1 = 3 * 5 * 17 * 257 * 641 * 65537 * 6700417`.
    Mod64 as u64, i64, test in test64, carmichael = 17153064960
}

#[cfg(doctest)]
#[allow(dead_code, reason = "ad-hoc compile-fail test")]
/// ```compile_fail
/// mod2km1::fast::Mod8::ZERO.is::<{ u8::MAX }>();
/// ```
///
/// ```compile_fail
/// mod2km1::fast::Mod16::ZERO.is::<{ u16::MAX }>();
/// ```
///
/// ```compile_fail
/// mod2km1::fast::Mod32::ZERO.is::<{ u32::MAX }>();
/// ```
///
/// ```compile_fail
/// mod2km1::fast::Mod64::ZERO.is::<{ u64::MAX }>();
/// ```
fn test_is() {}
