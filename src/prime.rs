//! Arithmetic modulo `2^7 - 1`, `2^13 - 1`, `2^31 - 1`, and `2^61 - 1`.
//!
//! Most combinations of operations are compiled as efficiently as possible. A notable exception is
//! shifting by a variable amount: it needs to be reduced modulo `k`, and for `k`s in this
//! submodule, this is not cheap. If the amount is guaranteed to be small (e.g. `< k`, `< 2 * k`, or
//! fits in `u32`), you can help the compiler optimize reduction with [`assert`] or
//! [`assert_unchecked`](core::hint::assert_unchecked).

use core::ops::{Add, Mul, Neg, Shl, Shr, Sub};

macro_rules! define_type {
    (
        #[$meta:meta]
        $ty:ident as $native:ident, $signed:ident,
        test in $test_mod:ident,
        k = $k:literal
    ) => {
        #[$meta]
        ///
        /// See [module-level documentation](self) for more information.
        #[derive(Clone, Copy, Default)]
        pub struct $ty {
            /// Stores the remainder exactly.
            value: $native,
        }

        crate::macros::define_type_basics!($ty as $native, shr = true);

        impl $ty {
            const MODULUS: $native = (1 << $k) - 1;
            #[allow(unused, reason = "used by tests")]
            const CARMICHAEL: u64 = Self::MODULUS as u64 - 1;

            /// Create a value corresponding to `x mod (2^k - 1)`.
            #[inline]
            pub const fn new(x: $native) -> Self {
                Self {
                    value: x % Self::MODULUS,
                }
            }

            /// Create a value corresponding to `x`, assuming `x < 2^k - 1`.
            ///
            /// This function is faster than [`new`](Self::new), but assumes `x` does not need to be
            /// reduced modulo `2^k - 1`. It does not perform any checks to validate this is the
            /// case.
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
                self.value
            }

            /// Get the internal optimized representation of the number.
            ///
            /// For prime moduli, this is the same thing as [`remainder`](Self::remainder). This is
            /// present for compatibility with fast moduli, where `to_raw` is faster.
            #[inline]
            pub const fn to_raw(self) -> $native {
                self.value
            }

            /// Compare for equality with a constant.
            ///
            /// This is the same thing as `x == ModK::new(C)`, but asserts in compile-time that `C`
            /// is a valid remainder. This function is mostly present for compatibility with fast
            /// moduli, for which `is` is faster than `==`.
            #[inline]
            pub const fn is<const C: $native>(self) -> bool {
                const {
                    assert!(C < Self::MODULUS, "constant out of bounds");
                }
                self.value == C
            }

            /// Compare for equality with zero.
            ///
            /// This is equialvent to `x.is::<0>()` or `x == ModK::ZERO`.
            #[inline]
            pub const fn is_zero(self) -> bool {
                self.value == 0
            }

            /// Compute `x^n mod (2^k - 1)`.
            ///
            /// The current implementation uses iterative binary exponentiation, combining it with
            /// [Euler's theorem][1] to reduce exponents. It works in `O(log n)`.
            ///
            /// [1]: https://en.wikipedia.org/wiki/Euler%27s_theorem
            pub fn pow(self, n: u64) -> Self {
                if n == 0 {
                    return Self::ONE;
                }
                // For prime moduli `p` and `x != 0`, FLT enables taking `n` modulo `p - 1`. We
                // instead use the adjustment
                //     n' = n - n // (p + 1) * (p - 1)
                // ...which is only slightly worse, but can be computed much faster since `p + 1`
                // is a power of two.
                //
                // It also turns out that `n > 0` implies `n' > 0`, since in
                //     n - n // (p + 1) * (p - 1) >= n - n // (p - 1) * (p - 1) >= 0
                // ...both equalities cannot hold at the same time: the second equality requires
                // `n = (p - 1) * k`, but for such `n`
                //     n // (p + 1) <= n / (p + 1) < k = n // (p - 1)
                // ...so the first equality can't hold. This allows the formula to be used even for
                // `x = 0`.
                let p = Self::MODULUS as u64;
                let n = n - n / (p + 1) * (p - 1);
                unsafe {
                    // SAFETY: proven above.
                    core::hint::assert_unchecked(n != 0);
                }
                self.pow_internal(n)
            }

            /// Check if the value is invertible, i.e. if `x != 0 (mod (2^k - 1))`.
            ///
            /// This method is provided for compatibility with fast moduli, for which the check is
            /// more complicated.
            #[inline]
            pub fn is_invertible(self) -> bool {
                self.value != 0
            }

            crate::macros::define_exgcd_inverse!(true);

            #[inline]
            fn shift_internal(self, n: u32, left: bool) -> Self {
                debug_assert!(n < $k);
                // SAFETY: Type invariant.
                unsafe {
                    core::hint::assert_unchecked(self.value < Self::MODULUS);
                }

                // Effectively a rotation of `self.value` as a `k`-bit number by `n`.
                let x = if cfg!(not(target_arch = "aarch64")) || $native::BITS < 64 {
                    // Place two copies of the input side by side, shift and take `k` bits at
                    // a fixed position. Requires a single possibly variable shift. For `Mod61`,
                    // x86-64 is great due to `shld`/`shrd`, but ARM is bad.
                    let offset = $native::BITS - $k;

                    // Simpler and faster, but nightly-only. [1]
                    // [1]: https://github.com/rust-lang/rust/issues/145686
                    // if left {
                    //     self.value.funnel_shl(self.value << offset, n) & Self::MODULUS
                    // } else {
                    //     self.value.funnel_shr(self.value << offset, n) >> offset
                    // }

                    let double =
                        u128::from(self.value) << offset | u128::from(self.value) << $native::BITS;
                    if left {
                        ((double << n) >> $native::BITS) as $native & Self::MODULUS
                    } else {
                        (double >> n) as $native >> offset
                    }
                } else {
                    // Split the input into two parts, rearrange and combine them. Great for
                    // constant amounts on ARM because `lsr` can be merged into `or`. Slow for
                    // variable amounts due to having to compute shifts.
                    if left {
                        ((self.value << n) & Self::MODULUS) | (self.value >> ($k - n))
                    } else {
                        (self.value >> n) | (self.value & ((1 << n) - 1)) << ($k - n)
                    }
                };
                // We'd prefer to use the first method for variable amounts and the second method
                // for constant amounts, but we have to live with a small regression because we
                // can't branch based on that.

                // SAFETY: The rotation fits in `k` bits by definition, and it can't be all ones
                // because the input can't be all ones.
                unsafe { Self::from_remainder_unchecked(x) }
            }
        }

        impl Add for $ty {
            type Output = Self;

            #[inline]
            fn add(self, other: Self) -> Self {
                let sum = self.value + other.value;
                let (new_sum, borrow) = sum.overflowing_sub(Self::MODULUS);
                // SAFETY: `x, y < 2^k - 1` implies `x + y < 2 * (2^k - 1)`. Subtracting `2^k - 1`
                // if necessary guarantees the chosen sum is `< 2^k - 1`.
                unsafe { Self::from_remainder_unchecked(if borrow { sum } else { new_sum }) }
            }
        }

        impl Sub for $ty {
            type Output = Self;

            #[inline]
            fn sub(self, other: Self) -> Self {
                let (mut diff, borrow) = self.value.overflowing_sub(other.value);
                if borrow {
                    diff = diff.wrapping_add(Self::MODULUS);
                }
                // SAFETY: `-(2^k - 1) < x - y < 2^k - 1`, so after correcting negative numbers
                // `diff < 2^k - 1`.
                unsafe { Self::from_remainder_unchecked(diff) }
            }
        }

        impl Mul for $ty {
            type Output = Self;

            #[inline]
            fn mul(self, other: Self) -> Self {
                // `u128` is sufficiently large to fit any product, and LLVM is good at replacing it
                // with the smallest optimal type.
                let product = u128::from(self.value) * u128::from(other.value);
                let low = (product as $native) & Self::MODULUS;
                let high = (product >> $k) as $native;
                // Can't use `+` from `Self` here because `low` and `high` might be equal to
                // `2^k - 1`, and calling `from_remainder_unchecked` on that is UB.
                let sum = low + high;
                let (new_sum, borrow) = sum.overflowing_sub(Self::MODULUS);
                // SAFETY: `low` and `high` can't both be equal to `2^k - 1`, so
                // `sum < 2 * (2^k - 1)`, which can be reduced straightforwardly.
                unsafe { Self::from_remainder_unchecked(if borrow { sum } else { new_sum }) }
            }
        }

        impl Neg for $ty {
            type Output = Self;

            #[inline]
            fn neg(self) -> Self {
                if self.value == 0 {
                    Self::ZERO
                } else {
                    // SAFETY: `value > 0` implies `MODULUS - value < MODULUS`.
                    unsafe { Self::from_remainder_unchecked(Self::MODULUS - self.value) }
                }
            }
        }

        impl Shl<i64> for $ty {
            type Output = Self;

            #[inline]
            fn shl(self, n: i64) -> Self {
                self.shift_internal(
                    if (0..$k).contains(&n) {
                        n as u32
                    } else {
                        n.rem_euclid($k) as u32
                    },
                    true,
                )
            }
        }

        impl Shl<u64> for $ty {
            type Output = Self;

            #[inline]
            #[allow(clippy::suspicious_arithmetic_impl, reason = "2^k = 1 (mod (2^k - 1))")]
            fn shl(self, n: u64) -> Self {
                self.shift_internal(if n < $k { n as u32 } else { (n % $k) as u32 }, true)
            }
        }

        impl Shr<i64> for $ty {
            type Output = Self;

            #[inline]
            fn shr(self, n: i64) -> Self {
                self.shift_internal(
                    if (0..$k).contains(&n) {
                        n as u32
                    } else {
                        n.rem_euclid($k) as u32
                    },
                    false,
                )
            }
        }

        impl Shr<u64> for $ty {
            type Output = Self;

            #[inline]
            #[allow(clippy::suspicious_arithmetic_impl, reason = "2^k = 1 (mod (2^k - 1))")]
            fn shr(self, n: u64) -> Self {
                self.shift_internal(if n < $k { n as u32 } else { (n % $k) as u32 }, false)
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
            use super::$ty;

            crate::macros::test_ty!($ty as $native, $signed, shr = true);

            #[test]
            fn raw() {
                for x in -10..10 {
                    let x = x as $native;
                    assert_eq!($ty::new(x).to_raw(), x % $ty::MODULUS);
                }
            }
        }
    };
}

define_type! {
    /// Arithmetic modulo `2^7 - 1 = 127`.
    Mod7 as u8, i8, test in test7, k = 7
}

define_type! {
    /// Arithmetic modulo `2^13 - 1 = 8191`.
    Mod13 as u16, i16, test in test13, k = 13
}

define_type! {
    /// Arithmetic modulo `2^31 - 1 = 2147483647`.
    Mod31 as u32, i32, test in test31, k = 31
}

define_type! {
    /// Arithmetic modulo `2^61 - 1 = 2305843009213693951`.
    Mod61 as u64, i64, test in test61, k = 61
}

#[cfg(doctest)]
#[allow(dead_code, reason = "ad-hoc compile-fail test")]
/// ```compile_fail
/// mod2km1::prime::Mod7::ZERO.is::<{ 1 << 7 }>();
/// ```
///
/// ```compile_fail
/// mod2km1::prime::Mod13::ZERO.is::<{ 1 << 13 }>();
/// ```
///
/// ```compile_fail
/// mod2km1::prime::Mod31::ZERO.is::<{ 1 << 31 }>();
/// ```
///
/// ```compile_fail
/// mod2km1::prime::Mod61::ZERO.is::<{ 1 << 61 }>();
/// ```
fn test_is() {}
