//! Arithmetic modulo `2^7 - 1`, `2^13 - 1`, `2^31 - 1`, and `2^61 - 1`.
//!
//! Most combinations of operations are compiled as efficiently as possible. A notable exception is
//! shifting by a variable amount: it needs to be reduced modulo `k`, and for `k`s in this
//! submodule, this is not cheap. If the amount is guaranteed to be small (e.g. `< k`, `< 2 * k`, or
//! fits in `u32`), you can help the compiler optimize reduction with [`assert`] or
//! [`assert_unchecked`](core::hint::assert_unchecked).

use super::Mod;
use core::ops::{Add, Mul, Neg, Shl, Shr, Sub};

macro_rules! define_type {
    (
        #[$meta:meta]
        $ty:ident as $native:ident, $signed:ident,
        test in $test_mod:ident,
        k = $k:literal
    ) => {
        // The `value` field stores the remainder.
        crate::macros::define_type_basics! {
            #[$meta]
            $ty as $native,
            shr = true
        }

        impl $ty {
            #[allow(unused, reason = "used by tests")]
            const CARMICHAEL: u64 = Self::MODULUS as u64 - 1;

            /// Reduce a number up to `2 * m - 1`.
            ///
            /// # Safety
            ///
            /// `x <= 2 * m - 1` must hold.
            #[inline]
            unsafe fn reduce_2x(x: $native) -> Self {
                let (diff, borrow) = x.overflowing_sub(Self::MODULUS);
                // SAFETY: If `x < m`, this chooses `x`. If `x >= m`, this choses
                // `x - m <= (2 * m - 1) - m < m`.
                unsafe { Self::new_unchecked(if borrow { x } else { diff }) }
            }

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
                unsafe { Self::new_unchecked(x) }
            }
        }

        impl Mod for $ty {
            type Native = $native;
            const MODULUS: $native = (1 << $k) - 1;
            const ZERO: Self = Self { value: 0 };
            const ONE: Self = Self { value: 1 };

            #[inline]
            fn new(x: $native) -> Self {
                let low = x & ((1 << $k) - 1);
                let high = x >> $k;
                // SAFETY: `low <= m`, `high` is very small for `$k`s in question, thus
                // `low + high <= 2 * m - 1`.
                unsafe { Self::reduce_2x(low + high) }
            }

            #[inline]
            unsafe fn new_unchecked(x: $native) -> Self {
                debug_assert!(x < Self::MODULUS);
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
                    assert!(C < Self::MODULUS as u64, "constant out of bounds");
                }
                self.value == C as $native
            }

            #[inline]
            fn is_zero(&self) -> bool {
                self.value == 0
            }

            fn pow(self, n: u64) -> Self {
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
                self.pow_internal(n, Self::ONE)
            }

            #[inline]
            fn is_invertible(&self) -> bool {
                self.value != 0
            }

            crate::macros::define_exgcd_inverse!(
                prime = true,
                limited_value = true,
                fast_shr = true
            );
        }

        impl Add for $ty {
            type Output = Self;

            #[inline]
            fn add(self, other: Self) -> Self {
                // SAFETY: `x, y <= m - 1` implies `x + y <= 2 * m - 2`.
                unsafe { Self::reduce_2x(self.value + other.value) }
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
                // SAFETY: `-m < x - y < m`, so after correcting negative numbers `diff < m`.
                unsafe { Self::new_unchecked(diff) }
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
                // SAFETY: `low, high <= m`. Both can't be equal to `m` at the same time, so
                // `low + high <= 2 * m - 1`.
                unsafe { Self::reduce_2x(low + high) }
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
                    unsafe { Self::new_unchecked(Self::MODULUS - self.value) }
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
            use super::{Mod, $ty};

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
    Prime7 as u8, i8, test in test7, k = 7
}

define_type! {
    /// Arithmetic modulo `2^13 - 1 = 8191`.
    Prime13 as u16, i16, test in test13, k = 13
}

define_type! {
    /// Arithmetic modulo `2^31 - 1 = 2147483647`.
    Prime31 as u32, i32, test in test31, k = 31
}

define_type! {
    /// Arithmetic modulo `2^61 - 1 = 2305843009213693951`.
    Prime61 as u64, i64, test in test61, k = 61
}

#[cfg(doctest)]
#[allow(dead_code, reason = "ad-hoc compile-fail test")]
/// ```compile_fail
/// use mod2k::Mod;
/// mod2k::Prime7::ZERO.is::<{ 1 << 7 }>();
/// ```
///
/// ```compile_fail
/// use mod2k::Mod;
/// mod2k::Prime13::ZERO.is::<{ 1 << 13 }>();
/// ```
///
/// ```compile_fail
/// use mod2k::Mod;
/// mod2k::Prime31::ZERO.is::<{ 1 << 31 }>();
/// ```
///
/// ```compile_fail
/// use mod2k::Mod;
/// mod2k::Prime61::ZERO.is::<{ 1 << 61 }>();
/// ```
fn test_is() {}
