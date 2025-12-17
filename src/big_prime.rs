//! Arithmetic modulo `2^8 - 5`, `2^16 - 15`, `2^32 - 5`, and `2^64 - 59`.
//!
//! These types are quite slow. Shifts are the slowest operations, since the multiplicative order
//! of `2` is large for these moduli. Prefer left shifts over right shifts and precalculate powers
//! of `2` if necessary. If the shift amount is guaranteed to be small (e.g. `< k` or `< 2 * k`),
//! you can help the compiler optimize reduction with [`assert`] or
//! [`assert_unchecked`](core::hint::assert_unchecked).

use super::Mod;
use core::hint::select_unpredictable;
use core::ops::{Add, Mul, Neg, Shl, Shr, Sub};

macro_rules! define_type {
    (
        #[$meta:meta]
        $ty:ident as $native:ident, $signed:ident,
        test in $test_mod:ident,
        d = $d:literal,
        d_order = $d_order:literal,
        d_inv = $d_inv:literal,
        inv_strategy = $($inv_strategy:tt)*
    ) => {
        // The `value` field stores some value equivalent to `x` modulo `2^k - d`.
        crate::macros::define_type_basics! {
            #[$meta]
            $ty as $native,
            shr = true
        }

        impl $ty {
            #[allow(unused, reason = "used by tests")]
            const CARMICHAEL: u64 = Self::MODULUS as u64 - 1;

            #[inline]
            fn shift_fast_path<const LEFT: bool>(self, n: u32) -> Self {
                let factor = if LEFT {
                    // Multiplication is optimized to shifts somewhat suboptimally due to [1]. If
                    // bitwise `&` is present in the source, codegen is suboptimal due to [2].
                    // [1]: https://github.com/llvm/llvm-project/issues/172097
                    // [2]: https://github.com/llvm/llvm-project/issues/171920
                    Self::new(1 << n)
                } else {
                    // `x * 2^(-n) = x * d^-1 * 2^(k - n)`. We can either compute this as
                    // `x * (d^-1 * 2^(k - n))` or `(x * d^-1) * 2^(k - n)`. There is a single
                    // multiplication and a single shift either way, but the former optimizes better
                    // for constant `n`, so it's preferable.
                    select_unpredictable(
                        n == 0,
                        Self::ONE,
                        Self::new($d_inv) * Self::new(1 << (n.wrapping_neg() % $native::BITS)),
                    )
                };

                self * factor
            }

            #[cold]
            fn shift_slow_path<const LEFT: bool>(self, q: i64, r: u32) -> Self {
                debug_assert!(q != 0);
                debug_assert!(r < $native::BITS);

                // For constant `q` and `r`, the factor is computed in compile time.
                let factor = if LEFT {
                    // `2^(kq + r) = d^q * 2^r`.
                    Self::new($d).pow_internal(q.rem_euclid($d_order) as u64, Self::new(1 << r))
                } else {
                    // `2^(-(kq + r)) = ((d^-1)^(q + 1) * 2^(k - r))`.
                    Self::new($d_inv).pow_internal(
                        (q + 1).rem_euclid($d_order) as u64,
                        Self::ONE << ($native::BITS - r),
                    )
                };

                self * factor
            }
        }

        impl crate::traits::sealed::Sealed for $ty {}
        impl Mod for $ty {
            type Native = $native;
            const MODULUS: $native = ($d as $native).wrapping_neg();
            const ZERO: Self = Self { value: 0 };
            const ONE: Self = Self { value: 1 };

            #[inline]
            fn new(x: $native) -> Self {
                Self { value: x }
            }

            #[inline]
            unsafe fn new_unchecked(x: $native) -> Self {
                debug_assert!(x < Self::MODULUS);
                Self { value: x }
            }

            #[inline]
            fn remainder(self) -> $native {
                // Bad lowering on aarch64 because codegenprepare doesn't infer
                // @llvm.usub.with.overflow.
                let (diff, borrow) = self.value.overflowing_sub(Self::MODULUS);
                select_unpredictable(borrow, self.value, diff)
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
                    || (C < $d && self.value == (C as $native + Self::MODULUS))
            }

            #[inline]
            fn is_zero(&self) -> bool {
                self.is::<0>()
            }

            fn pow(self, n: u64) -> Self {
                if n == 0 {
                    return Self::ONE;
                }
                // The same logic as in `prime.rs`.
                let q = ((n as u128 * (u64::MAX / Self::CARMICHAEL) as u128) >> 64) as u64;
                let n = n - q * Self::CARMICHAEL;
                unsafe {
                    // SAFETY: proven in `prime.rs`.
                    core::hint::assert_unchecked(n != 0);
                }
                self.pow_internal(n, Self::ONE)
            }

            #[inline]
            fn is_invertible(&self) -> bool {
                !self.is_zero()
            }

            crate::macros::define_exgcd_inverse!(prime = true, strategy = $($inv_strategy)*);
        }

        impl Add for $ty {
            type Output = Self;

            #[inline]
            fn add(self, other: Self) -> Self {
                let (sum, carry) = self.value.overflowing_add(other.value);
                let (sum, carry) = sum.overflowing_add(select_unpredictable(carry, $d, 0));
                Self::new(select_unpredictable(carry, sum.wrapping_add($d), sum))
            }
        }

        impl Sub for $ty {
            type Output = Self;

            #[inline]
            fn sub(self, other: Self) -> Self {
                // Bad lowering on aarch64 due to the issue in `remainder` and [1].
                // [1]: https://github.com/llvm/llvm-project/issues/171884
                let (diff, borrow) = self.value.overflowing_sub(other.remainder());
                Self::new(select_unpredictable(
                    borrow,
                    diff.wrapping_add(Self::MODULUS),
                    diff,
                ))
            }
        }

        impl Mul for $ty {
            type Output = Self;

            #[inline]
            fn mul(self, other: Self) -> Self {
                // `u128` is sufficiently large to fit any product, and LLVM is good at replacing it
                // with the smallest optimal type.
                let product = u128::from(self.value) * u128::from(other.value);

                if $native::BITS < 64 {
                    // If the product fits in the native word size, LLVM is great at optimizing it
                    // with Barrett reduction.
                    return Self::new((product % Self::MODULUS as u128) as $native);
                }

                // Use a smarter algorithm for large moduli, based on `d` being small.
                let mut low = product as $native;
                let mut high = (product >> $native::BITS) as $native;

                // Reduce (low, high) -> low + high * d. This can't be done on `u128` directly
                // because LLVM can't keep track of the two halves independently.
                let (tmp, carry);
                (tmp, high) = high.carrying_mul($d, 0);
                (low, carry) = low.overflowing_add(tmp);
                high += carry as $native;

                // Reduce again, this time knowing that `high < d`.
                let (low, carry) = low.overflowing_add(high * $d);
                Self::new(select_unpredictable(carry, low.wrapping_add($d), low))
            }
        }

        impl Neg for $ty {
            type Output = Self;

            #[inline]
            fn neg(self) -> Self {
                Self::new(
                    select_unpredictable(
                        self.value > Self::MODULUS,
                        Self::MODULUS.wrapping_mul(2),
                        Self::MODULUS,
                    )
                    .wrapping_sub(self.value),
                )
            }
        }

        impl Shl<i64> for $ty {
            type Output = Self;

            #[inline]
            fn shl(self, n: i64) -> Self {
                if (0..$native::BITS as i64).contains(&n) {
                    self.shift_fast_path::<true>(n as u32)
                } else {
                    self.shift_slow_path::<true>(
                        n.div_euclid($native::BITS as i64),
                        n.rem_euclid($native::BITS as i64) as u32,
                    )
                }
            }
        }

        impl Shl<u64> for $ty {
            type Output = Self;

            #[inline]
            fn shl(self, n: u64) -> Self {
                if n < $native::BITS as u64 {
                    self.shift_fast_path::<true>(n as u32)
                } else {
                    self.shift_slow_path::<true>(
                        (n / $native::BITS as u64) as i64,
                        (n as u64 % $native::BITS as u64) as u32,
                    )
                }
            }
        }

        impl Shr<i64> for $ty {
            type Output = Self;

            #[inline]
            fn shr(self, n: i64) -> Self {
                if (0..$native::BITS as i64).contains(&n) {
                    self.shift_fast_path::<false>(n as u32)
                } else {
                    self.shift_slow_path::<false>(
                        n.div_euclid($native::BITS as i64),
                        n.rem_euclid($native::BITS as i64) as u32,
                    )
                }
            }
        }

        impl Shr<u64> for $ty {
            type Output = Self;

            #[inline]
            fn shr(self, n: u64) -> Self {
                if n < $native::BITS as u64 {
                    self.shift_fast_path::<false>(n as u32)
                } else {
                    self.shift_slow_path::<false>(
                        (n / $native::BITS as u64) as i64,
                        (n as u64 % $native::BITS as u64) as u32,
                    )
                }
            }
        }

        impl PartialEq for $ty {
            #[inline]
            fn eq(&self, other: &$ty) -> bool {
                let min = self.value.min(other.value);
                let max = self.value.max(other.value);
                // `max - min` produces better codegen than `abs_diff`.
                self.value == other.value || max - min == Self::MODULUS
            }
        }

        #[cfg(test)]
        mod $test_mod {
            use super::{Mod, $ty};

            crate::macros::test_ty!($ty as $native, $signed, shr = true);
            crate::macros::test_exact_raw!($ty as $native);
        }
    };
}

define_type! {
    /// Arithmetic modulo `2^8 - 5 = 251`.
    BigPrime8 as u8, i8,
    test in test7,
    d = 5,
    d_order = 25,
    d_inv = 201,
    inv_strategy = short with 2939720171109091891
}

define_type! {
    /// Arithmetic modulo `2^16 - 15 = 65521`.
    BigPrime16 as u16, i16,
    test in test13,
    d = 15,
    d_order = 585,
    d_inv = 61153,
    inv_strategy = short with 1767152529183871249
}

define_type! {
    /// Arithmetic modulo `2^32 - 5 = 4294967291`.
    BigPrime32 as u32, i32,
    test in test31,
    d = 5,
    d_order = 2147483645,
    d_inv = 3435973833,
    inv_strategy = short with 3504881373833016115
}

define_type! {
    /// Arithmetic modulo `2^64 - 59 = 18446744073709551557`.
    BigPrime64 as u64, i64,
    test in test61,
    d = 59,
    d_order = 4611686018427387889,
    d_inv = 14694863923124558020,
    inv_strategy = long with 3751880150584993549
}

#[cfg(doctest)]
#[allow(dead_code, reason = "ad-hoc compile-fail test")]
/// ```compile_fail
/// use mod2k::Mod;
/// mod2k::BigPrime8::ZERO.is::<{ (1 << 8) - 1 }>();
/// ```
///
/// ```compile_fail
/// use mod2k::Mod;
/// mod2k::BigPrime16::ZERO.is::<{ (1 << 16) - 1 }>();
/// ```
///
/// ```compile_fail
/// use mod2k::Mod;
/// mod2k::BigPrime32::ZERO.is::<{ (1 << 32) - 1 }>();
/// ```
///
/// ```compile_fail
/// use mod2k::Mod;
/// mod2k::BigPrime64::ZERO.is::<{ (1 << 64) - 1 }>();
/// ```
fn test_is() {}
