//! Arithmetic modulo `2^8 - 5`, `2^16 - 15`, `2^32 - 5`, and `2^64 - 59`.
//!
//! These types are quite slow. Shifts are the slowest operations, since the multiplicative order
//! of `2` is large for these moduli. Prefer left shifts over right shifts and precalculate powers
//! of `2` if necessary. If the shift amount is guaranteed to be small (e.g. `< k` or `< 2 * k`),
//! you can help the compiler optimize reduction with [`assert`] or
//! [`assert_unchecked`](core::hint::assert_unchecked).

use super::Mod;
use core::ops::{Add, Mul, Neg, Shl, Shr, Sub};

macro_rules! define_type {
    (
        #[$meta:meta]
        $ty:ident as $native:ident, $signed:ident,
        test in $test_mod:ident,
        d = $d:literal,
        d_order = $d_order:literal,
        d_inv = $d_inv:literal
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

            #[inline(always)]
            fn shift_internal(self, q: i64, r: u32, left: bool) -> Self {
                debug_assert!(r < $native::BITS);

                // For constant `n`, the factor is computed in compile time.
                //
                // For constant `q = 0`, `pow_internal` is optimized out.
                let factor = if left {
                    // Calculate `2^(kq + r)` as `d^q * 2^r`.
                    //
                    // Reduces to `x * 2^r` for `q = 0`, using shifts instead of multiplication on
                    // the first reduction step. Slightly suboptimal due to [1].
                    // [1]: https://github.com/llvm/llvm-project/issues/171920
                    Self::new($d).pow_internal(q.rem_euclid($d_order) as u64, Self::new(1 << r))
                } else {
                    // Calculate `2^(-(kq + r))` as `((d^-1)^(q + 1) * 2^(k - r))`.
                    //
                    // Suboptimal lowering for constant `n = 0` because `factor` is computed as
                    // `2^k - d + 1`, not `1` exactly. Hopefully not too big of a deal.
                    //
                    // `q = 0` leaves two multiplications, but improving this further requires
                    // faster multiplication algorithms in general.
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
                if borrow { self.value } else { diff }
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
                // `prime.rs` demonstrates that the adjustment
                //     n' = n - n // 2^k * (p - 1)
                // ...works for all `x`.
                let n = n - n.unbounded_shr($native::BITS) * (Self::MODULUS as u64 - 1);
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

            crate::macros::define_exgcd_inverse!(
                prime = true,
                limited_value = false,
                fast_shr = false
            );
        }

        impl Add for $ty {
            type Output = Self;

            #[inline]
            fn add(self, other: Self) -> Self {
                let (sum, carry) = self.value.overflowing_add(other.value);
                let (sum, carry) = sum.overflowing_add(if carry { $d } else { 0 });
                Self::new(if carry { sum.wrapping_add($d) } else { sum })
            }
        }

        impl Sub for $ty {
            type Output = Self;

            #[inline]
            fn sub(self, other: Self) -> Self {
                // Bad lowering on aarch64 due to the issue in `remainder` and [1].
                // [1]: https://github.com/llvm/llvm-project/issues/171884
                let (diff, borrow) = self.value.overflowing_sub(other.remainder());
                Self::new(if borrow {
                    diff.wrapping_add(Self::MODULUS)
                } else {
                    diff
                })
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
                Self::new(if carry { low.wrapping_add($d) } else { low })
            }
        }

        impl Neg for $ty {
            type Output = Self;

            #[inline]
            fn neg(self) -> Self {
                Self::new(
                    if self.value > Self::MODULUS {
                        Self::MODULUS.wrapping_mul(2)
                    } else {
                        Self::MODULUS
                    }
                    .wrapping_sub(self.value),
                )
            }
        }

        impl Shl<i64> for $ty {
            type Output = Self;

            fn shl(self, n: i64) -> Self {
                self.shift_internal(
                    n.div_euclid($native::BITS as i64),
                    n.rem_euclid($native::BITS as i64) as u32,
                    true,
                )
            }
        }

        impl Shl<u64> for $ty {
            type Output = Self;

            fn shl(self, n: u64) -> Self {
                self.shift_internal(
                    (n / $native::BITS as u64) as i64,
                    (n as u64 % $native::BITS as u64) as u32,
                    true,
                )
            }
        }

        impl Shr<i64> for $ty {
            type Output = Self;

            fn shr(self, n: i64) -> Self {
                self.shift_internal(
                    n.div_euclid($native::BITS as i64),
                    n.rem_euclid($native::BITS as i64) as u32,
                    false,
                )
            }
        }

        impl Shr<u64> for $ty {
            type Output = Self;

            fn shr(self, n: u64) -> Self {
                self.shift_internal(
                    (n / $native::BITS as u64) as i64,
                    (n as u64 % $native::BITS as u64) as u32,
                    false,
                )
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
    BigPrime8 as u8, i8, test in test7, d = 5, d_order = 25, d_inv = 201
}

define_type! {
    /// Arithmetic modulo `2^16 - 15 = 65521`.
    BigPrime16 as u16, i16, test in test13, d = 15, d_order = 585, d_inv = 61153
}

define_type! {
    /// Arithmetic modulo `2^32 - 5 = 4294967291`.
    BigPrime32 as u32, i32, test in test31, d = 5, d_order = 2147483645, d_inv = 3435973833
}

define_type! {
    /// Arithmetic modulo `2^64 - 59 = 18446744073709551557`.
    BigPrime64 as u64, i64,
    test in test61,
    d = 59,
    d_order = 4611686018427387889,
    d_inv = 14694863923124558020
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
