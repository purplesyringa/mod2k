//! Arithmetic modulo `2^8 - 1`, `2^16 - 1`, `2^32 - 1`, and `2^64 - 1`.
//!
//! Computers can quickly perform arithmetic modulo `2^n` for `n = 8, 16, 32, 64`, but these moduli
//! can have undesirable properties. For example, polynomial hash functions modulo `2^n` [have
//! seed-independent collisions][thue-morse], and `2` is not invertible modulo `2^n`. This can
//! preclude such moduli from being used in certain computational problems.
//!
//! Prime moduli solve all these issues, but even deliberately chosen primes like `2^61 - 1` have
//! a non-trivial performance cost, especially around multiplication.
//!
//! Moduli like `2^64 - 1` strike an unusual balance: arithmetic modulo `2^64 - 1` can be performed
//! almost as efficiently as modulo `2^64`, typically at the cost of 1-3 additional instructions,
//! but their complex factorizations guarantee less predictable behavior than power-of-two moduli.
//!
//! [thue-morse]: https://en.wikipedia.org/wiki/Thue%E2%80%93Morse_sequence#Hash_collisions

#![no_std]

#[cfg(test)]
extern crate std;

use core::fmt::{Binary, Debug, Display, Formatter, LowerHex, Octal, UpperHex};
use core::hash::{Hash, Hasher};
use core::iter::{Product, Sum};
use core::ops::{
    Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Shl, ShlAssign, Shr, ShrAssign, Sub,
    SubAssign,
};

// The arithmetic logic needs to access many inherent methods on `uN` types, and making a common
// trait just to merge those definitions quickly gets unwieldy. Use macros instead.

macro_rules! define_binary_op {
    (
        impl <$ty:ty as $trait_name:ident>::$method_name:ident($a:ident, $b:ident) -> $out:ty
        [forwarding $assign_trait_name:ident::$assign_method_name:ident]
        $body:block
    ) => {
        impl $trait_name<&$ty> for &$ty {
            type Output = $out;

            #[inline]
            fn $method_name(self, other: &$ty) -> Self::Output {
                $trait_name::$method_name(*self, *other)
            }
        }

        impl $trait_name<&$ty> for $ty {
            type Output = $out;

            #[inline]
            fn $method_name(self, other: &$ty) -> Self::Output {
                $trait_name::$method_name(self, *other)
            }
        }

        impl $trait_name<$ty> for &$ty {
            type Output = $out;

            #[inline]
            fn $method_name(self, other: $ty) -> Self::Output {
                $trait_name::$method_name(*self, other)
            }
        }

        impl $trait_name for $ty {
            type Output = $out;

            #[inline]
            fn $method_name(self, other: $ty) -> Self::Output {
                let $a = self.value;
                let $b = other.value;
                $body
            }
        }

        impl $assign_trait_name<&$ty> for $ty {
            #[inline]
            fn $assign_method_name(&mut self, other: &$ty) {
                $assign_trait_name::$assign_method_name(self, *other);
            }
        }

        impl $assign_trait_name for $ty {
            #[inline]
            fn $assign_method_name(&mut self, other: $ty) {
                *self = $trait_name::$method_name(*self, other);
            }
        }
    };
}

macro_rules! define_shift_op {
    (
        @[$($shift_ty:ty),*]
        impl <$ty:ty as $trait_name:ident>::$method_name:ident($x:ident, $n:ident)
        [forwarding $assign_trait_name:ident::$assign_method_name:ident]
        $body:block
    ) => {
        $(
            impl $trait_name<&$shift_ty> for &$ty {
                type Output = $ty;

                #[inline]
                fn $method_name(self, n: &$shift_ty) -> Self::Output {
                    $trait_name::$method_name(*self, *n)
                }
            }

            impl $trait_name<&$shift_ty> for $ty {
                type Output = $ty;

                #[inline]
                fn $method_name(self, n: &$shift_ty) -> Self::Output {
                    $trait_name::$method_name(self, *n)
                }
            }

            impl $trait_name<$shift_ty> for &$ty {
                type Output = $ty;

                #[inline]
                fn $method_name(self, n: $shift_ty) -> Self::Output {
                    $trait_name::$method_name(*self, n)
                }
            }

            impl $trait_name<$shift_ty> for $ty {
                type Output = $ty;

                #[inline]
                fn $method_name(self, n: $shift_ty) -> Self::Output {
                    let $x = self.value;
                    let $n = n;
                    $body
                }
            }

            impl $assign_trait_name<&$shift_ty> for $ty {
                #[inline]
                fn $assign_method_name(&mut self, n: &$shift_ty) {
                    $assign_trait_name::$assign_method_name(self, *n);
                }
            }

            impl $assign_trait_name<$shift_ty> for $ty {
                #[inline]
                fn $assign_method_name(&mut self, n: $shift_ty) {
                    *self = $trait_name::$method_name(*self, n);
                }
            }
        )*
    };

    ($($tt:tt)*) => {
        define_shift_op!(@[u8, u16, u32, u64, usize, i8, i16, i32, i64, isize] $($tt)*);
    };
}

macro_rules! define_type {
    (#[$meta:meta] $ty:ident from $native:ident, carmichael = $carmichael:literal) => {
        #[$meta]
        ///
        /// This type implements most primitive operations:
        ///
        /// - `+`, `-` (both binary and unary), and `*` work straightforwardly.
        /// - [`inverse`](Self::inverse) computes the multiplicative inverse, if it exists.
        /// - `x / y` computes the product of `x` and the multiplicative inverse of `y`. If `y` does
        ///   is not coprime with `2^k - 1`, this operation panics. Note that computing inverses is
        ///   slow, so they should ideally computed once and then reused.
        /// - `pow` computes exponents of a value.
        /// - `<<` and `>>` correspond to multiplication by powers of two and division by powers of
        ///   two (i.e. multiplication by the multiplicative inverse).
        /// - `==` performs modular comparison.
        /// - [`Display`] and related traits print the remainder.
        ///
        /// Most combinations of operations are compiled as efficiently as possible. For example,
        /// you can efficiently check for invertability with `x.inverse().is_some()` without
        /// actually computing the inverse. A notable exception is comparison with a constant:
        /// prefer `x.is::<C>()` over `x == ModN::new(C)`.
        #[derive(Clone, Copy, Default)]
        pub struct $ty {
            /// Represents a zero remainder either as `0` or `T::MAX`, otherwise represents the
            /// remainder exactly.
            value: $native,
        }

        impl $ty {
            /// A constant `0` value.
            pub const ZERO: Self = Self { value: 0 };

            /// A constant `1` value.
            pub const ONE: Self = Self { value: 1 };

            const CARMICHAEL: u64 = $carmichael;

            /// Create a value corresponding to `x mod (2^k - 1)`.
            #[inline]
            pub const fn new(x: $native) -> Self {
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
            /// This is slightly more efficient than `x == C`. `C` must be a valid reminder, i.e.
            /// not be equal to `2^k - 1`.
            #[inline]
            pub const fn is<const C: $native>(self) -> bool {
                const {
                    assert!(C != $native::MAX, "constant out of bounds");
                }
                if C == 0 {
                    self.is_zero()
                } else {
                    self.value == C
                }
            }

            /// Compare for equality with zero.
            ///
            /// This is equialvent to `is::<0>()`.
            #[inline]
            pub const fn is_zero(self) -> bool {
                self.value == 0 || self.value == $native::MAX
            }

            /// Compute multiplicative inverse.
            ///
            /// Returns `None` if `x` is not coprime with `2^k - 1`.
            ///
            /// The current implementation uses the iterative binary extended Euclidian algorithm
            /// and works in `O(k)`.
            pub fn inverse(self) -> Option<Self> {
                let mut x = self.value;
                let mut y = $native::MAX;

                // Binary extended Euclidian algorithm a la https://eprint.iacr.org/2020/972.pdf
                // (Optimized Binary GCD for Modular Inversion, Thomas Pornin).
                //
                // At each step, `a_i x_i + b_i y_i = d`, where `d = (x, y)`.
                //
                // The values `a_1, b_1` are initially unknown. We only know that at the end,
                // `a_n = 0, b_n = 1`. As `x_i, y_i` are updated over the course of the algorithm,
                // we learn how `a_i, b_i` depends on `a_{i+1}, b_{i+1}`. The dependency is linear:
                //
                //     (a_i \\ b_i) = A_i * (a_{i+1} \\ b_{i+1})
                //     (a_1 \\ b_1) = A_1 * A_2 * ... * A_{n-1} * (0 \\ 1)
                //
                // Since we are only interested in `a`, we can compute
                //
                //     a_1 = (1 0) * A_1 * A_2 * ... * A_{n-1} * (0 \\ 1)
                //
                // and iteratively multiply the covector `(s t) = (1 0)` by matrices `A_i`.
                //
                // For binary Euclidian algorithm, `A_i` can contain division by powers of two, so
                // both `A_i` and `(s t)` are computed modulo `m`, since we're only interested in
                // `a mod m` anyway and dividing by two `mod m` is cheap.

                let mut s = Self::ONE;
                let mut t = Self::ZERO;

                // At the start of each iteration, `x` is non-zero and `y` is odd.
                while x != 0 {
                    let k = x.trailing_zeros();
                    x >>= k;
                    s >>= k;
                    if x < y {
                        core::mem::swap(&mut x, &mut y);
                        core::mem::swap(&mut s, &mut t);
                    }
                    x -= y;
                    s -= t;
                }

                (y == 1).then_some(t)
            }

            /// Compute `x^n mod m`.
            ///
            /// The current implementation uses iterative binary exponentiation, combining it with
            /// [the Carmichael function][1] to reduce exponents. It works in `O(log n)`.
            ///
            /// [1]: https://en.wikipedia.org/wiki/Carmichael_function#Exponential_cycle_length
            pub fn pow(self, n: u64) -> Self {
                // The existence of non-square-free Fermat numbers is an open problem, which means
                // we can assume `2^k - 1` is square-free for all reasonable data types. A property
                // of the Carmichael function guarantees
                //     a^(n + lambda(m)) = a^n  (mod m)
                // for *all* `a`, even those not coprime with `m`, as long as `n` >= the largest
                // exponent in factorization (i.e. 1), which almost always allows us to take `n`
                // modulo `lambda(m)`.
                if n == 0 {
                    return Self::ONE;
                }
                let new_n = if !Self::CARMICHAEL.is_power_of_two() && n <= Self::CARMICHAEL {
                    // Branching to avoid modulo is only useful for non-power-of-two moduli. LLVM
                    // can't infer that it's a no-op, so we enable it conditionally by hand.
                    n
                } else {
                    (n - 1) % Self::CARMICHAEL + 1
                };
                self.pow_internal(new_n)
            }

            // Used for tests.
            fn pow_internal(self, mut n: u64) -> Self {
                let mut res = Self::ONE;
                let mut tmp = self;
                while n > 0 {
                    // This line compiles to cmov. It's important to keep this branchless, because
                    // otherwise LLVM gets too smart for its own good and generated garbage [1].
                    // [1]: https://github.com/llvm/llvm-project/issues/171671
                    res *= if n % 2 == 1 { tmp } else { Self::ONE };
                    tmp *= tmp;
                    n /= 2;
                }
                res
            }
        }

        // Core logic.
        define_binary_op! {
            impl <$ty as Add>::add(a, b) -> $ty [forwarding AddAssign::add_assign] {
                let (sum, carry) = a.overflowing_add(b);
                Self::new(sum.wrapping_add(carry as $native))
            }
        }

        define_binary_op! {
            impl <$ty as Sub>::sub(a, b) -> $ty [forwarding SubAssign::sub_assign] {
                let (diff, borrow) = a.overflowing_sub(b);
                Self::new(diff.wrapping_sub(borrow as $native))
            }
        }

        define_binary_op! {
            impl <$ty as Mul>::mul(a, b) -> $ty [forwarding MulAssign::mul_assign] {
                let (low, high) = a.carrying_mul(b, 0);
                #[allow(clippy::suspicious_arithmetic_impl, reason = "2^k mod (2^k - 1) = 1")]
                {
                    Self::new(low) + Self::new(high)
                }
            }
        }

        define_binary_op! {
            impl <$ty as Div>::div(a, b) -> $ty [forwarding DivAssign::div_assign] {
                let b_inv = Self::new(b).inverse().expect("division by a non-invertible value");
                #[allow(clippy::suspicious_arithmetic_impl, reason = "multiplication by inverse")]
                {
                    Self::new(a) * b_inv
                }
            }
        }

        impl Neg for $ty {
            type Output = $ty;

            #[inline]
            fn neg(self) -> $ty {
                Self::new(!self.value)
            }
        }

        impl Neg for &$ty {
            type Output = $ty;

            #[inline]
            fn neg(self) -> $ty {
                -*self
            }
        }

        define_shift_op! {
            impl <$ty as Shl>::shl(x, n) [forwarding ShlAssign::shl_assign] {
                Self::new(x.rotate_left(n as u32))
            }
        }

        define_shift_op! {
            impl <$ty as Shr>::shr(x, n) [forwarding ShrAssign::shr_assign] {
                Self::new(x.rotate_right(n as u32))
            }
        }

        impl PartialEq for $ty {
            #[inline]
            fn eq(&self, other: &$ty) -> bool {
                let (diff, borrow) = self.value.overflowing_sub(other.value);
                let diff = diff.wrapping_sub(borrow as $native);
                // Optimize comparison against a constant. This still produces suboptimal results
                // (`sub + sbb + sete` instead of `cmp + sete`), but it's better than nothing.
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
        impl Eq for $ty {}

        impl Hash for $ty {
            fn hash<H: Hasher>(&self, state: &mut H) {
                self.remainder().hash(state)
            }
        }

        impl Debug for $ty {
            fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
                f.debug_tuple(stringify!($ty))
                    .field(&self.remainder())
                    .finish()
            }
        }

        impl Display for $ty {
            fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
                Display::fmt(&self.remainder(), f)
            }
        }

        impl Binary for $ty {
            fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
                Binary::fmt(&self.remainder(), f)
            }
        }

        impl Octal for $ty {
            fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
                Octal::fmt(&self.remainder(), f)
            }
        }

        impl LowerHex for $ty {
            fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
                LowerHex::fmt(&self.remainder(), f)
            }
        }

        impl UpperHex for $ty {
            fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
                UpperHex::fmt(&self.remainder(), f)
            }
        }

        impl Sum for $ty {
            fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
                iter.fold(Self::ZERO, |a, b| a + b)
            }
        }

        impl<'a> Sum<&'a $ty> for $ty {
            fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
                iter.copied().sum()
            }
        }

        impl Product for $ty {
            fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
                iter.fold(Self::ONE, |a, b| a * b)
            }
        }

        impl<'a> Product<&'a $ty> for $ty {
            fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
                iter.copied().product()
            }
        }
    };
}

define_type! {
    /// Arithmetic modulo `2^8 - 1 = 3 * 5 * 17`.
    Mod8 from u8, carmichael = 16
}

define_type! {
    /// Arithmetic modulo `2^16 - 1 = 3 * 5 * 17 * 257`.
    Mod16 from u16, carmichael = 256
}

define_type! {
    /// Arithmetic modulo `2^32 - 1 = 3 * 5 * 17 * 257 * 65537`.
    Mod32 from u32, carmichael = 65536
}

define_type! {
    /// Arithmetic modulo `2^64 - 1 = 3 * 5 * 17 * 257 * 641 * 65537 * 6700417`.
    Mod64 from u64, carmichael = 17153064960
}

#[cfg(test)]
mod tests {
    macro_rules! test_ty {
        ($ty:ident from $native:ident, signed $signed: ident) => {
            use crate::*;

            fn numbers() -> impl Iterator<Item = $ty> {
                // Range limited so that the product of two numbers fits in $signed for testing.
                (-11..=11).map(|x| $ty::new(x as $native))
            }

            fn to_signed(x: $ty) -> $signed {
                let x = x.to_raw() as $signed;
                if x < 0 { x + 1 } else { x }
            }

            fn from_signed(x: $signed) -> $ty {
                let x = if x < 0 { x.wrapping_sub(1) } else { x } as $native;
                $ty::new(x)
            }

            #[test]
            fn constants() {
                assert_eq!($ty::ZERO.to_raw(), 0);
                assert_eq!($ty::ONE.to_raw(), 1);
            }

            #[test]
            fn data() {
                for x in -10..10 {
                    let expected = if x == -1 { 0 } else { x } as $native;
                    assert_eq!($ty::new(x as $native).remainder(), expected);
                    assert_eq!($ty::new(x as $native).to_raw(), x as $native);
                }
            }

            #[test]
            fn arithmetic() {
                for x in numbers() {
                    for y in numbers() {
                        macro_rules! test_op {
                            ($op:tt, $op_assign:tt) => {
                                let expected = from_signed(to_signed(x) $op to_signed(y));
                                assert_eq!(x $op y, expected);
                                assert_eq!(&x $op y, expected);
                                assert_eq!(x $op &y, expected);
                                assert_eq!(&x $op &y, expected);
                                let mut x1 = x;
                                x1 $op_assign y;
                                assert_eq!(x1, expected);
                                x1 = x;
                                x1 $op_assign &y;
                                assert_eq!(x1, expected);
                            };
                        }

                        test_op!(+, +=);
                        test_op!(-, -=);
                        test_op!(*, *=);
                    }

                    assert_eq!(-x, from_signed(-to_signed(x)));
                    assert_eq!(-&x, from_signed(-to_signed(x)));
                }
            }

            #[test]
            fn shifts() {
                for x in numbers() {
                    for shift in 0..10.min($signed::BITS) {
                        let sx = to_signed(x);
                        if (sx << shift) >> shift != sx {
                            continue;
                        }
                        let expected = from_signed(sx << shift);

                        macro_rules! assert_for_shift_ty {
                            ($shift_ty:ty) => {
                                assert_eq!(x << shift as $shift_ty, expected);
                                assert_eq!(x >> (shift as $shift_ty).wrapping_neg(), expected);
                                assert_eq!(expected >> shift as $shift_ty, x);
                                assert_eq!(expected << (shift as $shift_ty).wrapping_neg(), x);
                            };
                        }

                        assert_for_shift_ty!(u8);
                        assert_for_shift_ty!(u16);
                        assert_for_shift_ty!(u32);
                        assert_for_shift_ty!(u64);
                        assert_for_shift_ty!(usize);
                        assert_for_shift_ty!(i8);
                        assert_for_shift_ty!(i16);
                        assert_for_shift_ty!(i32);
                        assert_for_shift_ty!(i64);
                        assert_for_shift_ty!(isize);
                    }

                    // Large powers of two.
                    let mut tmp = x;
                    for _ in 0..100 {
                        tmp += tmp;
                    }
                    assert_eq!(tmp, x << 100);
                    assert_eq!(tmp >> 100, x);
                }
            }

            #[test]
            fn equality() {
                for x in numbers() {
                    for y in numbers() {
                        assert_eq!(x == y, to_signed(x) == to_signed(y));
                    }
                }

                for x in numbers() {
                    let sx = to_signed(x);
                    assert_eq!(x.is_zero(), sx == 0);
                    assert_eq!(x.is::<0>(), sx == 0);
                    assert_eq!(x.is::<{ $native::MAX - 1 }>(), sx == -1);
                    assert_eq!(x.is::<5>(), sx == 5);
                }

                fn _impls_eq(x: $ty) -> impl Eq {
                    x
                }
            }

            #[test]
            fn iterators() {
                assert_eq!(
                    [1, 2, 3, 4].into_iter().map($ty::new).sum::<$ty>(),
                    $ty::new(10),
                );
                assert_eq!(
                    [1, 2, 3, 4].into_iter().map($ty::new).product::<$ty>(),
                    $ty::new(24),
                );
            }

            #[test]
            fn hash() {
                let hash = |x: $native| -> u64 {
                    let mut state = std::hash::DefaultHasher::new();
                    $ty::new(x).hash(&mut state);
                    state.finish()
                };

                assert_ne!(hash(5), hash(15));
                assert_ne!(hash(0), hash(15));
                assert_eq!(hash(0), hash($native::MAX));
            }

            #[test]
            fn formatting() {
                use std::format;
                use std::string::ToString;

                for x in numbers() {
                    assert_eq!(x.to_string(), x.remainder().to_string());
                    assert_eq!(format!("{x:b}"), format!("{:b}", x.remainder()));
                    assert_eq!(format!("{x:#b}"), format!("{:#b}", x.remainder()));
                    assert_eq!(format!("{x:o}"), format!("{:o}", x.remainder()));
                    assert_eq!(format!("{x:#o}"), format!("{:#o}", x.remainder()));
                    assert_eq!(format!("{x:x}"), format!("{:x}", x.remainder()));
                    assert_eq!(format!("{x:#x}"), format!("{:#x}", x.remainder()));
                    assert_eq!(format!("{x:X}"), format!("{:X}", x.remainder()));
                    assert_eq!(format!("{x:#X}"), format!("{:#X}", x.remainder()));
                    assert_eq!(
                        format!("{:?}", x),
                        format!("{}({})", stringify!($ty), x.remainder()),
                    );
                }
            }

            fn has_common_divisor(x: $native, y: $native) -> bool {
                (2..).find(|d| x % d == 0 && y % d == 0).is_some()
            }

            #[test]
            fn inverse() {
                for x in numbers() {
                    if let Some(y) = x.inverse() {
                        assert_eq!(x * y, $ty::ONE);
                    } else {
                        assert!(has_common_divisor(x.to_raw(), $native::MAX));
                    }
                }
            }

            #[test]
            fn division() {
                for x in numbers() {
                    for y in numbers() {
                        if y.inverse().is_some() {
                            assert_eq!(x / y * y, x);
                        }
                    }
                }
            }

            #[test]
            #[should_panic]
            fn division_by_non_invertible() {
                let _ = $ty::new(5) / $ty::new(5);
            }

            #[test]
            fn power() {
                for x in numbers() {
                    let mut expected = $ty::ONE;
                    for n in 0..10 {
                        assert_eq!(x.pow(n), expected);
                        assert_eq!(x.pow($ty::CARMICHAEL + n), x.pow_internal($ty::CARMICHAEL + n));
                        expected *= x;
                    }
                }
            }

            #[test]
            fn carmichael() {
                for x in numbers() {
                    if x.inverse().is_some() {
                        assert!(x.pow_internal($ty::CARMICHAEL).is::<1>());
                    }
                }
            }
        };
    }

    mod test8 {
        test_ty!(Mod8 from u8, signed i8);
    }

    mod test16 {
        test_ty!(Mod16 from u16, signed i16);
    }

    mod test32 {
        test_ty!(Mod32 from u32, signed i32);
    }

    mod test64 {
        test_ty!(Mod64 from u64, signed i64);
    }
}

#[allow(dead_code, reason = "ad-hoc compile-fail test")]
/// ```compile_fail
/// Mod8::new(0).is::<u8::MAX>();
/// ```
///
/// ```compile_fail
/// Mod16::new(0).is::<u16::MAX>();
/// ```
///
/// ```compile_fail
/// Mod32::new(0).is::<u32::MAX>();
/// ```
///
/// ```compile_fail
/// Mod64::new(0).is::<u64::MAX>();
/// ```
fn test_is() {}
