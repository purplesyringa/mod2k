// The arithmetic logic needs to access many inherent methods on `uN` types, and making a common
// trait just to merge those definitions quickly gets unwieldy. Use macros instead.

macro_rules! forward_binary_op {
    (
        $ty:ty,
        $trait:ident::$method_name:ident,
        $assign_trait:ident::$assign_method_name:ident
    ) => {
        impl core::ops::$trait<&$ty> for &$ty {
            type Output = $ty;

            #[inline]
            fn $method_name(self, other: &$ty) -> $ty {
                core::ops::$trait::$method_name(*self, *other)
            }
        }

        impl core::ops::$trait<&$ty> for $ty {
            type Output = $ty;

            #[inline]
            fn $method_name(self, other: &$ty) -> $ty {
                core::ops::$trait::$method_name(self, *other)
            }
        }

        impl core::ops::$trait<$ty> for &$ty {
            type Output = $ty;

            #[inline]
            fn $method_name(self, other: $ty) -> $ty {
                core::ops::$trait::$method_name(*self, other)
            }
        }

        impl core::ops::$assign_trait<&$ty> for $ty {
            #[inline]
            fn $assign_method_name(&mut self, other: &$ty) {
                core::ops::$assign_trait::$assign_method_name(self, *other);
            }
        }

        impl core::ops::$assign_trait for $ty {
            #[inline]
            fn $assign_method_name(&mut self, other: $ty) {
                *self = core::ops::$trait::$method_name(*self, other);
            }
        }
    };
}
pub(crate) use forward_binary_op;

macro_rules! forward_shift_op {
    (
        $shift_ty:ty $(as $shift_ty_via:ty)?,
        $ty:ty,
        $trait:ident::$method_name:ident,
        $assign_trait:ident::$assign_method_name:ident
    ) => {
        impl core::ops::$trait<&$shift_ty> for &$ty {
            type Output = $ty;

            #[inline]
            fn $method_name(self, n: &$shift_ty) -> Self::Output {
                core::ops::$trait::$method_name(*self, *n)
            }
        }

        impl core::ops::$trait<&$shift_ty> for $ty {
            type Output = $ty;

            #[inline]
            fn $method_name(self, n: &$shift_ty) -> Self::Output {
                core::ops::$trait::$method_name(self, *n)
            }
        }

        impl core::ops::$trait<$shift_ty> for &$ty {
            type Output = $ty;

            #[inline]
            fn $method_name(self, n: $shift_ty) -> Self::Output {
                core::ops::$trait::$method_name(*self, n)
            }
        }

        $(
            impl core::ops::$trait<$shift_ty> for $ty {
                type Output = $ty;

                #[inline]
                fn $method_name(self, n: $shift_ty) -> Self::Output {
                    core::ops::$trait::$method_name(self, n as $shift_ty_via)
                }
            }
        )?

        impl core::ops::$assign_trait<&$shift_ty> for $ty {
            #[inline]
            fn $assign_method_name(&mut self, n: &$shift_ty) {
                core::ops::$assign_trait::$assign_method_name(self, *n);
            }
        }

        impl core::ops::$assign_trait<$shift_ty> for $ty {
            #[inline]
            fn $assign_method_name(&mut self, n: $shift_ty) {
                *self = core::ops::$trait::$method_name(*self, n);
            }
        }
    };

    ($($tt:tt)*) => {
        $crate::macros::forward_shift_op!(u8 as u64, $($tt)*);
        $crate::macros::forward_shift_op!(u16 as u64, $($tt)*);
        $crate::macros::forward_shift_op!(u32 as u64, $($tt)*);
        $crate::macros::forward_shift_op!(u64, $($tt)*);
        $crate::macros::forward_shift_op!(usize as u64, $($tt)*);
        $crate::macros::forward_shift_op!(i8 as i64, $($tt)*);
        $crate::macros::forward_shift_op!(i16 as i64, $($tt)*);
        $crate::macros::forward_shift_op!(i32 as i64, $($tt)*);
        $crate::macros::forward_shift_op!(i64, $($tt)*);
        $crate::macros::forward_shift_op!(isize as i64, $($tt)*);
    };
}
pub(crate) use forward_shift_op;

macro_rules! define_exgcd_inverse {
    (
        prime = $prime:literal,
        limited_value = $limited_value:literal,
        fast_shr = $fast_shr:literal
    ) => {
        fn inverse(self) -> Option<Self> {
            // `$limited_value` indicates `value <= MODULUS`.
            let mut x = if $limited_value {
                self.value
            } else {
                self.remainder()
            };
            let mut y = Self::MODULUS;

            let is_zero = if $limited_value {
                self.is_zero()
            } else {
                x == 0
            };
            if is_zero {
                return None;
            }

            // Binary extended Euclidean algorithm a la https://eprint.iacr.org/2020/972.pdf
            // (Optimized Binary GCD for Modular Inversion, Thomas Pornin).
            //
            // At each step, `a_i x_i + b_i y_i = d`, where `d = (x, y)`.
            //
            // The values `a_1, b_1` are initially unknown. We only know that at the end,
            // `a_n = 0, b_n = 1`. As `x_i, y_i` are updated over the course of the algorithm,  we
            // learn how `a_i, b_i` depends on `a_{i+1}, b_{i+1}`. The dependency is linear:
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
            // For binary Euclidean algorithm, `A_i` can contain division by powers of two, so both
            // `A_i` and `(s t)` are computed modulo `m`, since we're only interested in `a mod m`
            // anyway and dividing by two `mod m` is usually cheap.
            //
            // The structure of binary GCD is taken from:
            // - https://en.algorithmica.org/hpc/algorithms/gcd/
            // - https://lemire.me/blog/2024/04/13/greatest-common-divisor-the-extended-euclidean-algorithm-and-speed/

            let mut s = Self::ONE;
            let mut t = Self::ZERO;
            let mut total_k = 0;

            // At the start of each iteration, `x` is non-zero and `y` is odd.
            let mut k = x.trailing_zeros();
            while x != 0 {
                // Teach the optimizer that `k` is small.
                // SAFETY: Initially, `max(x, y) <= MODULUS`. Each iteration can only reduce the
                // maximum. Thus, `2^k <= x <= MODULUS`.
                unsafe {
                    core::hint::assert_unchecked(k <= Self::MODULUS.ilog2());
                }
                x >>= k;
                if $fast_shr {
                    s >>= k;
                } else {
                    // Will shift right once at the end. Has suboptimal codegen due to [1].
                    // [1]: https://github.com/llvm/llvm-project/issues/172097
                    total_k += k;
                    t <<= k;
                }

                // (x, y) -> (|x - y|, min(x, y))
                let diff_xy = x.wrapping_sub(y);
                k = diff_xy.trailing_zeros(); // `|x - y|` has the same ctz as `x - y`
                (x, y, s, t) = core::hint::select_unpredictable(
                    x < y,
                    (diff_xy.wrapping_neg(), x, t, s),
                    (diff_xy, y, s, t),
                );
                s -= t;
            }

            if !$fast_shr {
                t >>= total_k;
            }

            // We have previously asserted `!is_zero`, and all non-zero values are invertible modulo
            // prime.
            let is_invertible = $prime || y == 1;
            is_invertible.then_some(t)
        }
    };
}
pub(crate) use define_exgcd_inverse;

macro_rules! define_type_basics {
    (#[$meta:meta] $ty:ident as $native:ident, shr = $shr:tt) => {
        #[$meta]
        ///
        /// This type does not have any inherent methods. Use the [`Mod`] trait to access its
        /// features.
        ///
        /// See [module-level documentation](self) for more information.
        #[derive(Clone, Copy, Default)]
        pub struct $ty {
            value: $native,
        }

        impl $ty {
            fn pow_internal(self, mut n: u64, coproduct: Self) -> Self {
                let mut res = coproduct;
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

        $crate::macros::forward_binary_op!($ty, Add::add, AddAssign::add_assign);
        $crate::macros::forward_binary_op!($ty, Sub::sub, SubAssign::sub_assign);
        $crate::macros::forward_binary_op!($ty, Mul::mul, MulAssign::mul_assign);
        $crate::macros::forward_binary_op!($ty, Div::div, DivAssign::div_assign);

        impl core::ops::Div for $ty {
            type Output = Self;

            #[inline]
            #[allow(
                clippy::suspicious_arithmetic_impl,
                reason = "multiplication by inverse"
            )]
            fn div(self, other: Self) -> Self {
                self * other.inverse().expect("division by a non-invertible value")
            }
        }

        impl core::ops::Neg for &$ty {
            type Output = $ty;

            #[inline]
            fn neg(self) -> $ty {
                -*self
            }
        }

        $crate::macros::forward_shift_op!($ty, Shl::shl, ShlAssign::shl_assign);

        #[cfg($shr)]
        $crate::macros::forward_shift_op!($ty, Shr::shr, ShrAssign::shr_assign);

        impl Eq for $ty {}

        impl core::hash::Hash for $ty {
            fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
                self.remainder().hash(state)
            }
        }

        impl core::fmt::Debug for $ty {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                f.debug_tuple(stringify!($ty))
                    .field(&self.remainder())
                    .finish()
            }
        }

        impl core::fmt::Display for $ty {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                core::fmt::Display::fmt(&self.remainder(), f)
            }
        }

        impl core::fmt::Binary for $ty {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                core::fmt::Binary::fmt(&self.remainder(), f)
            }
        }

        impl core::fmt::Octal for $ty {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                core::fmt::Octal::fmt(&self.remainder(), f)
            }
        }

        impl core::fmt::LowerHex for $ty {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                core::fmt::LowerHex::fmt(&self.remainder(), f)
            }
        }

        impl core::fmt::UpperHex for $ty {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                core::fmt::UpperHex::fmt(&self.remainder(), f)
            }
        }

        impl core::iter::Sum for $ty {
            fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
                iter.fold(Self::ZERO, |a, b| a + b)
            }
        }

        impl<'a> core::iter::Sum<&'a $ty> for $ty {
            fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
                iter.copied().sum()
            }
        }

        impl core::iter::Product for $ty {
            fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
                iter.fold(Self::ONE, |a, b| a * b)
            }
        }

        impl<'a> core::iter::Product<&'a $ty> for $ty {
            fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
                iter.copied().product()
            }
        }
    };
}
pub(crate) use define_type_basics;

#[cfg(test)]
macro_rules! test_ty {
    ($ty:ident as $native:ident, $signed:ident, shr = $shr:tt) => {
        fn numbers() -> impl Iterator<Item = $ty> {
            // Range limited so that the product of two numbers fits in $signed for testing.
            (-11..=11).map(|x| $ty::new(x as $native))
        }

        fn to_signed(x: $ty) -> $signed {
            let x = x.to_raw();
            if x <= $ty::MODULUS.wrapping_sub(1) / 2 {
                x as $signed
            } else {
                x.wrapping_sub($ty::MODULUS) as $signed
            }
        }

        fn from_signed(x: $signed) -> $ty {
            if $ty::MODULUS == 0 {
                // Full power-of-two modulus
                $ty::new(x as $native)
            } else {
                $ty::new((x as i128).rem_euclid($ty::MODULUS as i128) as $native)
            }
        }

        #[test]
        fn constants() {
            assert_eq!($ty::ZERO.to_raw(), 0);
            assert_eq!($ty::ONE.to_raw(), 1);
        }

        #[test]
        fn constructors() {
            assert_eq!($ty::new(5).remainder(), 5);
            assert_eq!(unsafe { $ty::new_unchecked(5) }.remainder(), 5);
        }

        #[test]
        fn remainder() {
            for x in -10..10 {
                let mut x = x as $native;
                if $ty::MODULUS != 0 {
                    x %= $ty::MODULUS;
                }
                assert_eq!($ty::new(x).remainder(), x);
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
                            #[cfg($shr)]
                            assert_eq!(expected >> shift as $shift_ty, x);
                        };
                        (signed $shift_ty:ty) => {
                            assert_for_shift_ty!($shift_ty);
                            #[cfg($shr)]
                            {
                                assert_eq!(x >> -(shift as $shift_ty), expected);
                                assert_eq!(expected << -(shift as $shift_ty), x);
                            }
                        };
                    }

                    assert_for_shift_ty!(u8);
                    assert_for_shift_ty!(u16);
                    assert_for_shift_ty!(u32);
                    assert_for_shift_ty!(u64);
                    assert_for_shift_ty!(usize);
                    assert_for_shift_ty!(signed i8);
                    assert_for_shift_ty!(signed i16);
                    assert_for_shift_ty!(signed i32);
                    assert_for_shift_ty!(signed i64);
                    assert_for_shift_ty!(signed isize);
                }

                // Large powers of two.
                let mut tmp = x;
                for n in 0..100 {
                    assert_eq!(tmp, x << n);
                    #[cfg($shr)]
                    assert_eq!(tmp >> n, x);
                    tmp += tmp;
                }
            }
        }

        #[cfg(not($shr))]
        #[test]
        #[should_panic]
        fn negative_shl() {
            let _ = $ty::ZERO << -1;
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
                assert_eq!(x.is::<{ $ty::MODULUS.wrapping_sub(1) as u64 }>(), sx == -1);
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
                use std::hash::{DefaultHasher, Hash, Hasher};
                let mut state = DefaultHasher::new();
                $ty::new(x).hash(&mut state);
                state.finish()
            };

            assert_ne!(hash(5), hash(15));
            assert_ne!(hash(0), hash(15));
            assert_eq!(hash(0), hash($ty::MODULUS));
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

        fn has_common_divisor(mut x: $native, mut y: $native) -> bool {
            // Textbook Euclidean algorithm.
            while x != 0 && y != 0 {
                x %= y;
                core::mem::swap(&mut x, &mut y);
            }
            x + y != 1
        }

        #[test]
        fn inverse() {
            assert!(!$ty::ZERO.is_invertible());
            assert!($ty::ZERO.inverse().is_none());

            assert!(!$ty::new($ty::MODULUS).is_invertible());
            assert!($ty::new($ty::MODULUS).inverse().is_none());

            for x in numbers() {
                if let Some(y) = x.inverse() {
                    assert!(x.is_invertible());
                    assert_eq!(x * y, $ty::ONE);
                } else {
                    assert!(!x.is_invertible());
                    assert!(has_common_divisor(x.to_raw(), if $ty::MODULUS == 0 { 2 } else { $ty::MODULUS }));
                }
            }
        }

        #[test]
        fn division() {
            for x in numbers() {
                for y in numbers() {
                    if y.is_invertible() {
                        assert_eq!(x / y * y, x);
                    }
                }
            }
        }

        #[test]
        #[should_panic]
        fn division_by_non_invertible() {
            assert!($ty::MODULUS != 0 && $ty::MODULUS % 5 == 0);
            let _ = $ty::new(5) / $ty::new(5);
        }

        #[test]
        #[should_panic]
        fn division_by_zero() {
            let _ = $ty::new(1) / $ty::new(0);
        }

        #[test]
        fn power() {
            for x in numbers() {
                let mut expected = $ty::ONE;
                for n in 0..10 {
                    assert_eq!(x.pow(n), expected);
                    assert_eq!(x.pow($ty::CARMICHAEL + n), x.pow_internal($ty::CARMICHAEL + n, $ty::ONE));
                    expected *= x;
                }
            }
        }

        #[test]
        fn carmichael() {
            for x in numbers() {
                if x.is_invertible() {
                    assert!(x.pow_internal($ty::CARMICHAEL, $ty::ONE).is::<1>());
                }
            }
        }
    };
}

#[cfg(test)]
pub(crate) use test_ty;

#[cfg(test)]
macro_rules! test_exact_raw {
    ($ty:ident as $native:ident) => {
        #[test]
        fn raw() {
            for x in -10..10 {
                assert_eq!($ty::new(x as $native).to_raw(), x as $native);
            }
        }
    };
}

#[cfg(test)]
pub(crate) use test_exact_raw;
