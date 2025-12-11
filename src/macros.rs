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

macro_rules! define_type_basics {
    ($ty:ident as $native:ident) => {
        impl $ty {
            /// A constant `0` value.
            pub const ZERO: Self = Self { value: 0 };

            /// A constant `1` value.
            pub const ONE: Self = Self { value: 1 };

            /// Compute multiplicative inverse.
            ///
            /// Returns `None` if `x` is not coprime with `2^k - 1`.
            ///
            /// The current implementation uses the iterative binary extended Euclidian algorithm
            /// and works in `O(k)`.
            pub fn inverse(self) -> Option<Self> {
                if self.value == 0 {
                    return None;
                }

                let mut x = self.value;
                let mut y = Self::MODULUS;

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
                    // Teach the optimizer that `k` is small.
                    // SAFETY: Initially, `max(x, y) <= MODULUS`. Each iteration can only reduce
                    // the maximum.
                    unsafe {
                        core::hint::assert_unchecked(x <= $ty::MODULUS);
                    }
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

                let is_invertible = Self::IS_PRIME || y == 1;
                is_invertible.then_some(t)
            }

            // Shared among fast and prime moduli.
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
    ($ty:ident as $native:ident, $signed: ident) => {
        fn numbers() -> impl Iterator<Item = $ty> {
            // Range limited so that the product of two numbers fits in $signed for testing.
            (-11..=11).map(|x| $ty::new(x as $native))
        }

        fn to_signed(x: $ty) -> $signed {
            let x = x.to_raw();
            if x <= $ty::MODULUS / 2 {
                x as $signed
            } else {
                x.wrapping_sub($ty::MODULUS) as $signed
            }
        }

        fn from_signed(x: $signed) -> $ty {
            $ty::new((x as i128).rem_euclid($ty::MODULUS as i128) as $native)
        }

        #[test]
        fn constants() {
            assert_eq!($ty::ZERO.to_raw(), 0);
            assert_eq!($ty::ONE.to_raw(), 1);
        }

        #[test]
        fn constructors() {
            assert_eq!($ty::new(5).remainder(), 5);
            assert_eq!(unsafe { $ty::from_remainder_unchecked(5) }.remainder(), 5);
        }

        #[test]
        fn remainder() {
            for x in -10..10 {
                let x = x as $native;
                assert_eq!($ty::new(x).remainder(), x % $ty::MODULUS);
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
                            assert_eq!(expected >> shift as $shift_ty, x);
                        };
                        (signed $shift_ty:ty) => {
                            assert_for_shift_ty!($shift_ty);
                            assert_eq!(x >> -(shift as $shift_ty), expected);
                            assert_eq!(expected << -(shift as $shift_ty), x);
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
                    assert_eq!(tmp >> n, x);
                    tmp += tmp;
                }
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
                assert_eq!(x.is::<{ $ty::MODULUS - 1 }>(), sx == -1);
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
            // Textbook Euclidian algorithm.
            while x != 0 && y != 0 {
                x %= y;
                core::mem::swap(&mut x, &mut y);
            }
            x + y != 1
        }

        #[test]
        fn inverse() {
            for x in numbers() {
                if let Some(y) = x.inverse() {
                    assert!(x.is_invertible());
                    assert_eq!(x * y, $ty::ONE);
                } else {
                    assert!(!x.is_invertible());
                    assert!(has_common_divisor(x.to_raw(), $ty::MODULUS));
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
            if $ty::MODULUS % 5 == 0 {
                let _ = $ty::new(5) / $ty::new(5);
            }
            let _ = $ty::new(1) / $ty::new(0);
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
                if x.is_invertible() {
                    assert!(x.pow_internal($ty::CARMICHAEL).is::<1>());
                }
            }
        }
    };
}

#[cfg(test)]
pub(crate) use test_ty;
