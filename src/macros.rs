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
        fn raw_numbers() -> impl Iterator<Item = $native> {
            let edge_cases = (-5i32..=5).map(|x| x as $native);

            let mut rng = fastrand::Rng::new();
            let random_data = (0..50).map(move |_| rng.u64(..) as $native);

            edge_cases.chain(random_data)
        }

        fn numbers() -> impl Iterator<Item = $ty> {
            raw_numbers().map($ty::new)
        }

        fn assert_remainder(x: $ty, expected: u128) {
            let modulus = if $ty::MODULUS == 0 {
                $native::MAX as u128 + 1
            } else {
                $ty::MODULUS as u128
            };
            assert_eq!(x.remainder(), (expected % modulus) as $native);
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
            for x in raw_numbers() {
                let expected = if $ty::MODULUS == 0 {
                    x
                } else {
                    x % $ty::MODULUS
                };
                assert_eq!($ty::new(x).remainder(), expected);
            }
        }

        #[test]
        fn arithmetic() {
            for x in numbers() {
                assert_remainder(-x, $ty::MODULUS.wrapping_sub(x.remainder()) as u128);
                assert_remainder(-&x, $ty::MODULUS.wrapping_sub(x.remainder()) as u128);
            }

            for x in numbers() {
                for y in numbers() {
                    macro_rules! test_op {
                        ($op:tt, $op_assign:tt, $expected:expr) => {{
                            let expected = $expected;
                            assert_remainder(x $op y, expected);
                            assert_remainder(&x $op y, expected);
                            assert_remainder(x $op &y, expected);
                            assert_remainder(&x $op &y, expected);
                            let mut x1 = x;
                            x1 $op_assign y;
                            assert_remainder(x1, expected);
                            x1 = x;
                            x1 $op_assign &y;
                            assert_remainder(x1, expected);
                        }};
                    }
                    test_op!(+, +=, x.remainder() as u128 + y.remainder() as u128);
                    test_op!(-, -=, x.remainder() as u128 + (-y).remainder() as u128);
                    test_op!(*, *=, x.remainder() as u128 * y.remainder() as u128);
                }
            }
        }

        #[test]
        fn shifts() {
            for x in numbers() {
                for shift in 0..=64 {
                    let expected = (x.remainder() as u128) << shift;

                    macro_rules! assert_for_shift_ty {
                        ($shift_ty:ty) => {
                            assert_remainder(x << shift as $shift_ty, expected);
                            #[cfg($shr)]
                            assert_eq!((x << shift as $shift_ty) >> shift as $shift_ty, x);
                        };
                        (signed $shift_ty:ty) => {
                            assert_for_shift_ty!($shift_ty);
                            #[cfg($shr)]
                            assert_remainder(x >> -(shift as $shift_ty), expected);
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
                    assert_eq!(x == y, x.remainder() == y.remainder());
                }
            }

            for x in numbers() {
                const MAX: $native = $ty::MODULUS.wrapping_sub(1);
                let r = x.remainder();
                assert_eq!(x.is_zero(), r == 0);
                assert_eq!(x.is::<0>(), r == 0);
                assert_eq!(x.is::<{ MAX as u64 }>(), r == MAX as $native);
                assert_eq!(x.is::<5>(), r == 5);
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
                    assert!(has_common_divisor(
                        x.to_raw(),
                        if $ty::MODULUS == 0 { 2 } else { $ty::MODULUS }
                    ));
                }
            }
        }

        #[test]
        fn division() {
            for y in numbers() {
                if y.is_invertible() {
                    for x in numbers() {
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
                    assert_eq!(
                        x.pow($ty::CARMICHAEL + n),
                        x.pow_internal($ty::CARMICHAEL + n, $ty::ONE),
                    );
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
