//! Explicit numeric type conversion.

/// Blanket trait that imports all traits in this crate.
///
/// Improves syntax ergonomics by allowing the syntax `foo.bar::<T>()`.
pub trait Xias {
    /// Convert between signed and unsigned types of the same integer,
    /// assuming that the value is homogeneous over the conversion.
    ///
    /// # Panics
    /// Panics if the value is out of range after conversion.
    fn homosign<T>(self) -> T
    where
        Self: Homosign<T>,
    {
        Homosign::homosign(self)
    }

    /// Downscale the precision of a floating point value.
    ///
    /// # Panics
    /// Panics if the value is infinite after conversion.
    fn lossy_float<T>(self) -> T
    where
        Self: LossyFloat<T>,
    {
        LossyFloat::lossy_float(self)
    }

    /// Reduce the size of an integer,
    /// assuming that the value is within the range of the new type.
    ///
    /// # Panics
    /// Panics if the value is out of range after conversion.
    fn small_int<T>(self) -> T
    where
        Self: SmallInt<T>,
    {
        SmallInt::small_int(self)
    }

    /// Converts an integer to a floating point value,
    /// assuming that the value can be losslessly represented in the new type.
    ///
    /// # Panics
    /// Panics if the value is infinite after conversion.
    fn small_float<T>(self) -> T
    where
        Self: SmallFloat<T>,
    {
        SmallFloat::small_float(self)
    }

    /// Converts a floating point value to an integer
    /// by calling the [`f32::trunc`]/[`f64::trunc`] method.
    ///
    /// # Panics
    /// Panics if the truncated integer is not in the range of the output type.
    fn trunc_int<T>(self) -> T
    where
        Self: TruncInt<T>,
    {
        TruncInt::trunc_int(self)
    }
}

macro_rules! impl_xias {
    ($($t:ty)*) => {
        $(
            impl Xias for $t {}
        )*
    }
}

impl_xias! {
    u8 u16 u32 u64 u128 usize
    i8 i16 i32 i64 i128 isize
    f32 f64
}

/// See [`Xias::homosign`].
pub trait Homosign<T>: Sized {
    /// See [`Xias::homosign`].
    fn homosign(self) -> T;
}

macro_rules! impl_homosign {
    ($unsigned:ty, $signed:ty) => {
        impl Homosign<$signed> for $unsigned {
            fn homosign(self) -> $signed {
                debug_assert!(
                    self <= <$unsigned>::MAX / 2,
                    "{:?} is not homogeneous over signs",
                    self
                );

                self as $signed
            }
        }

        impl Homosign<$unsigned> for $signed {
            fn homosign(self) -> $unsigned {
                debug_assert!(self >= 0, "{:?} is not homogeneous over signs", self);

                self as $unsigned
            }
        }
    };
}

impl_homosign!(u8, i8);
impl_homosign!(u16, i16);
impl_homosign!(u32, i32);
impl_homosign!(u64, i64);
impl_homosign!(u128, i128);
impl_homosign!(usize, isize);

/// See [`Xias::lossy_float`].
pub trait LossyFloat<T>: Sized {
    /// See [`Xias::lossy_float`].
    fn lossy_float(self) -> T;
}

impl LossyFloat<f32> for f64 {
    fn lossy_float(self) -> f32 {
        debug_assert!(
            self <= f32::MAX.into(),
            "{:?} will become infinite in f32",
            self
        );
        debug_assert!(
            self >= f32::MIN.into(),
            "{:?} will become infinite in f32",
            self
        );

        self as f32
    }
}

/// See [`Xias::small_int`].
pub trait SmallInt<T>: Sized {
    /// See [`Xias::small_int`].
    fn small_int(self) -> T;
}

macro_rules! impl_small_int {
    ($from:ty; $($to:ty),*) => {
        $(
            impl SmallInt<$to> for $from {
                fn small_int(self) -> $to {
                    debug_assert!(self >= <$to>::MIN as $from, "{:?} is too small to fit into {}", self, stringify!($to));
                    debug_assert!(self <= <$to>::MAX as $from, "{:?} is too large to fit into {}", self, stringify!($to));

                    self as $to
                }
            }
        )*
    };
}

impl_small_int!(u8; u8, usize);
impl_small_int!(u16; u8, usize);
impl_small_int!(u32; u16, u8, usize);
impl_small_int!(u64; u32, u16, u8, usize);
impl_small_int!(u128; u64, u32, u16, u8, usize);
impl_small_int!(usize; u128, u64, u32, u16, u8);

impl_small_int!(i8; isize);
impl_small_int!(i16; i8, isize);
impl_small_int!(i32; i16, i8, isize);
impl_small_int!(i64; i32, i16, i8, isize);
impl_small_int!(i128; i64, i32, i16, i8, isize);
impl_small_int!(isize; i128, i64, i32, i16, i8);

/// See [`Xias::small_float`].
pub trait SmallFloat<T>: Sized {
    /// See [`Xias::small_float`].
    fn small_float(self) -> T;
}

macro_rules! impl_small_float_unsigned {
    ($($from:ty),*; $to:ty) => {
        $(
            impl SmallFloat<$to> for $from {
                fn small_float(self) -> $to {
                    debug_assert!({
                        let float_size = <$to>::MANTISSA_DIGITS;
                        let int_size = <$from>::BITS - self.leading_zeros();
                        float_size >= int_size
                    }, "{:?} cannot fit into {}", self, stringify!($to));

                    self as $to
                }
            }
        )*
    };
}

impl_small_float_unsigned!(u8, u16, u32, u64, u128, usize; f32);
impl_small_float_unsigned!(u8, u16, u32, u64, u128, usize; f64);

macro_rules! impl_small_float_signed {
    ($($from:ty),*; $to:ty) => {
        $(
            impl SmallFloat<$to> for $from {
                fn small_float(self) -> $to {
                    debug_assert!({
                        let float_size = <$to>::MANTISSA_DIGITS;
                        let int_size = if self == <$from>::min_value() {
                            <$from>::BITS - 1
                        } else {
                            <$from>::BITS - self.leading_zeros()
                        };
                        float_size >= int_size
                    }, "{:?} cannot fit into {}", self, stringify!($to));

                    self as $to
                }
            }
        )*
    };
}

impl_small_float_signed!(i8, i16, i32, i64, i128, isize; f32);
impl_small_float_signed!(i8, i16, i32, i64, i128, isize; f64);

/// See [`Xias::trunc_int`].
pub trait TruncInt<T>: Sized {
    /// See [`Xias::trunc_int`].
    fn trunc_int(self) -> T;
}

macro_rules! impl_trunc_int {
    ($float:ty; $($int:ty),*) => {
        $(
            impl TruncInt<$int> for $float {
                fn trunc_int(self) -> $int {
                    debug_assert!(self.is_finite(), "Cannot convert a non-finite float ({:?}) to {}", self, stringify!($int));
                    let float = self.trunc();
                    debug_assert!(<$int>::MIN as $float <= float, "{:?} is too small to fit into {}", self, stringify!($int));
                    debug_assert!(<$int>::MAX as $float >= float, "{:?} is too large to fit into {}", self, stringify!($int));
                    float as $int
                }
            }
        )*
    }
}

impl_trunc_int! {
    f32;
    u8, u16, u32, u64, u128, usize,
    i8, i16, i32, i64, i128, isize
}
impl_trunc_int! {
    f64;
    u8, u16, u32, u64, u128, usize,
    i8, i16, i32, i64, i128, isize
}

#[cfg(all(test, debug_assertions))]
mod tests {
    use paste::paste;

    use super::Xias;

    // homosign tests

    macro_rules! test_homosign {
        ($signed:ty, $unsigned:ty) => {
            paste! {
                #[test]
                fn [<test_homosign_zero_ $signed _ $unsigned>]() {
                    let zero: $signed = 0;
                    let actual = zero.homosign::<$unsigned>();

                    let expect: $unsigned = 0;
                    assert_eq!(expect, actual);
                }

                #[test]
                fn [<test_homosign_zero_ $unsigned _ $signed>]() {
                    let zero: $unsigned = 0;
                    let actual = zero.homosign::<$signed>();

                    let expect: $signed = 0;
                    assert_eq!(expect, actual);
                }

                #[test]
                fn [<test_homosign_max_ $signed _ $unsigned>]() {
                    let max: $signed = <$signed>::MAX;
                    let actual = max.homosign::<$unsigned>();

                    let expect: $unsigned = <$unsigned>::MAX / 2;
                    assert_eq!(expect, actual);
                }

                #[test]
                fn [<test_homosign_max_ $unsigned _ $signed>]() {
                    let max: $unsigned = <$unsigned>::MAX / 2;
                    let actual = max.homosign::<$signed>();

                    let expect = <$signed>::MAX;
                    assert_eq!(expect, actual);
                }

                #[test]
                #[should_panic(expected = "is not homogeneous over signs")]
                fn [<test_homosign_panic_negative_ $signed _ $unsigned>]() {
                    let value: $signed = -1;
                    value.homosign::<$unsigned>();
                }

                #[test]
                #[should_panic(expected = "is not homogeneous over signs")]
                fn [<test_homosign_panic_overflow_ $signed _ $unsigned>]() {
                    let value: $unsigned = <$unsigned>::MAX / 2 + 1;
                    value.homosign::<$signed>();
                }
            }
        };
    }

    test_homosign!(i8, u8);
    test_homosign!(i16, u16);
    test_homosign!(i32, u32);
    test_homosign!(i64, u64);
    test_homosign!(i128, u128);
    test_homosign!(isize, usize);

    // lossy_float tests

    #[test]
    fn test_lossy_float() {
        assert_eq!(0f64.lossy_float::<f32>(), 0f32);
        assert_eq!(f64::from(f32::MAX).lossy_float::<f32>(), f32::MAX);
    }

    #[test]
    #[should_panic(expected = "will become infinite in")]
    fn test_lossy_float_panic_overflow() {
        let float = f64::from(f32::MAX) * 2.;
        float.lossy_float::<f32>();
    }

    #[test]
    #[should_panic(expected = "will become infinite in")]
    fn test_lossy_float_panic_underflow() {
        let float = f64::from(f32::MIN) * 2.;
        float.lossy_float::<f32>();
    }

    // small_int tests

    macro_rules! test_small_int_unsigned {
        ($from:ty; $($to:ty),*) => {
            paste! {
                $(
                    #[test]
                    fn [<test_small_int_zero_ $from _ $to>]() {
                        let zero: $from = 0;
                        let actual = zero.small_int::<$to>();
                        let expect: $to = 0;
                        assert_eq!(expect, actual);
                    }

                    #[test]
                    fn [<test_small_int_max_ $from _ $to>]() {
                        let zero: $from = <$from>::from($to::MAX);
                        let actual = zero.small_int::<$to>();
                        let expect: $to = $to::MAX;
                        assert_eq!(expect, actual);
                    }

                    #[test]
                    #[should_panic(expected = "is too large to fit into")]
                    fn [<test_small_int_panic_overflow_ $from _ $to>]() {
                        let int = <$from>::from(<$to>::MAX) + 1;
                        int.small_int::<$to>();
                    }
                )*
            }
        }
    }

    test_small_int_unsigned!(u16; u8);
    test_small_int_unsigned!(u32; u16, u8);
    test_small_int_unsigned!(u64; u32, u16, u8);
    test_small_int_unsigned!(u128; u64, u32, u16, u8);

    macro_rules! test_small_int_signed {
        ($from:ty; $($to:ty),*) => {
            test_small_int_unsigned!($from; $($to),*);

            $(

                paste! {
                    #[test]
                    #[should_panic(expected = "is too small to fit into")]
                    fn [<test_small_int_panic_underflow_ $from _ $to>]() {
                        let int = <$from>::from(<$to>::MIN) - 1;
                        int.small_int::<$to>();
                    }
                }
            )*
        }
    }

    test_small_int_signed!(i16; i8);
    test_small_int_signed!(i32; i16, i8);
    test_small_int_signed!(i64; i32, i16, i8);
    test_small_int_signed!(i128; i64, i32, i16, i8);

    // small_float tests

    macro_rules! test_small_float {
        ($float:ty; $($int:ty),*) => {
            paste! {
                $(
                    #[test]
                    fn [<test_small_float_zero_ $int _ $float>]() {
                        let zero: $int = 0;
                        let expect = zero.small_float::<$float>();
                        let actual: $float = 0.;
                        assert_eq!(expect, actual);
                    }

                    #[test]
                    fn [<test_small_float_max_ $int _ $float>]() {
                        let mut num: $int = 0;
                        let bits = std::cmp::min(<$float>::MANTISSA_DIGITS, <$int>::BITS);
                        for i in 0..bits {
                            num |= 1 << i;
                        }

                        num.small_float::<$float>();
                    }
                )*
            }
        }
    }

    test_small_float! {
        f32;
        u8, u16, u32, u64, u128, usize,
        i8, i16, i32, i64, i128, isize
    }
    test_small_float! {
        f64;
        u8, u16, u32, u64, u128, usize,
        i8, i16, i32, i64, i128, isize
    }

    macro_rules! test_small_float_panic_overflow {
        ($int:ty, $float:ty) => {
            paste! {
                #[test]
                #[should_panic(expected = "cannot fit into")]
                fn [<test_small_float_panic_overflow_ $int _ $float>]() {
                    <$int>::MAX.small_float::<$float>();
                }
            }
        };
    }

    test_small_float_panic_overflow!(u32, f32);
    test_small_float_panic_overflow!(i32, f32);
    test_small_float_panic_overflow!(u64, f64);
    test_small_float_panic_overflow!(i64, f64);

    macro_rules! test_small_float_panic_underflow {
        ($int:ty, $float:ty) => {
            paste! {
                #[test]
                #[should_panic(expected = "cannot fit into")]
                fn [<test_small_float_panic_underflow_ $int _ $float>]() {
                    <$int>::MIN.small_float::<$float>();
                }
            }
        };
    }

    test_small_float_panic_underflow!(i32, f32);
    test_small_float_panic_underflow!(i64, f64);

    macro_rules! test_trunc_int {
        ($float:ty; $($int:ty),*) => {
            paste! {
                $(
                    #[test]
                    fn [<test_trunc_int_ $float _ $int>]() {
                        let float = 1.5;
                        let expect: $int = 1;
                        let actual = float.trunc_int::<$int>();
                        assert_eq!(expect, actual);
                    }

                    #[test]
                    #[should_panic(expected = "Cannot convert a non-finite float (inf) to")]
                    fn [<test_trunc_int_panic_positive_infinity_ $float _ $int>]() {
                        <$float>::INFINITY.trunc_int::<$int>();
                    }

                    #[test]
                    #[should_panic(expected = "Cannot convert a non-finite float (-inf) to")]
                    fn [<test_trunc_int_panic_negative_infinity_ $float _ $int>]() {
                        <$float>::NEG_INFINITY.trunc_int::<$int>();
                    }

                    #[test]
                    #[should_panic(expected = "Cannot convert a non-finite float (NaN) to")]
                    fn [<test_trunc_int_panic_nan_ $float _ $int>]() {
                        <$float>::NAN.trunc_int::<$int>();
                    }
                )*
            }
        }
    }

    test_trunc_int! {
        f32;
        u8, u16, u32, u64, u128, usize,
        i8, i16, i32, i64, i128
    }
    test_trunc_int! {
        f64;
        u8, u16, u32, u64, u128, usize,
        i8, i16, i32, i64, i128
    }

    macro_rules! test_trunc_int_panic_overflow {
        ($float:ty; $($int:ty),*) => {
            paste! {
                $(
                    #[test]
                    #[should_panic(expected = "is too large to fit into")]
                    fn [<test_trunc_int_panic_overflow_ $float _ $int>]() {
                        let float = <$int>::MAX as $float * 2.;
                        float.trunc_int::<$int>();
                    }
                )*
            }
        }
    }

    test_trunc_int_panic_overflow!{
        f32;
        u8, u16, u32, u64, usize,
        i8, i16, i32, i64, isize
    }
    test_trunc_int_panic_overflow!{
        f64;
        u8, u16, u32, u64, u128, usize,
        i8, i16, i32, i64, i128, isize
    }
}
