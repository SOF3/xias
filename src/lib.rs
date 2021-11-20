//! Explicit numeric type conversion.

/// See [`Homosign::homosign`].
pub trait Homosign<T> {
    /// Convert between signed and unsigned types of the same integer,
    /// assuming that the value is homogeneous over the conversion.
    fn homosign(self) -> T;
}

macro_rules! impl_homosign {
    ($unsigned:ty, $signed:ty) => {
        impl Homosign<$signed> for $unsigned {
            fn homosign(self) -> $signed {
                debug_assert!(self <= <$unsigned>::max_value() / 2, "{:?} is not homogeneous over signs", self);

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

/// See [`LossyFloat::lossy_float`].
pub trait LossyFloat<T> {
    /// Downscale the precision of a floating point value.
    fn lossy_float(self) -> T;
}

impl LossyFloat<f32> for f64 {
    fn lossy_float(self) -> f32 {
        debug_assert!(self <= f32::MAX.into(), "{:?} will become infinite in f32", self);

        self as f32
    }
}

/// See [`SmallInt::small_int`].
pub trait SmallInt<T> {
    /// Reduce the size of an integer,
    /// assuming that the value is within the range of the new type.
    fn small_int(self) -> T;
}

macro_rules! impl_small_int {
    ($from:ty; $($to:ty),*) => {
        $(
            impl SmallInt<$to> for $from {
                fn small_int(self) -> $to {
                    debug_assert!(self >= <$to>::min_value() as $from, "{:?} is too small to fit into {}", self, stringify!($to));
                    debug_assert!(self <= <$to>::max_value() as $from, "{:?} is too large to fit into {}", self, stringify!($to));

                    self as $to
                }
            }
        )*
    };
}

impl_small_int!(u16; u8, usize);
impl_small_int!(u32; u16, u8, usize);
impl_small_int!(u64; u32, u16, u8, usize);
impl_small_int!(u128; u64, u32, u16, u8, usize);
impl_small_int!(usize; u128, u64, u32, u16, u8);

impl_small_int!(i16; i8, isize);
impl_small_int!(i32; i16, i8, isize);
impl_small_int!(i64; i32, i16, i8, isize);
impl_small_int!(i128; i64, i32, i16, i8, isize);
impl_small_int!(isize; i128, i64, i32, i16, i8);

/// See [`SmallFloat::small_float`].
pub trait SmallFloat<T> {
    /// Converts an integer to a floating point value,
    /// assuming that the value can be losslessly represented in the new type.
    fn small_float(self) -> T;
}

macro_rules! impl_small_float_unsigned {
    ($($from:ty),*; $to:ty) => {
        $(
            impl SmallFloat<$to> for $from {
                fn small_float(self) -> $to {
                    debug_assert!({
                        let float_size = <$to>::MANTISSA_DIGITS;
                        let int_size = self.leading_zeros();
                        float_size >= int_size
                    }, "{:?} is too large to fit into {}", self, stringify!($to));

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
                            self.leading_zeros()
                        };
                        float_size >= int_size
                    }, "{:?} is too large to fit into {}", self, stringify!($to));

                    self as $to
                }
            }
        )*
    };
}

impl_small_float_signed!(i8, i16, i32, i64, i128, isize; f32);
impl_small_float_signed!(i8, i16, i32, i64, i128, isize; f64);
