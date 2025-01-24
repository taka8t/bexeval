use num_traits::{
    Zero, One, 
    WrappingAdd, WrappingSub, WrappingMul, WrappingNeg, 
    WrappingShl, WrappingShr,
    AsPrimitive
};

/// Definition of who can be used as a numerical value
/// Currently the immediately available types are primitive integer type
/// (u8, u16, u32, u64, usize, i8, i16, i32, i64, isize)
pub trait Integer :
    Copy + Clone + std::str::FromStr + std::fmt::Debug
    + Ord + Eq
    + Zero + One
    + AsPrimitive<u32>
    + WrappingAdd + WrappingSub + WrappingMul
    + WrappingNeg + WrappingShl + WrappingShr
    + std::ops::BitAnd<Self, Output = Self>
    + std::ops::BitOr<Self, Output = Self>
    + std::ops::BitXor<Self, Output = Self>
    + std::ops::Div<Self, Output = Self>
    + std::ops::Rem<Self, Output = Self>
    + std::ops::Not<Output = Self>
    + AsPrimitive<u32>
    + std::convert::From<bool>
{
    fn wrapping_pow(self, exp: u32) -> Self;

    fn count_ones(self) -> Self;

    fn count_zeros(self) -> Self;
}

macro_rules! impl_int {
    ($t:ty) => {
        impl Integer for $t {
            fn wrapping_pow(self, exp: u32) -> $t {
                self.wrapping_pow(exp)
            }

            fn count_ones(self) -> $t {
                self.count_ones().as_()
            }

            fn count_zeros(self) -> $t {
                self.count_zeros().as_()
            }
        }
    }
}

impl_int!(i8);
impl_int!(i16);
impl_int!(i32);
impl_int!(i64);
impl_int!(isize);
impl_int!(u8);
impl_int!(u16);
impl_int!(u32);
impl_int!(u64);
impl_int!(usize);