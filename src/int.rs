//
// Copyright 2017 yvt, all rights reserved.
//
// Licensed under the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>. This file may
// not be copied, modified,or distributed except
// according to those terms.
//
//! Traits for integral types.
use core::mem::size_of;
use core::{fmt, ops};

use num::Integer;

/// Integral types with efficient binary operations.
pub trait BinaryInteger:
    Integer
    + Clone
    + Sized
    + ops::AddAssign
    + ops::SubAssign
    + ops::MulAssign
    + ops::DivAssign
    + ops::BitOrAssign
    + ops::BitAndAssign
    + ops::BitXorAssign
    + ops::BitOr<Self, Output = Self>
    + ops::BitAnd<Self, Output = Self>
    + ops::BitXor<Self, Output = Self>
    + ops::Shl<u32, Output = Self>
    + ops::Shr<u32, Output = Self>
    + ops::Not<Output = Self>
    + RefSaturatingAdd<Output = Self>
    + fmt::Debug
{
    type OneDigits: Iterator<Item = u32>;

    fn max_value() -> Self;
    fn min_value() -> Self;

    fn max_digits() -> u32;

    fn ones(range: ops::Range<u32>) -> Self;

    fn ones_truncated(range: ops::Range<u32>) -> Self;

    /// Return the number of trailing zeros in its binary representation.
    fn trailing_zeros(&self) -> u32;

    /// Return the number of leading zeros in its binary representation.
    fn leading_zeros(&self) -> u32;

    /// Return the number of ones in its binary representation.
    fn count_ones(&self) -> u32;

    /// Return the position of the least significant set bit since the position
    /// `start`.
    ///
    /// Retruns `Self::max_digits()` if none was found.
    fn bit_scan_forward(&self, start: u32) -> u32;

    /// Slice a part of its binary representation as `u32`.
    fn extract_u32(&self, range: ops::Range<u32>) -> u32;

    /// Retrieve whether the specified bit is set or not.
    fn get_bit(&self, i: u32) -> bool;

    /// Set a single bit.
    fn set_bit(&mut self, i: u32);

    /// Clear a single bit.
    fn clear_bit(&mut self, i: u32);

    /// Perform `ceil` treating the value as a fixed point number with `fp`
    /// fractional part digits.
    fn checked_ceil_fix(self, fp: u32) -> Option<Self>;

    /// Get an iterator over set bits, from the least significant bit to
    /// the most significant one.
    fn one_digits(&self) -> Self::OneDigits;
}

/// Types that supports saturating addition.
pub trait RefSaturatingAdd<RHS = Self> {
    type Output;
    fn ref_saturating_add(&self, rhs: RHS) -> Self::Output;
}

/// Unsigned integral types with efficient binary operations.
pub trait BinaryUInteger: BinaryInteger {
    /// Return `ture` if and only if `self == 2^k` for some `k`.
    fn is_power_of_two(&self) -> bool;
}

#[doc(hidden)]
pub struct OneDigits<T>(T);

macro_rules! impl_binary_integer {
    ($type:ty) => {
        impl BinaryInteger for $type {
            type OneDigits = OneDigits<Self>;

            #[inline]
            fn max_value() -> Self {
                <$type>::max_value()
            }
            #[inline]
            fn min_value() -> Self {
                <$type>::min_value()
            }

            #[inline]
            fn max_digits() -> u32 {
                (size_of::<$type>() * 8) as u32
            }
            #[inline]
            fn ones(range: ops::Range<u32>) -> Self {
                assert!(range.end <= Self::max_digits());
                Self::ones_truncated(range)
            }
            #[inline]
            fn ones_truncated(range: ops::Range<u32>) -> Self {
                assert!(range.start <= range.end);
                if range.end >= Self::max_digits() {
                    (0 as Self).wrapping_sub(1 << range.start)
                } else {
                    ((1 as Self) << range.end).wrapping_sub(1 << range.start)
                }
            }
            #[inline]
            fn trailing_zeros(&self) -> u32 {
                (*self).trailing_zeros()
            }
            #[inline]
            fn leading_zeros(&self) -> u32 {
                (*self).leading_zeros()
            }
            #[inline]
            fn count_ones(&self) -> u32 {
                (*self).count_ones()
            }
            #[inline]
            fn bit_scan_forward(&self, start: u32) -> u32 {
                if start >= Self::max_digits() {
                    Self::max_digits()
                } else {
                    (*self & !Self::ones(0..start)).trailing_zeros()
                }
            }
            #[inline]
            #[cfg_attr(feature = "cargo-clippy", allow(clippy::cast_lossless))]
            fn extract_u32(&self, range: ops::Range<u32>) -> u32 {
                let start = range.start;
                ((self & Self::ones_truncated(range)) >> start) as u32
            }
            #[inline]
            fn get_bit(&self, i: u32) -> bool {
                if i < Self::max_digits() {
                    self & ((1 as Self) << i) != 0
                } else {
                    false
                }
            }
            #[inline]
            fn set_bit(&mut self, i: u32) {
                if i < Self::max_digits() {
                    *self |= (1 as Self) << i;
                }
            }
            #[inline]
            fn clear_bit(&mut self, i: u32) {
                if i < Self::max_digits() {
                    *self &= !((1 as Self) << i);
                }
            }
            #[inline]
            fn checked_ceil_fix(self, fp: u32) -> Option<Self> {
                if fp >= Self::max_digits() {
                    if self == 0 {
                        Some(0)
                    } else {
                        None
                    }
                } else {
                    let mask = Self::ones(0..fp);
                    self.checked_add(mask).map(|x| x & !mask)
                }
            }
            #[inline]
            fn one_digits(&self) -> Self::OneDigits {
                OneDigits(*self)
            }
        }
        impl RefSaturatingAdd for $type {
            type Output = Self;
            fn ref_saturating_add(&self, rhs: Self) -> Self::Output {
                (*self).saturating_add(rhs)
            }
        }
        impl Iterator for OneDigits<$type> {
            type Item = u32;
            fn next(&mut self) -> Option<u32> {
                if self.0 == 0 {
                    None
                } else {
                    let index = self.0.trailing_zeros();
                    self.0 &= !((1 as $type) << index);
                    Some(index)
                }
            }
            fn size_hint(&self) -> (usize, Option<usize>) {
                let ones = self.len();
                (ones, Some(ones))
            }
            fn count(self) -> usize {
                self.len()
            }
        }
        impl ExactSizeIterator for OneDigits<$type> {
            fn len(&self) -> usize {
                self.0.count_ones() as usize
            }
        }
        impl DoubleEndedIterator for OneDigits<$type> {
            fn next_back(&mut self) -> Option<u32> {
                if self.0 == 0 {
                    None
                } else {
                    let index = (size_of::<$type>() * 8) as u32 - 1 - self.0.leading_zeros();
                    self.0 &= !((1 as $type) << index);
                    Some(index)
                }
            }
        }
    };
}

macro_rules! impl_binary_uinteger {
    ($type:ty) => {
        impl BinaryUInteger for $type {
            #[inline]
            fn is_power_of_two(&self) -> bool {
                Self::is_power_of_two(*self)
            }
        }
    };
}

impl_binary_integer!(i8);
impl_binary_integer!(i16);
impl_binary_integer!(i32);
impl_binary_integer!(i64);
impl_binary_integer!(isize);

impl_binary_integer!(u8);
impl_binary_integer!(u16);
impl_binary_integer!(u32);
impl_binary_integer!(u64);
impl_binary_integer!(usize);

impl_binary_uinteger!(u8);
impl_binary_uinteger!(u16);
impl_binary_uinteger!(u32);
impl_binary_uinteger!(u64);
impl_binary_uinteger!(usize);

use num::One;

pub(crate) fn round_up<T: BinaryUInteger>(x: &T, align: &T) -> T {
    (x.clone() + align.clone() - One::one()) & !(align.clone() - One::one())
}

pub(crate) fn round_down<T: BinaryUInteger>(x: &T, align: &T) -> T {
    x.clone() & !(align.clone() - One::one())
}
