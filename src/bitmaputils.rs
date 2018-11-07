//
// Copyright 2017 yvt, all rights reserved.
//
// Licensed under the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>. This file may
// not be copied, modified,or distributed except
// according to those terms.
//
use int::BinaryUInteger;
use std::ops::Range;

pub fn set_bits_ranged<T: BinaryUInteger + Copy>(map: &mut [T], range: Range<usize>) {
    let width = T::max_digits() as usize;

    if range.start >= range.end {
        return;
    }
    let mut start_i = range.start / width;
    let start_f = range.start % width;
    let end_i = range.end / width;
    let end_f = range.end % width;

    assert!(start_i < map.len());
    assert!(end_i <= map.len());

    if start_i == end_i {
        map[start_i] |= T::ones(start_f as u32..end_f as u32);
    } else {
        if start_f != 0 {
            map[start_i] |= T::ones(start_f as u32..width as u32);
            start_i += 1;
        }
        for e in &mut map[start_i..end_i] {
            *e = !T::zero();
        }
        if end_f != 0 {
            map[end_i] |= T::ones(0..end_f as u32);
        }
    }
}

pub fn clear_bits_ranged<T: BinaryUInteger + Copy>(map: &mut [T], range: Range<usize>) {
    let width = T::max_digits() as usize;

    if range.start >= range.end {
        return;
    }
    let mut start_i = range.start / width;
    let start_f = range.start % width;
    let end_i = range.end / width;
    let end_f = range.end % width;

    assert!(start_i < map.len());
    assert!(end_i <= map.len());

    if start_i == end_i {
        map[start_i] &= !T::ones(start_f as u32..end_f as u32);
    } else {
        if start_f != 0 {
            map[start_i] &= !T::ones(start_f as u32..width as u32);
            start_i += 1;
        }
        for e in &mut map[start_i..end_i] {
            *e = T::zero();
        }
        if end_f != 0 {
            map[end_i] &= !T::ones(0..end_f as u32);
        }
    }
}

pub fn find_zeros<T: BinaryUInteger + Copy>(
    map: &[T],
    start: usize,
    count: usize,
) -> Option<usize> {
    let width = T::max_digits() as usize;

    if start >= map.len() * width {
        None
    } else if count >= width {
        find_zeros_large(map, start, count)
    } else if count == 0 {
        Some(start)
    } else if count == 1 {
        find_zeros_small(map, start, count, |i| i)
    } else if count == 2 {
        find_zeros_small(map, start, count, |i| i | i >> 1)
    } else if count <= 4 {
        let last = (count - 2) as u32;
        find_zeros_small(map, start, count, move |mut i| {
            i |= i >> 1;
            i |= i >> last;
            i
        })
    } else if count <= 8 {
        let last = (count - 4) as u32;
        find_zeros_small(map, start, count, move |mut i| {
            i |= i >> 1;
            i |= i >> 2;
            i |= i >> last;
            i
        })
    } else if count <= 16 {
        let last = (count - 8) as u32;
        find_zeros_small(map, start, count, move |mut i| {
            i |= i >> 1;
            i |= i >> 2;
            i |= i >> 4;
            i |= i >> last;
            i
        })
    } else if count <= 32 {
        let last = (count - 16) as u32;
        find_zeros_small(map, start, count, move |mut i| {
            i |= i >> 1;
            i |= i >> 2;
            i |= i >> 4;
            i |= i >> 8;
            i |= i >> last;
            i
        })
    } else if count <= 64 {
        let last = (count - 32) as u32;
        find_zeros_small(map, start, count, move |mut i| {
            i |= i >> 1;
            i |= i >> 2;
            i |= i >> 4;
            i |= i >> 8;
            i |= i >> 16;
            i |= i >> last;
            i
        })
    } else if count <= 128 {
        let last = (count - 64) as u32;
        find_zeros_small(map, start, count, move |mut i| {
            i |= i >> 1;
            i |= i >> 2;
            i |= i >> 4;
            i |= i >> 8;
            i |= i >> 16;
            i |= i >> 32;
            i |= i >> last;
            i
        })
    } else {
        panic!("unsupported: T is too large (> 128 bits)");
    }
}

fn find_zeros_large<T: BinaryUInteger + Copy>(
    map: &[T],
    start: usize,
    count: usize,
) -> Option<usize> {
    let width = T::max_digits() as usize;
    debug_assert!(count >= width);

    let i_f = start % width;
    let mut i_i = start / width;
    let mut run = 0;
    debug_assert!(i_i < map.len());

    if i_f != 0 {
        run = (map[i_i] | T::ones(0..i_f as u32)).leading_zeros() as usize;
        i_i += 1;
    }

    while i_i < map.len() {
        if map[i_i].is_zero() {
            run += width;
            if run >= count {
                return Some(i_i * width + width - run);
            }
        } else {
            let tz = map[i_i].trailing_zeros() as usize;
            run += tz;
            if run >= count {
                return Some(i_i * width + tz - run);
            }
            run = map[i_i].leading_zeros() as usize;
        }
        i_i += 1;
    }

    None
}

/// `find_zeros` for the cases where `count < T::max_digits()`.
///
/// `F` must return `(0..count).fold(0, |a, i| a | (x >> i))` for the input `x`.
fn find_zeros_small<T: BinaryUInteger + Copy, F>(
    map: &[T],
    start: usize,
    count: usize,
    dilate: F,
) -> Option<usize>
where
    F: Fn(T) -> T,
{
    let width = T::max_digits() as usize;
    debug_assert!(count > 0);
    debug_assert!(count < width);

    let dilate_mask = T::ones(0..(width + 1 - count) as u32);

    let i_f = start % width;
    let mut i_i = start / width;
    let mut run = 0;
    debug_assert!(i_i < map.len());

    if i_f != 0 {
        let m = dilate(map[i_i]);
        let mask = dilate_mask & T::ones(i_f as u32..T::max_digits());
        if m & mask != mask {
            return Some((!m).bit_scan_forward(i_f as u32) as usize + i_i * width);
        }
        run = (map[i_i] | T::ones(0..i_f as u32)).leading_zeros() as usize;
        debug_assert!(run < count);
        i_i += 1;
    }

    while i_i < map.len() {
        let tz = map[i_i].trailing_zeros() as usize;
        run += tz;
        if run >= count {
            return Some(i_i * width + tz - run);
        }

        let m = dilate(map[i_i]);
        if m & dilate_mask != dilate_mask {
            return Some((!m).trailing_zeros() as usize + i_i * width);
        }

        run = map[i_i].leading_zeros() as usize;
        debug_assert!(run < count);

        i_i += 1;
    }

    None
}

#[cfg(test)]
mod find_zeros_tests {
    use super::*;

    struct Xorshift32(u32);

    impl Xorshift32 {
        /// Returns a random integer in `[0, 0xfffffffe]`
        fn next(&mut self) -> u32 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 17;
            self.0 ^= self.0 << 5;
            !self.0
        }
    }

    fn patterns<F: FnMut(&[u32])>(mut f: F) {
        f(&[0; 16]);
        f(&[0xffffffff; 16]);
        f(&[0x01010101; 16]);
        f(&[0x80808080; 16]);
        f(&[0xdeadbeef; 16]);
        f(&[0x11451419; 16]);

        let mut buf = [0; 16];
        let mut rng = Xorshift32(12345678);
        for _ in 0..32 {
            for x in buf.iter_mut() {
                *x = rng.next();
            }
            f(&buf);
        }
        for _ in 0..32 {
            for x in buf.iter_mut() {
                *x = rng.next() & rng.next() & rng.next();
            }
            f(&buf);
        }

        use int::BinaryInteger;
        for _ in 0..32 {
            for x in buf.iter_mut() {
                *x = 0;
                if rng.next() & 0x1 != 0 {
                    x.set_bit(rng.next() & 31);
                }
            }
            f(&buf);
        }
    }

    fn find_zeros_naive<T: BinaryUInteger + Copy>(
        map: &[T],
        start: usize,
        count: usize,
    ) -> Option<usize> {
        let width = T::max_digits() as usize;
        let mut run = 0;
        if count == 0 && start < map.len() * width {
            return Some(start);
        }
        for i in start..map.len() * width {
            let i_f = i % width;
            let i_i = i / width;
            if map[i_i].get_bit(i_f as u32) {
                run = 0;
            } else {
                run += 1;
                if run >= count {
                    return Some(i + 1 - count);
                }
            }
        }
        None
    }

    struct BitField<'a, T: 'a>(&'a [T]);

    use std::fmt;
    impl<'a, T: BinaryUInteger + Copy + 'a> fmt::Debug for BitField<'a, T> {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "BitField (")?;

            let width = T::max_digits();
            for x in self.0.iter() {
                write!(f, " ")?;
                for i in 0..width {
                    write!(f, "{}", if x.get_bit(i) { "1" } else { "0" })?;
                }
            }

            write!(f, " )")
        }
    }

    fn test_one(count: usize) {
        patterns(|p| {
            for &s in [0, 1, 2, 30, 31, 32].iter() {
                assert_eq!(
                    find_zeros(p, s, count),
                    find_zeros_naive(p, s, count),
                    "{:?}",
                    (BitField(p), s, count)
                );
            }
        });
    }

    #[test]
    fn test_0() {
        test_one(0)
    }

    #[test]
    fn test_1() {
        test_one(1)
    }

    #[test]
    fn test_2() {
        test_one(2)
    }

    #[test]
    fn test_3() {
        test_one(3)
    }

    #[test]
    fn test_4() {
        test_one(4)
    }

    #[test]
    fn test_6() {
        test_one(6)
    }

    #[test]
    fn test_8() {
        test_one(8)
    }

    #[test]
    fn test_12() {
        test_one(12)
    }

    #[test]
    fn test_16() {
        test_one(16)
    }

    #[test]
    fn test_24() {
        test_one(24)
    }

    #[test]
    fn test_32() {
        test_one(32)
    }

    #[test]
    fn test_48() {
        test_one(48)
    }

    #[test]
    fn test_64() {
        test_one(64)
    }
}
