//
// Copyright 2018 yvt, all rights reserved.
//
// Licensed under the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>. This file may
// not be copied, modified,or distributed except
// according to those terms.
//
//! A dynamic external memory allocator implementing the functionality of a
//! [circular buffer].
//!
//! [circular buffer]: https://en.wikipedia.org/wiki/Circular_buffer
//!
//! The calling program is responsible for tracking which allocated part is
//! currently the frontmost/backmost region of a [`Ring`]. When deallocating
//! a region, it must appropriately call `dealloc_front` or `dealloc_back`
//! depending on the position of the region within a `Ring`.
//!
//! # Examples
//!
//! ```
//! use xalloc::{Ring, RingRegion};
//! let mut ring: Ring<u32> = Ring::new(10);
//!
//! // Allocate regions
//! // [            ]
//! let alloc1: (RingRegion<u32>, u32) = ring.alloc_back(4).unwrap();
//! // [[ 1 ]       ]
//! let alloc2: (RingRegion<u32>, u32) = ring.alloc_back(4).unwrap();
//! // [[ 1 ][ 2 ]  ]
//! let (region1, offset1) = alloc1;
//! let (region2, offset2) = alloc2;
//! println!("allocated #1: {:?}", (&region1, offset1));
//! println!("allocated #2: {:?}", (&region2, offset2));
//!
//! // Deallocate regions
//! // [[ 1 ][ 2 ]  ]
//! ring.dealloc_front(region1);
//! // [     [ 2 ]  ]
//! ring.dealloc_front(region2);
//! // [            ]
//! ```
use num::{One, Zero};

use int::{round_down, round_up, BinaryUInteger};

/// A dynamic external memory allocator providing the functionality of a
/// [circular buffer].
///
/// [circular buffer]: https://en.wikipedia.org/wiki/Circular_buffer
///
/// See [the module-level documentation] for more.
///
/// [the module-level documentation]: index.html
///
/// ## Type parameters
///
///  - `T` is an integer type used to represent region sizes. You usually use
///    `u32` or `u64` for this.
///
#[derive(Debug)]
pub struct Ring<T> {
    size: T,

    /// The starting location of the allocated region. Must be less than `size`.
    start: T,

    /// The ending location of the allocated region. Must be less than `size`.
    end: T,

    /// Indicates whether this `Ring` is empty or not.
    empty: bool,
}

/// A handle type to a region allocated in a [`Ring`].
///
/// `RingRegion` returned by a `Ring` only can be used with the
/// same `Ring`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RingRegion<T> {
    start: T,
    end: T,
}

impl<T: BinaryUInteger> Ring<T> {
    /// Construct a `RingRegion`.
    ///
    /// `size` must be smaller than `T::max_value() >> 1` (this is a precaution
    /// taken not to cause unintentional overflows).
    pub fn new(size: T) -> Self {
        assert!(size < T::max_value() >> 1);

        Self {
            size: size.clone(),
            start: Zero::zero(),
            end: Zero::zero(),
            empty: true,
        }
    }

    /// Return `true` if `Ring` has no allocated regions.
    pub fn is_empty(&self) -> bool {
        self.empty
    }

    /// Return `true` if `Ring` has no free space.
    pub fn is_full(&self) -> bool {
        self.start == self.end
    }

    /// Allocate a region of the size `size` to the back of the allocated
    /// region.
    ///
    /// Returns a handle of the allocated region and its offset if the
    /// allocation succeeds. Returns `None` otherwise.
    ///
    /// `size` must not be zero.
    pub fn alloc_back(&mut self, size: T) -> Option<(RingRegion<T>, T)> {
        self.alloc_back_aligned(size, One::one())
    }

    /// Allocate a region of the size `size` to the front of the allocated
    /// region.
    ///
    /// Returns a handle of the allocated region and its offset if the
    /// allocation succeeds. Returns `None` otherwise.
    ///
    /// `size` must not be zero.
    pub fn alloc_front(&mut self, size: T) -> Option<(RingRegion<T>, T)> {
        self.alloc_front_aligned(size, One::one())
    }

    /// Allocate a region of the size `size` with a given alignment requirement
    /// to the back of the allocated region.
    ///
    /// Returns a handle of the allocated region and its offset if the
    /// allocation succeeds. Returns `None` otherwise.
    ///
    /// - `align` must be a power of two.
    /// - `size` must not be zero.
    pub fn alloc_back_aligned(&mut self, size: T, align: T) -> Option<(RingRegion<T>, T)> {
        assert_ne!(size, Zero::zero());
        assert!(align.is_power_of_two());

        if self.empty {
            self.alloc_empty(size)
        } else if size >= self.size {
            None
        } else {
            let mut new_wrapped = self.end <= self.start;
            let mut new_end = round_up(&self.end, &align);
            if new_end.clone() + size.clone() > self.size && !new_wrapped {
                new_end = Zero::zero();
                new_wrapped = true;
            }
            if new_wrapped && new_end.clone() + size.clone() > self.start {
                return None;
            }

            let offset = new_end.clone();
            new_end += size;
            if new_end == self.size {
                new_end = Zero::zero();
            }
            let region = RingRegion {
                start: self.end.clone(),
                end: new_end.clone(),
            };
            self.end = new_end;
            Some((region, offset))
        }
    }

    /// Allocate a region of the size `size` with a given alignment requirement
    /// to the front of the allocated region.
    ///
    /// Returns a handle of the allocated region and its offset if the
    /// allocation succeeds. Returns `None` otherwise.
    ///
    /// - `align` must be a power of two.
    /// - `size` must not be zero.
    pub fn alloc_front_aligned(&mut self, size: T, align: T) -> Option<(RingRegion<T>, T)> {
        assert_ne!(size, Zero::zero());
        assert!(align.is_power_of_two());

        if self.empty {
            self.alloc_empty(size)
        } else if size >= self.size {
            None
        } else {
            //  0                   1align              2align
            //  |                   |    size           |
            //  |===================|=====|             |
            //  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ enlarged_size
            //                            ^^^^^^^^^^^^^^^ pad
            let enlarged_size = round_up(&size, &align);
            let pad = enlarged_size.clone() - size.clone();

            let mut new_wrapped = self.end <= self.start;
            let mut new_start = round_down(&(self.start.clone() + pad.clone()), &align);
            if new_start < enlarged_size.clone() && !new_wrapped {
                new_start = round_down(&(self.size.clone() + pad.clone()), &align);
                new_wrapped = true;
            }
            if new_wrapped && self.end.clone() + enlarged_size.clone() > new_start {
                return None;
            }

            new_start -= enlarged_size;
            let offset = new_start.clone();
            let region = RingRegion {
                start: new_start.clone(),
                end: self.start.clone(),
            };
            self.start = new_start;
            Some((region, offset))
        }
    }

    fn alloc_empty(&mut self, size: T) -> Option<(RingRegion<T>, T)> {
        debug_assert!(self.empty);

        if size <= self.size {
            self.start = Zero::zero();
            self.end = if size == self.size {
                Zero::zero()
            } else {
                size.clone()
            };
            self.empty = false;
            Some((
                RingRegion {
                    start: Zero::zero(),
                    end: size,
                },
                Zero::zero(),
            ))
        } else {
            None
        }
    }

    /// Deallocate frontmost (first) regions until `r` becomes the new frontmost
    /// region. `r` is not removed.
    ///
    /// `r` must be in `Ring`.
    /// Otherwise, `Ring` might enter an inconsistent state and/or panic, but
    /// does not cause an undefined behavior.
    pub fn dealloc_front_until(&mut self, r: RingRegion<T>) {
        assert!(!self.empty, "empty");
        self.start = r.start;
    }

    /// Deallocate backmost (last) regions until `r` becomes the new backmost
    /// region. `r` is not removed.
    ///
    /// `r` must be in `Ring`.
    /// Otherwise, `Ring` might enter an inconsistent state and/or panic, but
    /// does not cause an undefined behavior.
    pub fn dealloc_back_until(&mut self, r: RingRegion<T>) {
        assert!(!self.empty, "empty");
        self.end = r.end;
    }

    /// Deallocate the frontmost (first) region.
    ///
    /// `r` must be the current frontmost region of `Ring`.
    /// Otherwise, `Ring` might enter an inconsistent state and/or panic, but
    /// does not cause an undefined behavior.
    pub fn dealloc_front(&mut self, r: RingRegion<T>) {
        assert!(!self.empty, "empty");
        assert!(self.start == r.start, "not front");
        self.start = r.end;
        if self.start == self.end {
            self.empty = true;
        }
    }

    /// Deallocate the backmost (last) region.
    ///
    /// `r` must be the current backmost region of `Ring`.
    /// Otherwise, `Ring` might enter an inconsistent state and/or panic, but
    /// does not cause an undefined behavior.
    pub fn dealloc_back(&mut self, r: RingRegion<T>) {
        assert!(!self.empty, "empty");
        assert!(self.end == r.end, "not back");
        self.end = r.start;
        if self.start == self.end {
            self.empty = true;
        }
    }
}
