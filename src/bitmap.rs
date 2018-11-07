//
// Copyright 2017 yvt, all rights reserved.
//
// Licensed under the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>. This file may
// not be copied, modified,or distributed except
// according to those terms.
//
//! Free space bitmap-based external memory allocator.
//!
//! This allocator uses a simple bitmap to track the allocation state, and
//! relies on a naïve bit scan for allocation.
//!
//! ## Memory Overhead
//!
//! Since it uses a bitmap to track free space, it consumes a memory proportional
//! to the size of the heap. The memory consumption is estimated to be roughly
//! `size / 8` bytes, where `size` is the size of the heap measured by the
//! number of allocation units.
//!
//! `BitmapAlloc` does not store information about individual allocated regions
//! by itself. Therefore, `BitmapAlloc` would be preferred when the number of
//! allocations is quite high and each allocation is very small (preferably,
//! just one allocation unit).
//!
//! The following table shows the memory overhead comparison between `Tlsf` and
//! `BitmapAlloc` with a varying number of allocations (assuming the heap is
//! fully occupied).
//!
//! | `size` | # of allocations | `Tlsf` (bytes) | `BitmapAloc` (bytes) |
//! | ------ | ---------------- | -------------- | -------------------- |
//! | 1,024  | 0                | 1,118          | 128                  |
//! |        | 1                | 1,174          | 128                  |
//! |        | 256              | 15,454         | 128                  |
//! |        | 1,024            | 58,462         | 128                  |
//! | 65,536 | 0                | 1,118          | 8,192                |
//! |        | 1                | 1,174          | 8,192                |
//! |        | 1,024            | 58,462         | 8,192                |
//! |        | 65,536           | 3,671,134      | 8,192                |
//!
//! ## Performance
//!
//! The allocation throughput is roughly the same as of jemalloc.
use bitmaputils::*;
use int::BinaryInteger;
use std::ops::Range;

/// Free space bitmap-based external memory allocator.
///
/// See [the module-level documentation] for more.
///
/// [the module-level documentation]: index.html
#[derive(Debug, Clone)]
pub struct BitmapAlloc {
    bitmap: Vec<usize>,
    size: usize,
    next: usize,
}

/// A handle type to a region allocated in a `BitmapAlloc`.
///
/// `BitmapAllocRegion` returned by a `BitmapAlloc` only can be used with the
/// same `BitmapAlloc`.
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct BitmapAllocRegion {
    range: Range<usize>,
}

impl BitmapAlloc {
    /// Construct a `BitmapAlloc`.
    pub fn new(size: usize) -> Self {
        let width = <usize>::max_digits() as usize;
        Self {
            bitmap: vec![0; (size + width - 1) / width],
            size,
            next: 0,
        }
    }

    /// Alias of [`alloc_next`].
    ///
    /// [`alloc_next`]: #method.alloc_next
    pub fn alloc(&mut self, size: usize) -> Option<(BitmapAllocRegion, usize)> {
        self.alloc_next(size)
    }

    /// Allocate a region of the size `size` using a Next-Fit strategy.
    /// The time complexity is linear to the size of the heap.
    ///
    /// Returns a handle of the allocated region and its offset if the
    /// allocation succeeds. Returns `None` otherwise.
    ///
    /// `size` must not be zero.
    pub fn alloc_next(&mut self, size: usize) -> Option<(BitmapAllocRegion, usize)> {
        let next = self.next;
        self.alloc_inner(size, next)
            .or_else(|| self.alloc_first(size))
    }

    /// Allocate a region of the size `size` using a First-Fit strategy.
    /// The time complexity is linear to the size of the heap.
    ///
    /// Returns a handle of the allocated region and its offset if the
    /// allocation succeeds. Returns `None` otherwise.
    ///
    /// `size` must not be zero.
    pub fn alloc_first(&mut self, size: usize) -> Option<(BitmapAllocRegion, usize)> {
        self.alloc_inner(size, 0)
    }

    fn alloc_inner(&mut self, size: usize, start: usize) -> Option<(BitmapAllocRegion, usize)> {
        assert!(size != 0);

        if start + size > self.size {
            return None;
        }

        find_zeros(&self.bitmap, start, size).and_then(|offs| {
            let range = offs..offs + size;
            if range.end <= self.size {
                set_bits_ranged(&mut self.bitmap, range.clone());
                if range.end == self.size {
                    self.next = 0;
                } else {
                    self.next = range.end;
                }
                Some((BitmapAllocRegion { range }, offs))
            } else {
                None
            }
        })
    }

    /// Deallocate the specified region.
    ///
    /// `r` must originate from the same instance of `BitmapAlloc`. Otherwise,
    /// `BitmapAlloc` enters an inconsistent state and possibly panics, but does
    /// not cause an undefined behavior.
    pub fn dealloc_relaxed(&mut self, r: BitmapAllocRegion) {
        // Optimize for stack-like usage
        if self.next == r.range.end {
            self.next = r.range.start;
        }

        clear_bits_ranged(&mut self.bitmap, r.range);
    }
}
