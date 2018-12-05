//
// Copyright 2017 yvt, all rights reserved.
//
// Licensed under the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>. This file may
// not be copied, modified,or distributed except
// according to those terms.
//
//! A dynamic external memory allocator based on the TLSF (Two-Level Segregated Fit)
//! algorithm[^1].
//!
//! [^1]: Masmano, Miguel, et al. "TLSF: A new dynamic memory allocator for real-time systems."
//!       Real-Time Systems, 2004. ECRTS 2004. Proceedings. 16th Euromicro Conference on. IEEE, 2004.
//!
//! ## Type parameters
//!
//!  - `T` is an integer type used to represent region sizes. You usually use
//!    `u32` or `u64` for this.
//!  - `A` is a memory arena type used to allocate internal block structures.
//!
//! ## A Caveat
//!
//! This TLSF allocator implements a Good-Fit strategy. In order to achieve the
//! O(1) execution time, only the first element of each free space list is examined.
//! As a result, allocations are not guaranteed to succeed even if there
//! is an enough free space if the following condition is met:
//!
//!  - There is no free space that is larger than the requested size by a certain
//!    amount.
//!  - There is a free space that is almost as large as the requested size.
//!
//! Or more strictly:
//!
//!  - Let `S`, `mapping` the number of bytes to allocate and the mapping
//!    function that calculates the indexes into the TLSF data structure given
//!    the size of a block, respectively. There exists no free space with a size
//!    `s` where `mapping(s) != mapping(S) && s > S`.
//!  - There exists a free space with a size `s` where
//!    `mapping(s) == mapping(S) && s < S`.
//!
//! ## Memory Overhead
//!
//! A TLSF allocator requires the following internal storage to operate (some
//! details are excluded):
//!
//!  - A variable storing the size of the heap.
//!  - One first-level list that consists of pointers to second-level lists and
//!    a bit field of type `T` where each bit indicates whether a free block is
//!    available in the corresponding second-level list or not.
//!  - `FLI` second-level lists each of which consists of `1 << SLI` pointers to
//!    free blocks and a bit field of `SLI`-bit wide where each bit indicates
//!    whether the corresponding entry of the free block is valid or not.
//!
//! When the heap size `size` is a power of two and larger than `1 << SLI`,
//! `FLI` can be written as `log2(size) + 1 - SLI`. `SLI` is hard-coded to `4`
//! in this implementation. Using these, the baseline memory consumption can be
//! calculated by the formula `2 * T + 3 * PS + FLI * (3 * PS + SLI * P + SLI / 8)`
//! (where `PS = size_of::<usize>()`).
//!
//! The following table shows the estimated baseline memory consumption of
//! [`SysTlsf`] for common configurations.
//!
//! | `size_of::<usize>()` |  `T`  |       `size`      | memory consumption (bytes) |
//! | -------------------- | ----- | ----------------- | -------------------------- |
//! | `8` (64-bit system)  | `u32` | `16`              | 186                        |
//! |                      | `u32` | `1 << 10` (1KiB)  | 1,110                      |
//! |                      | `u32` | `1 << 24` (16MiB) | 3,266                      |
//! |                      | `u32` | `1 << 30` (1GiB)  | 4,190                      |
//! |                      | `u64` | `16`              | 194                        |
//! |                      | `u64` | `1 << 10` (1KiB)  | 1,118                      |
//! |                      | `u64` | `1 << 24` (16MiB) | 3,274                      |
//! |                      | `u64` | `1 << 30` (1GiB)  | 4,198                      |
//! |                      | `u64` | `1 << 36` (64GiB) | 5,122                      |
//! | `4` (32-bit system)  | `u32` | `16`              | 98                         |
//! |                      | `u32` | `1 << 10` (1KiB)  | 566                        |
//! |                      | `u32` | `1 << 24` (16MiB) | 1,658                      |
//! |                      | `u32` | `1 << 30` (1GiB)  | 2,126                      |
//!
//! [`SysTlsf`]: type.SysTlsf.html
//!
//! Note that this does not include the overhead incurred by the system memory
//! allocator.
//!
//! Furthermore, each allocated/free region (represented by `TlsfBlock`)
//! consumes a certain amount of memory. The exact size of `TlsfBlock` might
//! differ among compiler versions due to structure layout optimizations, but
//! we can know the lower bound:
//!
//! ```
//! use xalloc::tlsf::TlsfBlock;
//! use std::mem::size_of;
//! assert!(size_of::<TlsfBlock<u32, u32>>() >= 25);
//! assert!(size_of::<TlsfBlock<u32, u64>>() >= 41);
//! assert!(size_of::<TlsfBlock<u64, u64>>() >= 49);
//! ```
//!
//! ## Performance
//!
//! The allocation throughput is mostly equivalent to that of jemalloc.
use num::{One, Zero};
use std::fmt;
use unreachable::{unreachable, UncheckedOptionExt};

use arena::{SafeArena, UnsafeArena, UnsafeArenaWithMembershipCheck};
use int::{BinaryInteger, BinaryUInteger};

type TlsfL2Bitmap = u16;
const LOG2_L2_SIZE: u32 = 4; // must be <= log2(sizeof(TlsfL2Bitmap)*8)
const L2_SIZE: u32 = 1 << LOG2_L2_SIZE;

/// TLSF-based external memory allocator.
///
/// See [the module-level documentation] for more.
///
/// [the module-level documentation]: index.html
///
/// ## Type parameters
///
///  - `T` is an integer type used to represent region sizes. You usually use
///    `u32` or `u64` for this.
///  - `A` is a memory arena type used to allocate internal block structures.
///
#[derive(Debug)]
pub struct Tlsf<T, A, P>
where
    A: UnsafeArena<TlsfBlock<T, P>, Ptr = P>,
    P: Clone + Default + PartialEq + Eq + fmt::Debug,
{
    size: T,
    l1: TlsfL1<T, P>,
    blocks: A,
}

use arena;

/// [`Tlsf`] that uses [`CheckedArena`] for rigorous memory safety check.
///
/// It is really slow. Use [`SysTlsf`] in a production code.
///
/// [`CheckedArena`]: crate::arena::CheckedArena
///
/// ## Type parameter
///
///  - `T` is an integer type used to represent region sizes. You usually use
///    `u32` or `u64` for this.
///
pub type SafeTlsf<T> =
    Tlsf<T, arena::CheckedArena<TlsfBlock<T, arena::checked::Ptr>>, arena::checked::Ptr>;

/// Type alias of [`TlsfRegion`] for [`SafeTlsf`].
pub type SafeTlsfRegion = TlsfRegion<arena::checked::Ptr>;

impl<T: BinaryUInteger> SafeTlsf<T> {
    /// Construct a `SafeTlsf`.
    pub fn new(size: T) -> Self {
        Tlsf::with_arena(size, arena::CheckedArena::new())
    }
}

/// `Tlsf` that uses the system allocator for the internal storage allocation.
///
/// ## Type parameter
///
///  - `T` is an integer type used to represent region sizes. You usually use
///    `u32` or `u64` for this.
///
pub type SysTlsf<T> = Tlsf<
    T,
    arena::PooledArena<TlsfBlock<T, arena::sys::Ptr>, arena::SysAllocator, arena::sys::Ptr>,
    arena::sys::Ptr,
>;

/// Type alias of [`TlsfRegion`] for [`SysTlsf`].
pub type SysTlsfRegion = TlsfRegion<arena::sys::Ptr>;

impl<T: BinaryUInteger> SysTlsf<T> {
    /// Construct a `SysTlsf`.
    pub fn new(size: T) -> Self {
        Tlsf::with_arena(size, arena::PooledArena::new(arena::SysAllocator))
    }

    /// Construct a `SysTlsf` with a specific capacity.
    pub fn with_capacity(size: T, capacity: usize) -> Self {
        Tlsf::with_arena(
            size,
            arena::PooledArena::with_capacity(arena::SysAllocator, capacity),
        )
    }
}

/// A handle type to a region allocated in a [`Tlsf`].
///
/// `TlsfRegion` returned by a `Tlsf` only can be used with the
/// same `Tlsf`.
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct TlsfRegion<P>(P);

/// Internal data structure used by [`Tlsf`] that represents a free/occpied
/// memory block.
#[derive(Debug)]
pub struct TlsfBlock<T, P> {
    /// Points the previous (in terms of the external memory address) block.
    prev: Option<P>,

    /// Points the next (in terms of the external memory address) block.
    next: Option<P>,

    /// The external memory address.
    address: T,

    /// The size of the block in the external memory space.
    size: T,
    state: TlsfBlockState<P>,
}

#[derive(Debug, PartialEq, Eq)]
enum TlsfBlockState<P> {
    Free {
        /// The previous free block in the same free space list.
        prev_free: Option<P>,

        /// The next free block in the same free space list.
        next_free: Option<P>,
    },
    Used,
}

impl<P> TlsfBlockState<P> {
    fn is_used(&self) -> bool {
        match self {
            TlsfBlockState::Used => true,
            _ => false,
        }
    }
}

/// First level table.
#[derive(Debug)]
struct TlsfL1<T, P> {
    /// Array of second level tables.
    ///
    /// - `l1[0]` contains segregated lists for free spaces smaller
    ///   than `L2_SIZE`.
    ///   `l1[0].l2[L] contains the segregated list for free spaces whose sizes
    ///   are equal to `L`.
    /// - `l1[K]` contains segregated lists for free spaces whose sizes are
    ///   in the range `L2_SIZE << (K - 1) .. L2_Size << K`.
    ///   `l1[K].l2[L] contains the segregated list for free spaces whose sizes
    ///   are in the range
    ///   `(L2_SIZE << (K - 1)) + (1 << (K - 1)) * L .. (L2_Size << (K - 1)) + (1 << (K - 1)) * (L + 1)`
    ///
    l1: Vec<TlsfL2<P>>,

    /// Each bit indices whether the corresponding element of
    /// `l1` has at least one free space or not.
    ///
    /// The following invariant holds:
    ///
    ///  - `(bitmap.extract_u32(i..(i+1)) != 0) == (i1[i].bitmap != 0)`
    //
    /// The number of L2 tables is proportional to the number of digits of the pool
    /// size, so using `T` here would be a good choice.
    bitmap: T,

    /// Points the free block that fills entire the available space
    /// (used only if the pool size is a power of two and no
    /// segregated list entry is available for it)
    entire: Option<P>,
}

/// Second level table.
#[derive(Debug, Clone)]
struct TlsfL2<P> {
    /// Each bit indicates whether the corresponding element of
    /// `l2` is valid or not.
    bitmap: TlsfL2Bitmap,

    /// Each element represents the first block in a free space list.
    ///
    /// Points blocks stored in `Tlsf::blocks`. The validity of each
    /// element is indicated by the corresponding bit of `bitmap`.
    l2: [P; L2_SIZE as usize],
}

impl<T, P, A> Tlsf<T, A, P>
where
    T: BinaryUInteger,
    A: UnsafeArena<TlsfBlock<T, P>, Ptr = P>,
    P: Clone + Default + PartialEq + Eq + fmt::Debug,
{
    /// Construct a `Tlsf`.
    pub fn with_arena(size: T, arena: A) -> Self {
        let mut sa = Tlsf {
            l1: TlsfL1::new(&size),
            size,
            blocks: arena,
        };

        // Create the initial free block
        let block = TlsfBlock {
            prev: None,
            next: None,
            address: Zero::zero(),
            size: sa.size.clone(),
            state: TlsfBlockState::Used, // don't care
        };
        let block_ptr = sa.blocks.insert(block);
        unsafe {
            sa.l1.link(&mut sa.blocks, block_ptr);
        }

        sa
    }

    /// Get a reference to the underlying memory arena.
    pub fn arena(&self) -> &A {
        &self.blocks
    }

    /// Get a mutable reference to the underlying memory arena.
    pub fn arena_mut(&mut self) -> &mut A {
        &mut self.blocks
    }

    /// Allocate a region of the size `size` with a given alignment requirement.
    ///
    /// Returns a handle of the allocated region and its offset if the
    /// allocation succeeds. Returns `None` otherwise.
    ///
    /// - `align` must be a power of two.
    /// - `size` must not be zero.
    #[cfg_attr(feature = "cargo-clippy", allow(clippy::needless_pass_by_value))]
    pub fn alloc_aligned(&mut self, size: T, align: T) -> Option<(TlsfRegion<P>, T)> {
        assert!(align.is_power_of_two());
        self.allocate_aligned_log2(size, align.trailing_zeros())
    }

    /// Allocate a region of the size `size`.
    ///
    /// Returns a handle of the allocated region and its offset if the
    /// allocation succeeds. Returns `None` otherwise.
    ///
    /// `size` must not be zero.
    pub fn alloc(&mut self, size: T) -> Option<(TlsfRegion<P>, T)> {
        self.allocate_aligned_log2(size, 0)
    }

    fn allocate_aligned_log2(&mut self, size: T, align_bits: u32) -> Option<(TlsfRegion<P>, T)> {
        if size > self.size {
            return None;
        }
        assert_ne!(size, Zero::zero());

        let suitable = unsafe { self.l1.search_suitable(&mut self.blocks, &size, align_bits) };
        suitable.map(|(position, free_block_ptr, pad)| unsafe {
            let (mut prev, mut next, free_block_address, free_block_size) = {
                let block = self.blocks.get_unchecked(&free_block_ptr);
                (
                    block.prev.clone(),
                    block.next.clone(),
                    block.address.clone(),
                    block.size.clone(),
                )
            };
            let data_end = pad.clone() + size.clone();

            // For exception safety...
            let mut reserve = 0;
            if pad != Zero::zero() {
                reserve += 1;
            }
            if data_end != free_block_size {
                reserve += 1;
            }
            self.blocks.reserve(reserve);

            self.l1
                .unlink_head(&mut self.blocks, free_block_ptr.clone(), position);
            self.blocks.remove_unchecked(&free_block_ptr);

            if pad != Zero::zero() {
                let block = TlsfBlock {
                    prev: prev.clone(),
                    next: None, // linked later
                    address: free_block_address.clone(),
                    size: pad.clone(),
                    state: TlsfBlockState::Used, // don't care
                };
                let block_ptr = self.blocks.insert(block);
                self.l1.link(&mut self.blocks, block_ptr.clone());
                if let Some(ref old_prev) = prev {
                    self.blocks.get_unchecked_mut(old_prev).next = Some(block_ptr.clone());
                }
                prev = Some(block_ptr);
            }

            if data_end != free_block_size {
                let block = TlsfBlock {
                    prev: None, // linked later
                    next: next.clone(),
                    address: free_block_address.clone() + data_end.clone(),
                    size: free_block_size.clone() - data_end.clone(),
                    state: TlsfBlockState::Used, // don't care
                };
                let block_ptr = self.blocks.insert(block);
                self.l1.link(&mut self.blocks, block_ptr.clone());
                if let Some(ref old_next) = next {
                    self.blocks.get_unchecked_mut(old_next).prev = Some(block_ptr.clone());
                }
                next = Some(block_ptr);
            }

            let main_ptr = {
                let block = TlsfBlock {
                    prev: prev.clone(),
                    next: next.clone(),
                    address: free_block_address.clone() + pad.clone(),
                    size,
                    state: TlsfBlockState::Used, // care!
                };
                self.blocks.insert(block)
            };

            // Connect neighboring blocks to this
            let address = self.blocks.get_unchecked(&main_ptr).address.clone();

            if let Some(ptr) = prev {
                self.blocks.get_unchecked_mut(&ptr).next = Some(main_ptr.clone());
            }
            if let Some(ptr) = next {
                self.blocks.get_unchecked_mut(&ptr).prev = Some(main_ptr.clone());
            }

            (TlsfRegion(main_ptr), address)
        })
    }

    /// Deallocate the specified region, without checking the origin of the
    /// `TlsfRegion`.
    ///
    /// This might result in an undefined behavior if `r` originates from
    /// a different instance of `Tlsf`.
    pub unsafe fn dealloc_unchecked(&mut self, r: TlsfRegion<P>) {
        let block_ptr = r.0;

        let (prev_ptr, next_ptr) = {
            let block = self.blocks.get_unchecked(&block_ptr);
            if let TlsfBlockState::Used = block.state {
            } else {
                // It's impossible for the application to obtain a
                // `TlsfRegion` for a free block. `TlsfRegion` isn't even
                // `Clone` nor `Copy`.
                unreachable();
            }
            (block.prev.clone(), block.next.clone())
        };

        // Try to merge neighboring free blocks
        let prev_info = if let Some(ref ptr) = prev_ptr {
            let block = self.blocks.get_unchecked(ptr);
            if let TlsfBlockState::Free { .. } = block.state {
                Some((block.prev.clone(), block.size.clone()))
            } else {
                None
            }
        } else {
            None
        };
        let next_info = if let Some(ref ptr) = next_ptr {
            let block = self.blocks.get_unchecked(ptr);
            if let TlsfBlockState::Free { .. } = block.state {
                Some((block.next.clone(), block.size.clone()))
            } else {
                None
            }
        } else {
            None
        };
        {
            let block = self.blocks.get_unchecked_mut(&block_ptr);
            if let Some((ref new_prev_ptr, ref prev_size)) = prev_info {
                block.prev = new_prev_ptr.clone();
                block.size += prev_size.clone();
                block.address -= prev_size.clone();
            }
            if let Some((ref new_next_ptr, ref next_size)) = next_info {
                block.next = new_next_ptr.clone();
                block.size += next_size.clone();
            }
        }

        if prev_info.is_some() {
            self.l1
                .unlink(&mut self.blocks, prev_ptr.clone().unchecked_unwrap());
            self.blocks.remove_unchecked(&prev_ptr.unchecked_unwrap());
        }
        if next_info.is_some() {
            self.l1
                .unlink(&mut self.blocks, next_ptr.clone().unchecked_unwrap());
            self.blocks.remove_unchecked(&next_ptr.unchecked_unwrap());
        }

        if let Some((Some(new_prev_ptr), _)) = prev_info {
            let block = self.blocks.get_unchecked_mut(&new_prev_ptr);
            block.next = Some(block_ptr.clone());
        }
        if let Some((Some(new_next_ptr), _)) = next_info {
            let block = self.blocks.get_unchecked_mut(&new_next_ptr);
            block.prev = Some(block_ptr.clone());
        }

        self.l1.link(&mut self.blocks, block_ptr);
    }

    #[doc(hidden)]
    pub unsafe fn test_integrity(&mut self, root_ptr: &TlsfRegion<P>)
    where
        P: fmt::Debug + PartialEq,
    {
        // Find the physically first block
        let mut first_ptr = root_ptr.0.clone();
        while self.blocks.get_unchecked(&first_ptr).prev.is_some() {
            first_ptr = self.blocks.get_unchecked(&first_ptr).prev.clone().unwrap();
        }

        let dump = || {
            use std::fmt::Write;
            let mut s = String::new();
            let mut cur_ptr = first_ptr.clone();
            loop {
                let cur = self.blocks.get_unchecked(&cur_ptr);
                let next_ptr = cur.next.clone();
                writeln!(
                    &mut s,
                    "{:?} - [{:?}, {:?}] - {:?}",
                    cur.prev, cur_ptr, cur.state, cur.next
                )
                .unwrap();
                if let Some(next_ptr) = next_ptr {
                    cur_ptr = next_ptr;
                } else {
                    break;
                }
            }
            s
        };

        // scan every block and check the physical connections
        let mut cur_ptr = first_ptr.clone();
        let mut addr = Zero::zero();
        loop {
            let cur = self.blocks.get_unchecked(&cur_ptr);
            assert_eq!(
                cur.address,
                addr,
                "[{:?}].prev ({:?}) should be {:?}. Dump: \n{}",
                cur_ptr,
                &cur.address,
                &addr,
                dump()
            );
            addr += cur.size.clone();

            let next_ptr = cur.next.clone();
            if let Some(next_ptr) = next_ptr {
                let next = self.blocks.get_unchecked(&next_ptr);
                assert_eq!(
                    next.prev,
                    Some(cur_ptr.clone()),
                    "[{:?}].prev ({:?}) should be {:?}. Dump: \n{}",
                    next_ptr,
                    next.prev,
                    cur_ptr,
                    dump()
                );
                assert!(
                    next.state.is_used() || cur.state.is_used(),
                    "[{:?}].state and [{:?}].state must not be Free at the same time. Dump: \n{}",
                    next_ptr,
                    cur_ptr,
                    dump()
                );
                cur_ptr = next_ptr;
            } else {
                break;
            }
        }
        assert_eq!(
            self.size,
            addr,
            "self.size ({:?}) should be {:?}. Dump: \n{}",
            &self.size,
            &addr,
            dump()
        );
    }
}

impl<T, P, A> Tlsf<T, A, P>
where
    T: BinaryUInteger,
    A: UnsafeArena<TlsfBlock<T, P>, Ptr = P> + UnsafeArenaWithMembershipCheck<TlsfBlock<T, P>>,
    P: Clone + Default + PartialEq + Eq + fmt::Debug,
{
    /// Deallocate the specified region.
    ///
    /// Returns `Err(r)` if `r` does not originate from the same instance of `Tlsf`.
    pub fn dealloc(&mut self, r: TlsfRegion<P>) -> Result<(), TlsfRegion<P>> {
        unsafe {
            if self.blocks.contains_unchecked(&r.0) {
                self.dealloc_unchecked(r);
                Ok(())
            } else {
                Err(r)
            }
        }
    }
}

impl<T, P, A> Tlsf<T, A, P>
where
    T: BinaryUInteger,
    A: UnsafeArena<TlsfBlock<T, P>, Ptr = P> + SafeArena<TlsfBlock<T, P>>,
    P: Clone + Default + PartialEq + Eq + fmt::Debug,
{
    /// Deallocate the specified region.
    ///
    /// `r` must originate from the same instance of `Tlsf`. Otherwise, `Tlsf`
    /// enters an inconsistent state and possibly panics, but does not cause an
    /// undefined behavior.
    pub fn dealloc_relaxed(&mut self, r: TlsfRegion<P>) {
        unsafe { self.dealloc_unchecked(r) }
    }
}

impl<T: BinaryUInteger, P> TlsfBlock<T, P> {
    /// Return whether the requested region can fit in this space (assuming it
    /// is free).
    ///
    /// The returned value is the size of padding required to meet the
    /// alignment requirement. `None` if it cannot fit.
    fn can_fit(&self, size: &T, align_bits: u32) -> Option<T> {
        if align_bits == 0 {
            if size <= &self.size {
                Some(Zero::zero())
            } else {
                None
            }
        } else {
            let start = self.address.clone().checked_ceil_fix(align_bits);
            let end_block = self.address.clone() + self.size.clone();
            if let Some(start) = start {
                if start < end_block && size <= &(end_block.clone() - start.clone()) {
                    Some(start - self.address.clone())
                } else {
                    None
                }
            } else {
                start
            }
        }
    }
}

impl<T: BinaryUInteger, P: Clone + Default + PartialEq + Eq + fmt::Debug> TlsfL1<T, P> {
    /// Constructs `TlsfL1`.
    fn new(size: &T) -> Self {
        assert!(size > &Zero::zero());

        let size_m1 = size.clone() - One::one();
        let num_l2s = T::max_digits().saturating_sub(LOG2_L2_SIZE + size_m1.leading_zeros()) + 1;

        Self {
            l1: vec![
                TlsfL2 {
                    bitmap: Zero::zero(),
                    l2: [
                        // L2_SIZE elements
                        P::default(),
                        P::default(),
                        P::default(),
                        P::default(),
                        P::default(),
                        P::default(),
                        P::default(),
                        P::default(),
                        P::default(),
                        P::default(),
                        P::default(),
                        P::default(),
                        P::default(),
                        P::default(),
                        P::default(),
                        P::default(),
                    ],
                };
                num_l2s as usize
            ],
            bitmap: Zero::zero(),
            entire: None,
        }
    }

    /// Compute the first and second level table index for a given size of free
    /// space.
    #[inline]
    fn map_size(&self, size: &T) -> (u32, u32) {
        // Equivalent to:
        // `let l1_index = T::max_digits().saturating_sub(LOG2_L2_SIZE + size.leading_zeros());`
        let l1_index = T::max_digits()
            - LOG2_L2_SIZE
            - (size.clone() | T::ones(0..LOG2_L2_SIZE)).leading_zeros();

        // Branch-less equivalent of:
        // `let min_bit_index = l1_index.saturating_sub(1);`
        let min_bit_index = l1_index - if l1_index == 0 { 0 } else { 1 };

        let l2_index = (size.clone() >> min_bit_index).extract_u32(0..LOG2_L2_SIZE);

        (l1_index, l2_index)
    }

    /// Search a free block at least as large as `size` with the alignment
    /// requirement `1 << align_bits`.
    ///
    /// The result can be one of the following:
    ///
    ///  - `None`: No suitable block was found.
    ///  - `Some((position, block_ptr, pad)):  A suitable block was found. `position` is either of:
    ///      - `Some((l1, l2))`: `block_ptr` is the head of the free space list at the position `(l1, l2)`.
    ///      - `None`: `block_ptr` is `self.entire`.
    ///
    /// `size` must be less than or equal to the size of the heap.
    #[cfg_attr(feature = "cargo-clippy", allow(clippy::type_complexity))]
    unsafe fn search_suitable<A: UnsafeArena<TlsfBlock<T, P>, Ptr = P>>(
        &self,
        blocks: &mut A,
        size: &T,
        align_bits: u32,
    ) -> Option<(Option<(u32, u32)>, P, T)> {
        if let Some(ref entire) = self.entire {
            return Some((None, entire.clone(), Zero::zero()));
        }

        let (l1_first, l2_first) = self.map_size(size);
        if self.bitmap.get_bit(l1_first) {
            if l1_first as usize >= self.l1.len() {
                unreachable();
            }
            let l2t: &TlsfL2<P> = &self.l1[l1_first as usize];
            if l2t.bitmap.get_bit(l2_first) {
                // Found a free block in the same bucket.
                let block_ptr = l2t.l2[l2_first as usize].clone();
                let block = blocks.get_unchecked(&block_ptr);
                if let Some(pad) = block.can_fit(size, align_bits) {
                    return Some((Some((l1_first, l2_first)), block_ptr, pad));
                }
            }

            // Search the same second level table.
            let l2 = l2t.bitmap.bit_scan_forward(l2_first + 1);
            if l2 < L2_SIZE {
                // Found one
                let block_ptr = l2t.l2[l2 as usize].clone();
                let can_fit = if align_bits == 0 {
                    Some(Zero::zero())
                } else {
                    blocks.get_unchecked(&block_ptr).can_fit(size, align_bits)
                };
                if let Some(pad) = can_fit {
                    if align_bits == 0 {
                        debug_assert!(blocks
                            .get_unchecked(&block_ptr)
                            .can_fit(size, align_bits)
                            .is_some());
                    }
                    return Some((Some((l1_first, l2)), block_ptr, pad));
                }
            }
        }

        let mut l1_first = self.bitmap.bit_scan_forward(l1_first + 1);
        let mut l2_first = if l1_first == T::max_digits() {
            return None;
        } else {
            if l1_first as usize >= self.l1.len() {
                unreachable();
            }
            let l2t: &TlsfL2<P> = &self.l1[l1_first as usize];
            let l2 = l2t.bitmap.bit_scan_forward(0);
            debug_assert_ne!(l2, TlsfL2Bitmap::max_digits());
            let block_ptr = l2t.l2[l2 as usize].clone();
            let can_fit = if align_bits == 0 {
                Some(Zero::zero())
            } else {
                blocks.get_unchecked(&block_ptr).can_fit(size, align_bits)
            };
            if let Some(pad) = can_fit {
                if align_bits == 0 {
                    debug_assert!(blocks
                        .get_unchecked(&block_ptr)
                        .can_fit(size, align_bits)
                        .is_some());
                }
                return Some((Some((l1_first, l2)), block_ptr, pad));
            }
            l2
        };

        // For aligned allocations, there are cases where no free space that can
        // satisfy the alignment requirement even if the size requirement is met.
        // We need to check more free lists.
        //
        // The code below should be unreachable for allocations without an
        // alignment requirement.
        debug_assert_ne!(align_bits, 0);

        // FIXME: add explanation
        let worst_size = size.ref_saturating_add(T::ones(0..align_bits));
        let (l1_worst, l2_worst) = self.map_size(&worst_size);
        while (l1_first, l2_first) < (l1_worst, l2_worst) {
            // Determine the next search start position
            l2_first += 1;
            if l2_first >= TlsfL2Bitmap::max_digits() {
                l1_first = self.bitmap.bit_scan_forward(l1_first + 1);
                if l1_first == T::max_digits() {
                    return None;
                }
                l2_first = 0;
            }

            let l2t: &TlsfL2<P> = &self.l1[l1_first as usize];
            let l2 = l2t.bitmap.bit_scan_forward(l2_first);
            if l2 == TlsfL2Bitmap::max_digits() {
                l2_first = l2;
                continue;
            }
            let block_ptr = l2t.l2[l2 as usize].clone();
            if let Some(pad) = blocks.get_unchecked(&block_ptr).can_fit(size, align_bits) {
                return Some((Some((l1_first, l2)), block_ptr, pad));
            } else {
                l2_first = l2;
            }
        }

        None
    }

    /// Remove the given block from the free space list.
    #[inline]
    unsafe fn unlink<A: UnsafeArena<TlsfBlock<T, P>, Ptr = P>>(
        &mut self,
        blocks: &mut A,
        block_ptr: P,
    ) {
        let (l1, l2) = self.map_size(&blocks.get_unchecked(&block_ptr).size);
        if l1 as usize >= self.l1.len() {
            self.entire = None;
        } else {
            {
                debug_assert!(self.bitmap.get_bit(l1));
                debug_assert!(
                    self.l1[l1 as usize].bitmap.get_bit(l2),
                    "L2 bitmap 0b{:b} has not bit {} set.",
                    &self.l1[l1 as usize].bitmap,
                    l2
                );
                if self.l1[l1 as usize].l2[l2 as usize] == block_ptr {
                    return self.unlink_head(blocks, block_ptr, Some((l1, l2)));
                }
            }

            // Retrieve the neighboring blocks (in the free space list)
            let (prev_ptr, o_next_ptr) = {
                let block = blocks.get_unchecked(&block_ptr);
                if let TlsfBlockState::Free {
                    prev_free: Some(ref prev_free),
                    ref next_free,
                } = block.state
                {
                    (prev_free.clone(), next_free.clone())
                } else {
                    unreachable();
                }
            };

            // Unlink the current block
            if let Some(ref next_ptr) = o_next_ptr {
                let mut next_block = blocks.get_unchecked_mut(next_ptr);
                if let TlsfBlockState::Free {
                    ref mut prev_free, ..
                } = next_block.state
                {
                    debug_assert_eq!(*prev_free, Some(block_ptr.clone()));
                    *prev_free = Some(prev_ptr.clone());
                } else {
                    unreachable();
                }
            }

            {
                let prev_block = blocks.get_unchecked_mut(&prev_ptr);
                if let TlsfBlockState::Free {
                    ref mut next_free, ..
                } = prev_block.state
                {
                    debug_assert_eq!(*next_free, Some(block_ptr.clone()));
                    *next_free = o_next_ptr;
                } else {
                    unreachable();
                }
            }
        }
    }

    /// Remove the given block from the free space list.
    ///
    /// `block_ptr` must be the head of the free space list specified by `position`.
    /// `block_ptr` returned by `search_suitable` always satisfies this condition,
    /// supposing no intervening modification was done.
    #[inline]
    unsafe fn unlink_head<A: UnsafeArena<TlsfBlock<T, P>, Ptr = P>>(
        &mut self,
        blocks: &mut A,
        block_ptr: P,
        position: Option<(u32, u32)>,
    ) {
        if let Some((l1, l2)) = position {
            let l2t: &mut TlsfL2<P> = &mut self.l1[l1 as usize];

            debug_assert!(self.bitmap.get_bit(l1));
            debug_assert!(
                l2t.bitmap.get_bit(l2),
                "L2 bitmap 0b{:b} has not bit {} set.",
                &l2t.bitmap,
                l2
            );
            debug_assert_eq!(block_ptr, l2t.l2[l2 as usize]);

            let next_block_ptr = {
                let block = blocks.get_unchecked(&block_ptr);
                if let TlsfBlockState::Free { ref next_free, .. } = block.state {
                    next_free.clone()
                } else {
                    unreachable();
                }
            };

            if let Some(next_block_ptr) = next_block_ptr {
                let next_block = blocks.get_unchecked_mut(&next_block_ptr);
                if let TlsfBlockState::Free {
                    ref mut prev_free, ..
                } = next_block.state
                {
                    debug_assert_eq!(*prev_free, Some(block_ptr));
                    *prev_free = None;
                } else {
                    unreachable();
                }

                l2t.l2[l2 as usize] = next_block_ptr;
            } else {
                l2t.bitmap.clear_bit(l2);
                if l2t.bitmap == Zero::zero() {
                    self.bitmap.clear_bit(l1);
                }

                // don't care about the value of `l2t.l2[l2 as usize]`
            }
        } else {
            debug_assert_eq!(Some(block_ptr), self.entire);
            self.entire = None;
        }
    }

    /// Insert the given block to a free space list.
    ///
    /// `block_ptr` must point a valid `TlsfBlock` in `blocks`.
    /// The given block's `TlsfBlock::state` will be overwritten with a new
    /// `TlsfBlockState::Free` value.
    #[inline]
    unsafe fn link<A>(&mut self, blocks: &mut A, block_ptr: P)
    where
        A: UnsafeArena<TlsfBlock<T, P>, Ptr = P>,
    {
        let (l1, l2) = self.map_size(&blocks.get_unchecked(&block_ptr).size);
        if l1 as usize >= self.l1.len() {
            self.entire = Some(block_ptr);
        } else {
            let l2t: &mut TlsfL2<P> = &mut self.l1[l1 as usize];

            // Update bitmaps
            let head_valid = l2t.bitmap.get_bit(l2);
            l2t.bitmap.set_bit(l2);
            self.bitmap.set_bit(l1);

            // Link the given block to the list
            let head = &mut l2t.l2[l2 as usize];

            {
                let block = blocks.get_unchecked_mut(&block_ptr);
                block.state = TlsfBlockState::Free {
                    prev_free: None,
                    next_free: if head_valid { Some(head.clone()) } else { None },
                };
            }
            if head_valid {
                let next_block = blocks.get_unchecked_mut(head);
                if let TlsfBlockState::Free {
                    ref mut prev_free, ..
                } = next_block.state
                {
                    debug_assert!(prev_free.is_none());
                    *prev_free = Some(block_ptr.clone());
                } else {
                    unreachable();
                }
            }

            *head = block_ptr;
        }
    }
}

#[test]
fn num_l2s() {
    for i in 1..L2_SIZE {
        let l1 = TlsfL1::<_, u32>::new(&(i as u32));
        assert_eq!(l1.l1.len(), 1);
    }
    for k in 0..4 {
        let i = L2_SIZE << k;
        let l1 = TlsfL1::<_, u32>::new(&i);
        assert_eq!(l1.l1.len(), k + 1);
    }
}
