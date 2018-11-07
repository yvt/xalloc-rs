//
// Copyright 2017 yvt, all rights reserved.
//
// Licensed under the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>. This file may
// not be copied, modified,or distributed except
// according to those terms.
//
//! Dynamic suballocators for external memory (e.g., Vulkan device memory).
//!
//! # Provided Algorithms
//!
//! |               Name              | Time Complexity |  Space Complexity |
//! | ------------------------------- | --------------- | ----------------- |
//! | TLSF (Two-Level Segregated Fit) | `O(1)`          | `O(N + log size)` |
//! | Free space bitmap               | `O(size)`       | `O(size)`         |
//!
//! (`size`: heap size measured by the number of allocation units, `N`: number of allocations)
//!
//! # Examples
//!
//! ```
//! use xalloc::{SysTlsf, SysTlsfRegion};
//! let mut tlsf = xalloc::SysTlsf::new(8u32);
//!
//! // Allocate regions
//! let alloc1: (SysTlsfRegion, u32) = tlsf.alloc(4).unwrap();
//! let alloc2: (SysTlsfRegion, u32) = tlsf.alloc(4).unwrap();
//! let (region1, offset1) = alloc1;
//! let (region2, offset2) = alloc2;
//! println!("allocated #1: {:?}", (&region1, offset1));
//! println!("allocated #2: {:?}", (&region2, offset2));
//!
//! // Deallocate a region
//! tlsf.dealloc(region1).unwrap();
//!
//! // Now we can allocate again
//! tlsf.alloc(2).unwrap();
//! tlsf.alloc(2).unwrap();
//! ```
//!
//! # Feature Flags
//!
//! - `nightly` — Enables optimizations which currently require a Nightly Rust
//!   compiler. This flag is now unused due to the [stabilization] of `NonNull`
//!   in Rust 1.25.
//!
//! [stabilization]: https://blog.rust-lang.org/2018/03/29/Rust-1.25.html
//!
// Clippy does not understand that generic numeric types are not always
// as capable as built-in ones and raise false warnings
#![allow(clippy::op_ref)]

pub extern crate num;
extern crate unreachable;

pub mod arena;
pub mod bitmap;
mod bitmaputils;
pub mod int;
pub mod tlsf;

pub use self::bitmap::{BitmapAlloc, BitmapAllocRegion};
pub use self::tlsf::{
    SafeTlsf, SafeTlsfRegion, SysTlsf, SysTlsfRegion, Tlsf, TlsfBlock, TlsfRegion,
};
