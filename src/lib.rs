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
//! # Examples
//!
//! ```
//! let mut tlsf = xalloc::SysTlsf::new(8u32);
//!
//! // Allocate regions
//! let (region1, offset1) = tlsf.alloc(4).unwrap();
//! let (region2, offset2) = tlsf.alloc(4).unwrap();
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
//!   compiler.
//!
#![cfg_attr(feature = "nightly", feature(nonzero))]
pub extern crate num_traits;
pub extern crate num_integer;

pub mod arena;
pub mod tlsf;
pub mod int;

pub use self::tlsf::{Tlsf, SafeTlsf, SysTlsf, TlsfBlock};
