//
// Copyright 2017 yvt, all rights reserved.
//
// Licensed under the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>. This file may
// not be copied, modified,or distributed except
// according to those terms.
//
extern crate xalloc;

use xalloc::BitmapAlloc;
use std::ops;

struct Xorshift32(u32);

impl Xorshift32 {
    /// Returns a random integer in `[0, 0xfffffffe]`
    fn next(&mut self) -> u32 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 17;
        self.0 ^= self.0 << 5;
        !self.0
    }
    fn next_range(&mut self, range: ops::Range<u32>) -> u32 {
        let len = range.end - range.start;
        let mut mask = len - 1;
        mask |= mask >> 1;
        mask |= mask >> 2;
        mask |= mask >> 4;
        mask |= mask >> 8;
        mask |= mask >> 16;

        // Let's not care about the unbounded execution time :)
        let mut value = self.next() & mask;
        while value >= len {
            value = self.next() & mask;
        }

        value + range.start
    }
}

#[test]
fn create() {
    for i in 1..100 {
        println!("new({})", i);
        BitmapAlloc::new(i);
    }
}

#[test]
fn full_allocate() {
    for i in 1..100 {
        println!("new({})", i);
        let mut sa = BitmapAlloc::new(i);
        let result = sa.alloc(i);
        assert!(result.is_some());
    }
}

#[test]
fn allocate_two() {
    for i in 1..50 {
        for k in 1..i {
            println!("new({})", i);
            let mut sa = BitmapAlloc::new(i);
            println!("  alloc({})", k);
            let result1 = sa.alloc(k);
            assert!(result1.is_some());
            println!("  alloc({})", i - k);
            let result2 = sa.alloc((i - k));
            assert!(result2.is_some());
        }
    }
}

#[test]
fn allocate_three() {
    for i in 1..50 {
        for k in 1..i {
            for j in 1..i - k {
                println!("new({})", i);
                let mut sa = BitmapAlloc::new(i);
                println!("  alloc({})", k);
                let result1 = sa.alloc(k);
                assert!(result1.is_some());
                println!("  alloc({})", i - k - j);
                let result2 = sa.alloc((i - k - j));
                assert!(result2.is_some());
                println!("  alloc({})", j);
                let result3 = sa.alloc((j));
                assert!(result3.is_some());
            }
        }
    }
}

#[test]
fn allocate_deallocate_two1() {
    for i in 1..50 {
        for k in 1..i {
            println!("new({})", i);
            let mut sa = BitmapAlloc::new(i);
            println!("  alloc({})", k);
            let result1 = sa.alloc(k);
            assert!(result1.is_some());
            println!("  alloc({})", i - k);
            let result2 = sa.alloc((i - k));
            assert!(result2.is_some());

            println!("  dealloc(result1)");
            sa.dealloc_relaxed(result1.unwrap().0);
            println!("  dealloc(result2)");
            sa.dealloc_relaxed(result2.unwrap().0);
        }
    }
}

#[test]
fn stress() {
    let mut sa = BitmapAlloc::new(1000);
    let mut allocated = Vec::new();
    let mut r = Xorshift32(0x11451419u32);
    for _ in 0..1000 {
        let len = 1u32 + (r.next() & 127u32);
        println!("alloc({})", len);
        let reg = sa.alloc(len as usize);
        if let Some((reg, pos)) = reg {
            println!("  success: {:?}", (&reg, pos));
            allocated.push(reg);
        } else {
            assert!(allocated.len() > 0);
            let a_index = r.next_range(0..allocated.len() as u32);
            let old_reg = allocated.swap_remove(a_index as usize);
            println!("  failed, deallocating {:?}", old_reg);
            sa.dealloc_relaxed(old_reg);
        }
    }
    for reg in allocated {
        println!("dealloc({:?})", reg);
        sa.dealloc_relaxed(reg);
    }

    // Try the full allocation
    println!("alloc({})", 1000u32);
    let reg = sa.alloc(1000);
    assert!(reg.is_some());
}
