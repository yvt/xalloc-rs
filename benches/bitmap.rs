//
// Copyright 2017 yvt, all rights reserved.
//
// Licensed under the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>. This file may
// not be copied, modified,or distributed except
// according to those terms.
//
#![feature(test)]
extern crate test;
extern crate unreachable;
extern crate xalloc;

use test::Bencher;
use unreachable::UncheckedOptionExt;
use xalloc::*;

struct Xorshift32(u32);

impl Xorshift32 {
    fn next(&mut self) -> u32 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 17;
        self.0 ^= self.0 << 5;
        !self.0
    }
}

#[bench]
fn bitmap_random(b: &mut Bencher) {
    let mut v: Vec<_> = (0..512).map(|_| None).collect();
    let mut sa = BitmapAlloc::new(512);
    b.iter(|| unsafe {
        let mut r = Xorshift32(0x11451419);
        for _ in 0..65536 {
            let i = ((r.next() >> 8) & 511) as usize;
            if v[i].is_some() {
                sa.dealloc_relaxed(v[i].take().unchecked_unwrap());
            } else {
                v[i] = Some(sa.alloc(1).unchecked_unwrap().0);
            }
        }
        for x in v.iter_mut() {
            if let Some(x) = x.take() {
                sa.dealloc_relaxed(x);
            }
        }
    });
}

#[bench]
fn bitmap_4_random(b: &mut Bencher) {
    let mut v: Vec<_> = (0..512).map(|_| None).collect();
    let mut sa = BitmapAlloc::new(512 * 4);
    b.iter(|| unsafe {
        let mut r = Xorshift32(0x11451419);
        for _ in 0..65536 {
            let i = ((r.next() >> 8) & 511) as usize;
            if v[i].is_some() {
                sa.dealloc_relaxed(v[i].take().unchecked_unwrap());
            } else {
                v[i] = Some(sa.alloc(4).unchecked_unwrap().0);
            }
        }
        for x in v.iter_mut() {
            if let Some(x) = x.take() {
                sa.dealloc_relaxed(x);
            }
        }
    });
}
