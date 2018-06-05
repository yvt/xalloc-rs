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
fn systlsf_random(b: &mut Bencher) {
    let mut v: Vec<_> = (0..512).map(|_| None).collect();
    let mut sa = SysTlsf::with_capacity(512u32, 512);
    b.iter(|| unsafe {
        let mut r = Xorshift32(0x11451419);
        for _ in 0..65536 {
            let i = ((r.next() >> 8) & 511) as usize;
            if v[i].is_some() {
                sa.dealloc_unchecked(v[i].take().unchecked_unwrap());
            } else {
                v[i] = Some(sa.alloc(1u32).unchecked_unwrap().0);
            }
        }
        for x in v.iter_mut() {
            if let Some(x) = x.take() {
                sa.dealloc_unchecked(x);
            }
        }
    });
}

#[bench]
fn sys_random(b: &mut Bencher) {
    let mut v: Vec<_> = (0..512).map(|_| None).collect();
    b.iter(|| {
        let mut r = Xorshift32(0x11451419);
        for _ in 0..65536 {
            let i = ((r.next() >> 8) & 511) as usize;
            if v[i].is_some() {
                v[i].take();
            } else {
                v[i] = Some(Box::new(1u32));
            }
        }
        for x in v.iter_mut() {
            x.take();
        }
    });
}

#[bench]
fn systlsf_stack(b: &mut Bencher) {
    let mut sa = SysTlsf::with_capacity(65536u32, 65536);
    let mut v = Vec::with_capacity(65536);
    b.iter(|| unsafe {
        for _ in 0..65536 {
            v.push(sa.alloc(1u32).unchecked_unwrap().0);
        }
        while let Some(x) = v.pop() {
            sa.dealloc_unchecked(x);
        }
    });
}

#[bench]
fn sys_stack(b: &mut Bencher) {
    let mut v = Vec::with_capacity(65536);
    b.iter(|| {
        for _ in 0..65536 {
            v.push(Box::new(1u32));
        }
        while let Some(_) = v.pop() {}
    });
}
