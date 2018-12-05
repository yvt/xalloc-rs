//
// Copyright 2018 yvt, all rights reserved.
//
// Licensed under the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>. This file may
// not be copied, modified,or distributed except
// according to those terms.
//
extern crate xalloc;

use xalloc::Ring;

#[test]
fn create() {
    let ring = Ring::new(114514u32);
    assert!(ring.is_empty());
}

#[test]
fn create_zero_sized() {
    let ring = Ring::new(0u32);
    assert!(ring.is_empty());
    assert!(ring.is_full());
}

#[test]
fn reset1() {
    let mut ring = Ring::new(8u32);
    let (region1, offset1) = ring.alloc_back(4).unwrap();
    let (region2, offset2) = ring.alloc_back(4).unwrap();
    assert_eq!(offset1, 0);
    assert_eq!(offset2, 4);
    assert!(ring.is_full());
    ring.dealloc_front(region1);
    ring.dealloc_back(region2);

    // The `Ring` is now empty
    assert!(ring.is_empty());

    let (_, offset) = ring.alloc_back(8).unwrap();
    assert_eq!(offset, 0);
}

#[test]
fn reset2() {
    let mut ring = Ring::new(8u32);
    let (region1, offset1) = ring.alloc_back(4).unwrap();
    let (region2, offset2) = ring.alloc_back(4).unwrap();
    assert_eq!(offset1, 0);
    assert_eq!(offset2, 4);
    assert!(ring.is_full());
    ring.dealloc_back(region2);
    ring.dealloc_front(region1);

    // The `Ring` is now empty
    assert!(ring.is_empty());

    let (_, offset) = ring.alloc_back(8).unwrap();
    assert_eq!(offset, 0);
}

#[test]
#[should_panic]
fn alloc_back_zero_size() {
    let mut ring = Ring::new(8u32);
    ring.alloc_back_aligned(0, 1);
}

#[test]
#[should_panic]
fn alloc_back_bad_align() {
    let mut ring = Ring::new(8u32);
    ring.alloc_back_aligned(4, 3);
}

#[test]
#[should_panic]
fn alloc_front_zero_size() {
    let mut ring = Ring::new(8u32);
    ring.alloc_front_aligned(0, 1);
}

#[test]
#[should_panic]
fn alloc_front_bad_align() {
    let mut ring = Ring::new(8u32);
    ring.alloc_front_aligned(4, 3);
}

#[test]
fn alloc_back_too_large() {
    let mut ring = Ring::new(8u32);
    assert_eq!(ring.alloc_back_aligned(16, 1), None);
}

#[test]
fn alloc_front_too_large() {
    let mut ring = Ring::new(8u32);
    assert_eq!(ring.alloc_front_aligned(16, 1), None);
}

#[test]
fn alloc_back_too_large2() {
    let mut ring = Ring::new(8u32);
    ring.alloc_back(1).unwrap();
    assert_eq!(ring.alloc_back_aligned(8, 1), None);
}

#[test]
fn alloc_front_too_large2() {
    let mut ring = Ring::new(8u32);
    ring.alloc_back(1).unwrap();
    assert_eq!(ring.alloc_front_aligned(8, 1), None);
}

#[test]
fn alloc_back_aligned() {
    let mut ring = Ring::new(8u32);
    let (_, offset1) = ring.alloc_back_aligned(2, 64).unwrap();
    let (_, offset2) = ring.alloc_back_aligned(2, 4).unwrap();

    // 0   1   2   3   4   5   6   7   8
    // [1     ]        [2     ]
    assert_eq!(offset1, 0);
    assert_eq!(offset2, 4);
}

#[test]
fn alloc_back_wrap() {
    let mut ring = Ring::new(8u32);
    let (region, offset1) = ring.alloc_back(4).unwrap();
    let (_, offset2) = ring.alloc_back(2).unwrap();
    assert_eq!(offset1, 0);
    assert_eq!(offset2, 4);
    ring.dealloc_front(region);

    // 0   1   2   3   4   5   6   7   8
    // [new           ][2     ]
    assert_eq!(ring.alloc_back(6), None);
    assert_eq!(ring.alloc_back(5), None);
    let (_, offset) = ring.alloc_back(4).unwrap();
    assert_eq!(offset, 0);
}

#[test]
fn alloc_back_aligned_wrap() {
    let mut ring = Ring::new(8u32);
    let (region, offset1) = ring.alloc_back(4).unwrap();
    let (_, offset2) = ring.alloc_back(2).unwrap();
    assert_eq!(offset1, 0);
    assert_eq!(offset2, 4);
    ring.dealloc_front(region);

    // 0   1   2   3   4   5   6   7   8
    // [new   ]        [2     ]
    let (_, offset) = ring.alloc_back_aligned(2, 4).unwrap();
    assert_eq!(offset, 0);
}

#[test]
fn alloc_back_wrap_fail() {
    let mut ring = Ring::new(8u32);
    let (region, offset1) = ring.alloc_back(6).unwrap();
    let (_, offset2) = ring.alloc_back(2).unwrap();
    assert_eq!(offset1, 0);
    assert_eq!(offset2, 6);
    ring.dealloc_front(region);

    let (_, offset3) = ring.alloc_back(2).unwrap();
    assert_eq!(offset3, 0);

    // 0   1   2   3   4   5   6   7   8
    // [3     ][4     ]        [2     ]
    let (_, offset4) = ring.alloc_back(2).unwrap();
    assert_eq!(offset4, 2);

    assert_eq!(ring.alloc_back(8), None);
    assert_eq!(ring.alloc_back(6), None);
    assert_eq!(ring.alloc_back(4), None);
    assert_eq!(ring.alloc_back(2).unwrap().1, 4);
}

#[test]
fn alloc_front_aligned() {
    let mut ring = Ring::new(8u32);
    let (_, offset1) = ring.alloc_front_aligned(2, 64).unwrap();
    let (_, offset2) = ring.alloc_front_aligned(3, 4).unwrap();

    // 0   1   2   3   4   5   6   7   8
    // [1     ]        [2         ]
    assert_eq!(offset1, 0);
    assert_eq!(offset2, 4);
}

#[test]
fn alloc_front_wrap() {
    let mut ring = Ring::new(8u32);
    let (region, offset1) = ring.alloc_back(2).unwrap();
    let (_, offset2) = ring.alloc_back(2).unwrap();
    assert_eq!(offset1, 0);
    assert_eq!(offset2, 2);
    ring.dealloc_front(region);

    // 0   1   2   3   4   5   6   7   8
    //         [2     ][new           ]
    assert_eq!(ring.alloc_front(5), None);
    let (_, offset) = ring.alloc_front(4).unwrap();
    assert_eq!(offset, 4);
}

#[test]
fn alloc_front_aligned_wrap() {
    let mut ring = Ring::new(8u32);
    let (region, offset1) = ring.alloc_back(1).unwrap();
    let (_, offset2) = ring.alloc_back(4).unwrap();
    assert_eq!(offset1, 0);
    assert_eq!(offset2, 1);
    ring.dealloc_front(region);

    // 0   1   2   3   4   5   6   7   8
    //     [2             ]    [new   ]
    assert_eq!(ring.alloc_front_aligned(2, 4), None);
    let (_, offset) = ring.alloc_front_aligned(2, 2).unwrap();
    assert_eq!(offset, 6);
}

#[test]
fn alloc_front_aligned2() {
    let mut ring = Ring::new(8u32);
    let (region, offset1) = ring.alloc_back(2).unwrap();
    let (_, offset2) = ring.alloc_back(4).unwrap();
    assert_eq!(offset1, 0);
    assert_eq!(offset2, 2);
    ring.dealloc_front(region);

    // 0   1   2   3   4   5   6   7   8
    // [new   ][2             ]
    let (_, offset) = ring.alloc_front_aligned(2, 8).unwrap();
    assert_eq!(offset, 0);
}

#[test]
#[should_panic]
fn dealloc_front_bad() {
    let mut ring = Ring::new(8u32);
    let (_, _) = ring.alloc_back(3).unwrap();
    let (region2, _) = ring.alloc_back(3).unwrap();
    ring.dealloc_front(region2);
}

#[test]
#[should_panic]
fn dealloc_back_bad() {
    let mut ring = Ring::new(8u32);
    let (region1, _) = ring.alloc_back(3).unwrap();
    let (_, _) = ring.alloc_back(3).unwrap();
    ring.dealloc_back(region1);
}

#[test]
#[should_panic]
fn dealloc_front_bad2() {
    let mut ring = Ring::new(8u32);
    let (region, _) = ring.alloc_back(3).unwrap();
    ring.dealloc_front(region);
    ring.dealloc_front(region);
}

#[test]
#[should_panic]
fn dealloc_back_bad2() {
    let mut ring = Ring::new(8u32);
    let (region, _) = ring.alloc_back(3).unwrap();
    ring.dealloc_back(region);
    ring.dealloc_back(region);
}
