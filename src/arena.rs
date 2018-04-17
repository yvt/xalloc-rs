//
// Copyright 2017 yvt, all rights reserved.
//
// Licensed under the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>. This file may
// not be copied, modified,or distributed except
// according to those terms.
//
//! Memory arena traits (used by `Tlsf`).
use std::fmt;

/// Homogeneous memory arena types supporting operations that do not guarantee
/// memory safety.
///
/// Methods prefixed with `_unchecked` all assume given pointers are valid;
/// specifically, they assumes that:
///
///  1. The pointers were constructed by the same instance of `UnsafeArena`.
///  2. The pointers have not been removed from the arena yet.
///
pub trait UnsafeArena<T> {
    /// Pointer type.
    ///
    ///  - `Ptr::clone(p)` returns a pointer that points the same object.
    ///  - `Ptr::default()` returns an uninitialized pointer with a well-defined
    ///    value (e.g., null pointer).
    ///  - `Ptr::eq(x, y)` checks the equality of two pointers. Both pointers
    ///    must originate from the same arena. Otherwise, the returned value
    ///    does not make sense.
    type Ptr: fmt::Debug + Clone + Default + PartialEq + Eq;

    /// Insert a value into the arena.
    ///
    /// Returns a pointer that points the inserted value.
    fn insert(&mut self, x: T) -> Self::Ptr;

    /// Reserves capacity for at least `additional` values to be inserted in the arena.
    fn reserve(&mut self, _additional: usize) {}

    /// Get a reference to a contained value, without a pointer validity check.
    unsafe fn get_unchecked(&self, ptr: &Self::Ptr) -> &T;

    /// Get a mutable reference to a contained value, without a pointer validity
    /// check.
    unsafe fn get_unchecked_mut(&mut self, ptr: &Self::Ptr) -> &mut T;

    /// Remove a value from the arena, without a pointer validity check.
    ///
    /// Returns the removed value.
    unsafe fn remove_unchecked(&mut self, ptr: &Self::Ptr) -> T;
}

/// Marker trait indicating all operations from `UnsafeArena` are actually
/// implemented as memory-safe (not `unsafe`).
///
/// An invalid operation on `SafeArena` must result in one of the following
/// possible outcomes:
///
///  1. A panic. The internal state can be left in an inconsistent state, but
///     even if so, further operations on the arena should not violate the
///     memory safety, for example by employing the "poisoning" strategy.
///  2. It behaves as if arbitrary valid values were provided as the parameter.
///
pub trait SafeArena<T>: UnsafeArena<T> {}

/// Homogeneous memory arena types capable of checking whether a given pointer
/// was created by the same instance of the arena.
pub trait UnsafeArenaWithMembershipCheck<T>: UnsafeArena<T> {
    /// Return `true` if the pointer was created from the same instance of the
    /// arena.
    ///
    /// Calling this with an already-freed pointer or an uninitialized pointer
    /// might result in an undefined behavior.
    unsafe fn contains_unchecked(&self, ptr: &Self::Ptr) -> bool;
}

/// Memory-safe homogeneous memory arena types.
pub trait Arena<T>: UnsafeArena<T> {
    /// Get a reference to a contained value.
    fn get(&self, ptr: &Self::Ptr) -> Option<&T>;

    /// Get a mutable reference to a contained value.
    fn get_mut(&mut self, ptr: &Self::Ptr) -> Option<&mut T>;

    /// Remove a value from the arena.
    ///
    /// Returns the removed value.
    fn remove(&mut self, ptr: &Self::Ptr) -> Option<T>;
}

#[cfg(test)]
fn test_common<T: UnsafeArenaWithMembershipCheck<&'static str>>(arena: &mut T) {
    let p1 = arena.insert("twi");
    let p2 = arena.insert("aj");

    unsafe {
        assert!(arena.contains_unchecked(&p1));
        assert!(arena.contains_unchecked(&p2));

        assert_eq!(arena.get_unchecked(&p1), &"twi");
        assert_eq!(arena.get_unchecked_mut(&p2), &"aj");

        *arena.get_unchecked_mut(&p2) = "flutter";

        assert_eq!(&arena.remove_unchecked(&p1), &"twi");
        assert_eq!(&arena.remove_unchecked(&p2), &"flutter");
    }
}

/// `UnsafeArena` implementation that relies on the system memory allocator.
pub mod sys {
    use super::*;
    use std::mem::{ManuallyDrop, transmute, transmute_copy};
    use std::ptr::read;

    use std::ptr::NonNull;

    /// `UnsafeArena` implementation that relies on the system memory allocator.
    #[derive(Debug, Clone, Copy)]
    pub struct SysAllocator;

    /// Pointer type of `SysAllocator`.
    pub struct Ptr(NonNull<u8>);

    impl Ptr {
        unsafe fn new<T>(ptr: *mut T) -> Self {
            debug_assert!(!ptr.is_null());
            Ptr(transmute(ptr))
        }

        fn as_ptr<T>(&self) -> *mut T {
            unsafe { transmute_copy(&self.0) }
        }
    }
    impl PartialEq for Ptr {
        fn eq(&self, other: &Self) -> bool {
            self.as_ptr::<u8>() == other.as_ptr::<u8>()
        }
    }
    impl Eq for Ptr {}
    impl Clone for Ptr {
        fn clone(&self) -> Self {
            unsafe { transmute_copy(self) }
        }
    }
    impl Default for Ptr {
        fn default() -> Self {
            static X: u8 = 0;
            unsafe { Ptr::new((&X) as *const u8 as *mut u8) }
        }
    }
    impl fmt::Debug for Ptr {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            f.debug_tuple("Ptr").field(&self.as_ptr::<u8>()).finish()
        }
    }
    impl fmt::Pointer for Ptr {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{:p}", &self.as_ptr::<u8>())
        }
    }

    unsafe impl Sync for Ptr {}
    unsafe impl Send for Ptr {}

    impl<T> UnsafeArena<T> for SysAllocator {
        type Ptr = Ptr;

        fn insert(&mut self, x: T) -> Self::Ptr {
            unsafe { Ptr::new(Box::into_raw(Box::new(ManuallyDrop::new(x)))) }
        }

        unsafe fn get_unchecked(&self, ptr: &Self::Ptr) -> &T {
            &**ptr.as_ptr::<ManuallyDrop<T>>()
        }

        unsafe fn get_unchecked_mut(&mut self, ptr: &Self::Ptr) -> &mut T {
            &mut **ptr.as_ptr::<ManuallyDrop<T>>()
        }

        unsafe fn remove_unchecked(&mut self, ptr: &Self::Ptr) -> T {
            let b = Box::from_raw(ptr.as_ptr::<ManuallyDrop<T>>());
            read(&**b)
        }
    }

    impl<T> UnsafeArenaWithMembershipCheck<T> for SysAllocator {
        unsafe fn contains_unchecked(&self, _ptr: &Self::Ptr) -> bool {
            true
        }
    }

    #[test]
    fn test() {
        test_common(&mut SysAllocator);
    }
}

pub use self::sys::SysAllocator;

/// Naïve memory-safe implementation of `Arena`.
pub mod checked {
    use super::*;
    use std::sync::Arc;
    use std::collections::HashMap;

    /// Naïve memory-safe implementation of `Arena`.
    ///
    /// For a test purpose only. Do not use this in production. It is really slow.
    #[derive(Debug)]
    pub struct CheckedArena<T> {
        map: HashMap<u64, T>,
        id: Arc<()>,
        next_key: u64,
    }

    /// Pointer type of `CheckedArena`.
    #[derive(Default, Debug, Clone, PartialEq, Eq, Hash)]
    pub struct Ptr(Arc<()>, u64);

    impl<T> CheckedArena<T> {
        /// Construct a `CheckedArena`.
        pub fn new() -> Self {
            Self {
                map: HashMap::new(),
                id: Arc::new(()),
                next_key: 0,
            }
        }
    }

    impl<T> UnsafeArena<T> for CheckedArena<T> {
        type Ptr = Ptr;

        fn insert(&mut self, x: T) -> Self::Ptr {
            let key = self.next_key;
            self.next_key = self.next_key.checked_add(1).unwrap();
            assert!(self.map.insert(key, x).is_none());
            Ptr(Arc::clone(&self.id), key)
        }

        unsafe fn get_unchecked(&self, ptr: &Self::Ptr) -> &T {
            assert!(self.contains_unchecked(ptr), "invalid arena");
            self.map.get(&ptr.1).expect("already removed")
        }

        unsafe fn get_unchecked_mut(&mut self, ptr: &Self::Ptr) -> &mut T {
            assert!(self.contains_unchecked(ptr), "invalid arena");
            self.map.get_mut(&ptr.1).expect("already removed")
        }

        unsafe fn remove_unchecked(&mut self, ptr: &Self::Ptr) -> T {
            assert!(self.contains_unchecked(ptr), "invalid arena");
            self.map.remove(&ptr.1).expect("already removed")
        }
    }

    impl<T> SafeArena<T> for CheckedArena<T> {}

    impl<T> UnsafeArenaWithMembershipCheck<T> for CheckedArena<T> {
        unsafe fn contains_unchecked(&self, ptr: &Self::Ptr) -> bool {
            Arc::ptr_eq(&ptr.0, &self.id)
        }
    }

    impl<T> Arena<T> for CheckedArena<T> {
        fn get(&self, ptr: &Self::Ptr) -> Option<&T> {
            if unsafe { !self.contains_unchecked(ptr) } {
                None
            } else {
                self.map.get(&ptr.1)
            }
        }

        fn get_mut(&mut self, ptr: &Self::Ptr) -> Option<&mut T> {
            if unsafe { !self.contains_unchecked(ptr) } {
                None
            } else {
                self.map.get_mut(&ptr.1)
            }
        }

        fn remove(&mut self, ptr: &Self::Ptr) -> Option<T> {
            if unsafe { !self.contains_unchecked(ptr) } {
                None
            } else {
                self.map.remove(&ptr.1)
            }
        }
    }

    #[test]
    fn test1() {
        test_common(&mut CheckedArena::new());
    }

    #[test]
    fn test2() {
        let mut arena1 = CheckedArena::new();
        let mut arena2 = CheckedArena::new();
        let p1 = arena1.insert("twi");
        let p2 = arena1.insert("aj");
        let p3 = arena2.insert("r");

        unsafe {
            assert!(arena1.contains_unchecked(&p1));
            assert!(arena1.contains_unchecked(&p2));
            assert!(arena2.contains_unchecked(&p3));

            assert!(!arena2.contains_unchecked(&p1));
            assert!(!arena2.contains_unchecked(&p2));
            assert!(!arena1.contains_unchecked(&p3));

            assert_eq!(arena1.get_unchecked(&p1), &"twi");
            assert_eq!(arena1.get_unchecked_mut(&p2), &"aj");

            *arena1.get_unchecked_mut(&p2) = "flutter";

            assert_eq!(&arena1.remove_unchecked(&p1), &"twi");
            assert_eq!(&arena1.remove_unchecked(&p2), &"flutter");
        }
    }
}

pub use self::checked::CheckedArena;

/// Adds a `Vec`-based pool to any memory arena for faster reallocation.
pub mod pooled {
    use super::*;
    use std::marker::PhantomData;
    use std::mem::{ManuallyDrop, uninitialized};
    use std::ptr::read;

    /// Adds a vacant entry pool to any memory arena for faster reallocation.
    #[derive(Debug)]
    pub struct PooledArena<T, A, P>
    where
        A: UnsafeArena<Entry<T, P>, Ptr = P>,
        P: Clone + Default + PartialEq + Eq + fmt::Debug,
    {
        inner: A,
        first_vacant: Option<P>,
        _phantom: PhantomData<T>,
    }

    #[derive(Debug)]
    pub struct Entry<T, P> {
        data: ManuallyDrop<T>,
        occupied: bool,
        next: Option<P>,
    }

    impl<T, P> Drop for Entry<T, P> {
        fn drop(&mut self) {
            if self.occupied {
                unsafe {
                    ManuallyDrop::drop(&mut self.data);
                }
            }
        }
    }

    impl<T, A, P> PooledArena<T, A, P>
    where
        A: UnsafeArena<Entry<T, P>, Ptr = P>,
        P: Clone + Default + PartialEq + Eq + fmt::Debug,
    {
        /// Construct a `PooledArena`.
        pub fn new(inner: A) -> Self {
            Self::with_capacity(inner, 0)
        }

        /// Construct a `PooledArena` with the specified number of pre-allocated
        /// entries.
        pub fn with_capacity(inner: A, capacity: usize) -> Self {
            let mut arena = Self {
                inner,
                first_vacant: None,
                _phantom: PhantomData,
            };

            for _ in 0..capacity {
                let p = arena.inner.insert(Entry {
                    data: unsafe { uninitialized() },
                    occupied: false,
                    next: arena.first_vacant.take(),
                });
                arena.first_vacant = Some(p);
            }

            arena
        }

        /// Discard all vacant entries.
        pub fn purge(&mut self) {
            while let Some(p) = self.first_vacant.take() {
                let mut e = unsafe { self.inner.remove_unchecked(&p) };

                // Skip `T::drop()` because we know it is a vacant entry.
                // We can't just `forget(e)` because `P` might be `Drop`.
                debug_assert!(!e.occupied);
                e.occupied = false;
            }
        }
    }

    impl<T, A, P> UnsafeArena<T> for PooledArena<T, A, P>
    where
        A: UnsafeArena<Entry<T, P>, Ptr = P>,
        P: Clone + Default + PartialEq + Eq + fmt::Debug,
    {
        type Ptr = A::Ptr;

        fn insert(&mut self, x: T) -> Self::Ptr {
            if let Some(ptr) = self.first_vacant.take() {
                let ent = unsafe { self.inner.get_unchecked_mut(&ptr) };

                debug_assert!(!ent.occupied);

                ent.occupied = true;
                ent.data = ManuallyDrop::new(x);

                self.first_vacant = ent.next.take();

                ptr
            } else {
                self.inner.insert(Entry {
                    data: ManuallyDrop::new(x),
                    occupied: true,
                    next: None,
                })
            }
        }

        unsafe fn get_unchecked(&self, ptr: &Self::Ptr) -> &T {
            debug_assert!(self.inner.get_unchecked(ptr).occupied);
            &*self.inner.get_unchecked(ptr).data
        }

        unsafe fn get_unchecked_mut(&mut self, ptr: &Self::Ptr) -> &mut T {
            debug_assert!(self.inner.get_unchecked(ptr).occupied);
            &mut *self.inner.get_unchecked_mut(ptr).data
        }

        unsafe fn remove_unchecked(&mut self, ptr: &Self::Ptr) -> T {
            let entry = self.inner.get_unchecked_mut(ptr);
            debug_assert!(entry.occupied);

            let value = read(&*entry.data);
            entry.occupied = false;
            entry.next = self.first_vacant.take();

            self.first_vacant = Some(ptr.clone());

            value
        }
    }

    impl<T, A, P> UnsafeArenaWithMembershipCheck<T>
        for PooledArena<T, A, P>
    where
        A: UnsafeArena<Entry<T, P>, Ptr = P> + UnsafeArenaWithMembershipCheck<Entry<T, P>>,
        P: Clone + Default + PartialEq + Eq + fmt::Debug,
    {
        unsafe fn contains_unchecked(&self, ptr: &Self::Ptr) -> bool {
            self.inner.contains_unchecked(ptr)
        }
    }

    impl<T, A, P> Arena<T> for PooledArena<T, A, P>
    where
        A: UnsafeArena<Entry<T, P>, Ptr = P>
            + Arena<Entry<T, P>>,
        P: Clone + Default + PartialEq + Eq + fmt::Debug,
    {
        fn get(&self, ptr: &Self::Ptr) -> Option<&T> {
            self.inner.get(ptr).map(|x| {
                debug_assert!(x.occupied);
                &*x.data
            })
        }

        fn get_mut(&mut self, ptr: &Self::Ptr) -> Option<&mut T> {
            self.inner.get_mut(ptr).map(|x| {
                debug_assert!(x.occupied);
                &mut *x.data
            })
        }

        fn remove(&mut self, ptr: &Self::Ptr) -> Option<T> {
            if let Some(r) = self.inner.get_mut(ptr) {
                debug_assert!(r.occupied);

                let value = unsafe { read(&*r.data) };
                r.occupied = false;
                r.next = self.first_vacant.take();

                self.first_vacant = Some(ptr.clone());

                Some(value)
            } else {
                None
            }
        }
    }

    #[test]
    fn test1() {
        test_common(&mut PooledArena::new(CheckedArena::new()));
    }

    #[test]
    fn test2() {
        let mut arena = PooledArena::new(CheckedArena::new());

        for _ in 0..2 {
            let p1 = arena.insert("twi");
            let p2 = arena.insert("aj");

            unsafe {
                assert!(arena.contains_unchecked(&p1));
                assert!(arena.contains_unchecked(&p2));
            }

            assert_eq!(arena.get(&p1), Some(&"twi"));
            assert_eq!(arena.get_mut(&p2), Some(&mut "aj"));

            *arena.get_mut(&p2).unwrap() = "flutter";

            assert_eq!(arena.remove(&p1), Some("twi"));
            assert_eq!(arena.remove(&p2), Some("flutter"));
        }

        arena.purge();
    }
}

pub use self::pooled::PooledArena;
