// SPDX-License-Identifier: GPL-2.0

//! Extensions to [`Box`] for fallible allocations.

use super::{AllocError, Flags};
use alloc::boxed::Box;
use core::mem::MaybeUninit;

/// Extensions to [`Box`].
pub trait BoxExt<T>: Sized {
    /// Allocates a new box.
    ///
    /// The allocation may fail, in which case an error is returned.
    fn new(x: T, flags: Flags) -> Result<Self, AllocError>;

    /// Allocates a new uninitialised box.
    ///
    /// The allocation may fail, in which case an error is returned.
    fn new_uninit(flags: Flags) -> Result<Box<MaybeUninit<T>>, AllocError>;

    /// Allocates a new uninitialised box of a slice.
    ///
    /// The allocation may fail, in which case an error is returned.
    fn new_uninit_slice(len: usize, flags: Flags) -> Result<Box<[MaybeUninit<T>]>, AllocError>;

    /// Allocates a new box with a slice.
    ///
    /// All elements are initialised with clones of `value`.
    ///
    /// The allocation may fail, in which case an error is returned.
    fn new_slice(len: usize, value: T, flags: Flags) -> Result<Box<[T]>, AllocError>
    where
        T: Clone;
}

#[cfg(not(any(test, testlib)))]
fn allocate<T>(count: usize, flags: Flags) -> Result<*mut MaybeUninit<T>, AllocError> {
    if core::mem::size_of::<MaybeUninit<T>>() == 0 {
        Ok(core::ptr::NonNull::dangling().as_ptr())
    } else {
        let layout = core::alloc::Layout::array::<MaybeUninit<T>>(count).map_err(|_| AllocError)?;

        // SAFETY: Memory is being allocated (first arg is null). The only other source of
        // safety issues is sleeping in atomic context, which is addressed by klint. Lastly,
        // the type is not a ZST (checked above).
        let ptr =
            unsafe { super::allocator::krealloc_aligned(core::ptr::null_mut(), layout, flags) };
        if ptr.is_null() {
            Err(AllocError)
        } else {
            Ok(ptr.cast::<MaybeUninit<T>>())
        }
    }
}

impl<T> BoxExt<T> for Box<T> {
    fn new(x: T, flags: Flags) -> Result<Self, AllocError> {
        let b = <Self as BoxExt<_>>::new_uninit(flags)?;
        Ok(Box::write(b, x))
    }

    #[cfg(any(test, testlib))]
    fn new_uninit(_flags: Flags) -> Result<Box<MaybeUninit<T>>, AllocError> {
        Ok(Box::new_uninit())
    }

    #[cfg(not(any(test, testlib)))]
    fn new_uninit(flags: Flags) -> Result<Box<MaybeUninit<T>>, AllocError> {
        let ptr = allocate(1, flags)?;

        // SAFETY: For non-zero-sized types, we allocate above using the global allocator. For
        // zero-sized types, we use `NonNull::dangling`.
        Ok(unsafe { Box::from_raw(ptr) })
    }

    #[cfg(any(test, testlib))]
    fn new_uninit_slice(len: usize, _flags: Flags) -> Result<Box<[MaybeUninit<T>]>, AllocError> {
        Ok(Box::new_uninit_slice(len))
    }

    #[cfg(not(any(test, testlib)))]
    fn new_uninit_slice(len: usize, flags: Flags) -> Result<Box<[MaybeUninit<T>]>, AllocError> {
        let ptr = allocate(len, flags)?;
        let sptr = core::ptr::slice_from_raw_parts_mut(ptr, len);

        // SAFETY: For non-zero-sized types, we allocate above using the global allocator. For
        // zero-sized types, we use `NonNull::dangling`.
        Ok(unsafe { Box::from_raw(sptr) })
    }

    fn new_slice(len: usize, value: T, flags: Flags) -> Result<Box<[T]>, AllocError>
    where
        T: Clone,
    {
        let mut b = Self::new_uninit_slice(len, flags)?;
        for v in b.iter_mut() {
            v.write(value.clone());
        }
        // SAFETY: We just initialised all items above.
        Ok(unsafe { b.assume_init() })
    }
}
