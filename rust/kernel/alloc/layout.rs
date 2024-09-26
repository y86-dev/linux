// SPDX-License-Identifier: GPL-2.0

use core::{alloc::Layout, marker::PhantomData};

/// Error when constructing an [`ArrayLayout`].
pub struct LayoutError;

/// A layout for an array `[T; n]`.
///
/// # Invariants
///
/// - `len * size_of::<T>() <= isize::MAX`
pub struct ArrayLayout<T> {
    len: usize,
    _phantom: PhantomData<fn() -> T>,
}

impl<T> Clone for ArrayLayout<T> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<T> Copy for ArrayLayout<T> {}

const ISIZE_MAX: usize = isize::MAX as usize;

impl<T> ArrayLayout<T> {
    /// Creates a new layout for `[T; 0]`.
    pub fn empty() -> Self {
        Self {
            len: 0,
            _phantom: PhantomData,
        }
    }

    /// Creates a new layout for `[T; len]`.
    ///
    /// # Errors
    ///
    /// When `len * size_of::<T>()` overflows or when `len * size_of::<T>() > isize::MAX`.
    pub fn new(len: usize) -> Result<Self, LayoutError> {
        match len.checked_mul(size_of::<T>()) {
            Some(len) if len <= ISIZE_MAX => {
                // INVARIANT: we checked above that `len * size_of::<T>() <= isize::MAX`
                Ok(Self {
                    len,
                    _phantom: PhantomData,
                })
            }
            _ => Err(LayoutError),
        }
    }

    /// Returns the number of array elements represented by this layout.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` when no array elements are represented by this layout.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

impl<T> From<ArrayLayout<T>> for Layout {
    fn from(value: ArrayLayout<T>) -> Self {
        let res = Layout::array::<T>(value.len);
        // SAFETY: by the type invariant of `ArrayLayout` we have
        // `len * size_of::<T>() <= isize::MAX` and thus the result must be `Ok`.
        unsafe { res.unwrap_unchecked() }
    }
}
