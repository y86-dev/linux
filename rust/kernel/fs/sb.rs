// SPDX-License-Identifier: GPL-2.0

//! File system super blocks.
//!
//! This module allows Rust code to use superblocks.
//!
//! C headers: [`include/linux/fs.h`](srctree/include/linux/fs.h)

use super::FileSystem;
use crate::{bindings, types::Opaque};
use core::marker::PhantomData;

/// A file system super block.
///
/// Wraps the kernel's `struct super_block`.
#[repr(transparent)]
pub struct SuperBlock<T: FileSystem + ?Sized>(
    pub(crate) Opaque<bindings::super_block>,
    PhantomData<T>,
);

impl<T: FileSystem + ?Sized> SuperBlock<T> {
    /// Creates a new superblock reference from the given raw pointer.
    ///
    /// # Safety
    ///
    /// Callers must ensure that:
    ///
    /// * `ptr` is valid and remains so for the lifetime of the returned object.
    /// * `ptr` has the correct file system type, or `T` is [`super::UnspecifiedFS`].
    pub(crate) unsafe fn from_raw<'a>(ptr: *mut bindings::super_block) -> &'a Self {
        // SAFETY: The safety requirements guarantee that the cast below is ok.
        unsafe { &*ptr.cast::<Self>() }
    }

    /// Creates a new superblock mutable reference from the given raw pointer.
    ///
    /// # Safety
    ///
    /// Callers must ensure that:
    ///
    /// * `ptr` is valid and remains so for the lifetime of the returned object.
    /// * `ptr` has the correct file system type, or `T` is [`super::UnspecifiedFS`].
    /// * `ptr` is the only active pointer to the superblock.
    pub(crate) unsafe fn from_raw_mut<'a>(ptr: *mut bindings::super_block) -> &'a mut Self {
        // SAFETY: The safety requirements guarantee that the cast below is ok.
        unsafe { &mut *ptr.cast::<Self>() }
    }

    /// Returns whether the superblock is mounted in read-only mode.
    pub fn rdonly(&self) -> bool {
        // SAFETY: `s_flags` only changes during init, so it is safe to read it.
        unsafe { (*self.0.get()).s_flags & bindings::SB_RDONLY != 0 }
    }

    /// Sets the magic number of the superblock.
    pub fn set_magic(&mut self, magic: usize) -> &mut Self {
        // SAFETY: This is a new superblock that is being initialised, so it's ok to write to its
        // fields.
        unsafe { (*self.0.get()).s_magic = magic as core::ffi::c_ulong };
        self
    }
}
