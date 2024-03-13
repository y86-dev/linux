// SPDX-License-Identifier: GPL-2.0

//! Extension to the `pinned_init` crate.
//!
//! Most `struct`s from the [`sync`] module need to be pinned, because they contain self-referential
//! `struct`s from C. [Pinning][pinning] is Rust's way of ensuring data does not move.
//!
//! # [`Opaque`]
//!
//! For the special case where initializing a field is a single FFI-function call that cannot fail,
//! there exist the helper function [`Opaque::ffi_init`]. This function initialize a single
//! [`Opaque`] field by just delegating to the supplied closure. You can use these in combination
//! with [`pin_init!`].
//!
//! # Examples
//!
//! ```rust
//! # #![allow(clippy::disallowed_names)]
//! use kernel::{types::Opaque, pinned_init::pin_init_from_closure};
//! #[repr(C)]
//! struct RawFoo([u8; 16]);
//! extern {
//!     fn init_foo(_: *mut RawFoo);
//! }
//!
//! #[pin_data]
//! struct Foo {
//!     #[pin]
//!     raw: Opaque<RawFoo>,
//! }
//!
//! impl Foo {
//!     fn setup(self: Pin<&mut Self>) {
//!         pr_info!("Setting up foo");
//!     }
//! }
//!
//! let foo = pin_init!(Foo {
//!     raw <- unsafe {
//!         Opaque::ffi_init(|s| {
//!             init_foo(s);
//!         })
//!     },
//! }).pin_chain(|foo| {
//!     foo.setup();
//!     Ok(())
//! });
//! ```
//!
//! ```rust
//! # #![allow(unreachable_pub, clippy::disallowed_names)]
//! use kernel::{prelude::*, init, types::Opaque};
//! use core::{ptr::addr_of_mut, marker::PhantomPinned, pin::Pin};
//! # mod bindings {
//! #     #![allow(non_camel_case_types)]
//! #     pub struct foo;
//! #     pub unsafe fn init_foo(_ptr: *mut foo) {}
//! #     pub unsafe fn destroy_foo(_ptr: *mut foo) {}
//! #     pub unsafe fn enable_foo(_ptr: *mut foo, _flags: u32) -> i32 { 0 }
//! # }
//! # // `Error::from_errno` is `pub(crate)` in the `kernel` crate, thus provide a workaround.
//! # trait FromErrno {
//! #     fn from_errno(errno: core::ffi::c_int) -> Error {
//! #         // Dummy error that can be constructed outside the `kernel` crate.
//! #         Error::from(core::fmt::Error)
//! #     }
//! # }
//! # impl FromErrno for Error {}
//! /// # Invariants
//! ///
//! /// `foo` is always initialized
//! #[pin_data(PinnedDrop)]
//! pub struct RawFoo {
//!     #[pin]
//!     foo: Opaque<bindings::foo>,
//!     #[pin]
//!     _p: PhantomPinned,
//! }
//!
//! impl RawFoo {
//!     pub fn new(flags: u32) -> impl PinInit<Self, Error> {
//!         // SAFETY:
//!         // - when the closure returns `Ok(())`, then it has successfully initialized and
//!         //   enabled `foo`,
//!         // - when it returns `Err(e)`, then it has cleaned up before
//!         unsafe {
//!             init::pin_init_from_closure(move |slot: *mut Self| {
//!                 // `slot` contains uninit memory, avoid creating a reference.
//!                 let foo = addr_of_mut!((*slot).foo);
//!
//!                 // Initialize the `foo`
//!                 bindings::init_foo(Opaque::raw_get(foo));
//!
//!                 // Try to enable it.
//!                 let err = bindings::enable_foo(Opaque::raw_get(foo), flags);
//!                 if err != 0 {
//!                     // Enabling has failed, first clean up the foo and then return the error.
//!                     bindings::destroy_foo(Opaque::raw_get(foo));
//!                     return Err(Error::from_errno(err));
//!                 }
//!
//!                 // All fields of `RawFoo` have been initialized, since `_p` is a ZST.
//!                 Ok(())
//!             })
//!         }
//!     }
//! }
//!
//! #[pinned_drop]
//! impl PinnedDrop for RawFoo {
//!     fn drop(self: Pin<&mut Self>) {
//!         // SAFETY: Since `foo` is initialized, destroying is safe.
//!         unsafe { bindings::destroy_foo(self.foo.get()) };
//!     }
//! }
//! ```
//!
//! [`pin_init!`]: kernel::pin_init
//! [`sync`]: crate::sync
//! [pinning]: https://doc.rust-lang.org/std/pin/index.html
//! [`Opaque`]: kernel::types::Opaque
//! [`Opaque::ffi_init`]: kernel::types::Opaque::ffi_init

use core::pin::Pin;

use crate::pinned_init::{self, InPlaceInit, Init, PinInit, Zeroable};
use crate::{
    error::{self, Error},
    types::Opaque,
};

/// Extension trait of [`InPlaceInit<T>`] allowing better interoperability with the custom
/// [`Error`] type.
pub trait InPlaceInitExt<T>: InPlaceInit<T> {
    /// Use the given pin-initializer to pin-initialize a `T` inside of a new smart pointer of this
    /// type.
    ///
    /// If `T: !Unpin` it will not be able to move afterwards.
    fn pin_init<E>(init: impl PinInit<T, E>) -> error::Result<Pin<Self>>
    where
        Error: From<E>,
    {
        // SAFETY: We delegate to `init` and only change the error type.
        let init = unsafe {
            pinned_init::pin_init_from_closure(|slot| {
                init.__pinned_init(slot).map_err(|e| Error::from(e))
            })
        };
        Self::try_pin_init(init)
    }

    /// Use the given initializer to in-place initialize a `T`.
    fn init<E>(init: impl Init<T, E>) -> error::Result<Self>
    where
        Error: From<E>,
    {
        // SAFETY: We delegate to `init` and only change the error type.
        let init = unsafe {
            pinned_init::init_from_closure(|slot| {
                init.__pinned_init(slot).map_err(|e| Error::from(e))
            })
        };
        Self::try_init(init)
    }
}

impl<T, I: InPlaceInit<T>> InPlaceInitExt<T> for I {}

// SAFETY: `Opaque` wraps a `MaybeUninit<T>` which allows any bit pattern.
unsafe impl<T> Zeroable for Opaque<T> {}
