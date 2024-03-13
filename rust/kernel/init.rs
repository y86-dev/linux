// SPDX-License-Identifier: GPL-2.0

//! Extension to the `pinned_init` crate.
//!
//! Most `struct`s from the [`sync`] module need to be pinned, because they contain self-referential
//! `struct`s from C. [Pinning][pinning] is Rust's way of ensuring data does not move.
//!
//! [`sync`]: crate::sync
//! [pinning]: https://doc.rust-lang.org/std/pin/index.html
