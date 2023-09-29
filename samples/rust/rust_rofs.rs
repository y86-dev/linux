// SPDX-License-Identifier: GPL-2.0

//! Rust read-only file system sample.

use kernel::fs::sb;
use kernel::prelude::*;
use kernel::{c_str, fs};

kernel::module_fs! {
    type: RoFs,
    name: "rust_rofs",
    author: "Rust for Linux Contributors",
    description: "Rust read-only file system sample",
    license: "GPL",
}

struct RoFs;
impl fs::FileSystem for RoFs {
    const NAME: &'static CStr = c_str!("rust_rofs");

    fn fill_super(sb: &mut sb::SuperBlock<Self>) -> Result {
        sb.set_magic(0x52555354);
        Ok(())
    }
}
