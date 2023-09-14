// SPDX-License-Identifier: GPL-2.0

#![allow(dead_code)]

//! Rust counting example for Kangrejos

use kernel::{new_mutex, prelude::*, sync::Mutex};

module! {
    type: RustCounting,
    name: "rust_counting",
    author: "Benno Lossin",
    description: "Rust counting sample for Kangrejos",
    license: "GPL",
}

struct RustCounting;

#[pin_data]
struct NamedCounter {
    name: &'static str,
    #[pin]
    value: Mutex<(i32, i32)>,
}

impl NamedCounter {
    fn new(name: &'static str, cur_value: i32, max_value: i32) -> impl PinInit<Self> {
        pin_init!(Self {
            name,
            value <- new_mutex!((cur_value, max_value)),
        })
    }

    fn increment(&self) -> bool {
        let mut val = self.value.lock();
        val.0 += 1;
        val.0 >= val.1
    }

    fn value(&self) -> i32 {
        self.value.lock().0
    }

    fn set_max(&self, max_value: i32) {
        self.value.lock().1 = max_value;
    }
}

impl kernel::Module for RustCounting {
    fn init(_module: &'static ThisModule) -> Result<Self> {
        Ok(Self)
    }
}
