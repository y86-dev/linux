// SPDX-License-Identifier: GPL-2.0

#![allow(dead_code)]

//! Rust counting example for Kangrejos

use kernel::{init, new_mutex, prelude::*, sync::Mutex};

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

#[pin_data]
struct MonitoredBuffer {
    #[pin]
    read: NamedCounter,
    #[pin]
    write: NamedCounter,
    buf: Box<[u8; 100_000]>,
}

impl MonitoredBuffer {
    fn new() -> impl PinInit<Self, Error> {
        try_pin_init!(Self {
            read <- NamedCounter::new("Read Counter", 0, i32::MAX),
            write <- NamedCounter::new("Write Counter", 0, i32::MAX),
            buf: Box::init(init::zeroed())?,
        })
    }

    fn set(&mut self, idx: usize, val: u8) {
        self.write.increment();
        self.buf[idx] = val;
    }

    fn get(&self, idx: usize) -> u8 {
        self.read.increment();
        self.buf[idx]
    }
}

impl kernel::Module for RustCounting {
    fn init(_module: &'static ThisModule) -> Result<Self> {
        Ok(Self)
    }
}
