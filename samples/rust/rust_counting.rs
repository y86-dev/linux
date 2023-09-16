// SPDX-License-Identifier: GPL-2.0

#![allow(dead_code)]

//! Rust counting example for Kangrejos

use kernel::{
    init::{self, PinnedDrop},
    new_mutex,
    prelude::*,
    sync::Mutex,
};

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

#[pin_data(PinnedDrop)]
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

#[pinned_drop]
impl PinnedDrop for MonitoredBuffer {
    fn drop(self: Pin<&mut Self>) {
        pr_info!(
            "Monitored Buffer was read {} times and written to {} times.",
            self.read.value(),
            self.write.value()
        )
    }
}

#[derive(Zeroable, Debug)]
struct LotsOfData {
    a_buf: [u8; 128],
    b_buf: [u8; 256],
    mode: i32,
    count: usize,
    data: *mut u8,
    len: usize,
}

impl kernel::Module for RustCounting {
    fn init(_module: &'static ThisModule) -> Result<Self> {
        let data = Box::init(init!(LotsOfData {
            mode: 8,
            ..Zeroable::zeroed()
        }));
        pr_info!("{data:?}");
        Ok(Self)
    }
}
