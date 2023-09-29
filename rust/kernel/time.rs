// SPDX-License-Identifier: GPL-2.0

//! Time related primitives.
//!
//! This module contains the kernel APIs related to time and timers that
//! have been ported or wrapped for usage by Rust code in the kernel.

use crate::{bindings, error::code::*, error::Result};

/// The time unit of Linux kernel. One jiffy equals (1/HZ) second.
pub type Jiffies = core::ffi::c_ulong;

/// The millisecond time unit.
pub type Msecs = core::ffi::c_uint;

/// Converts milliseconds to jiffies.
#[inline]
pub fn msecs_to_jiffies(msecs: Msecs) -> Jiffies {
    // SAFETY: The `__msecs_to_jiffies` function is always safe to call no
    // matter what the argument is.
    unsafe { bindings::__msecs_to_jiffies(msecs) }
}

/// A [`Timespec`] instance at the Unix epoch.
pub const UNIX_EPOCH: Timespec = Timespec {
    t: bindings::timespec64 {
        tv_sec: 0,
        tv_nsec: 0,
    },
};

/// A timestamp.
#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct Timespec {
    t: bindings::timespec64,
}

impl Timespec {
    /// Creates a new timestamp.
    ///
    /// `sec` is the number of seconds since the Unix epoch. `nsec` is the number of nanoseconds
    /// within that second.
    pub fn new(sec: u64, nsec: u32) -> Result<Self> {
        if nsec >= 1000000000 {
            return Err(EDOM);
        }

        Ok(Self {
            t: bindings::timespec64 {
                tv_sec: sec.try_into()?,
                tv_nsec: nsec.into(),
            },
        })
    }
}

impl From<Timespec> for bindings::timespec64 {
    fn from(v: Timespec) -> Self {
        v.t
    }
}
