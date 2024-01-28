.. SPDX-License-Identifier: GPL-2.0
.. highlight:: rust

Examples
========

Unsound APIs
------------

Simple Unsound Function
***********************
::

    struct Data {
        a: usize,
    }

    fn access_a(data: *mut Data) -> usize {
        unsafe { (*data).a }
    }

One would normally call this function as follows, which does not trigger UB::

    fn main() {
        let mut d = Data { a: 42 };
        println!("{}", access_a(&mut d));
    }

However, a caller could also call it like this, which triggers UB using only safe code::

    fn main() {
        println!("{}", access_a(core::ptr::null_mut()));
    }

And this would result in a dereference of a null pointer.


Sound ``unsafe`` Code
---------------------

The Importance of the API Boundary
**********************************

Is the following API sound?::

    fn foo(r: &mut u32) {
        let ptr: *mut u32 = r;
        let val;
        unsafe {
            val = *ptr;
            *ptr = 0;
        }
    }

It better be sound, but one could argue that it is unsound, since one could replace the ptr
initialization by ``ptr = core::ptr::null_mut()``::

    fn foo(r: &mut u32) {
        let ptr: *mut u32 = core::ptr::null_mut();
        let val;
        unsafe {
            val = *ptr;
            *ptr = 0;
        }
    }

But this modification is not allowed, since it goes beyond the API boundary of ``foo``. This way
any ``unsafe`` code that relies on surrounding safe code could be shown to be unsound. Instead one
should only consider safe code using the API, in this case, there is no way to make the code
incorrect, since a reference is always valid to dereference during its lifetime.
