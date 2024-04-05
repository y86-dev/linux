.. SPDX-License-Identifier: GPL-2.0
.. highlight:: rust

====================
Rust Safety Standard
====================

Safe Rust code cannot have memory related bugs. This is a guarantee by the Rust compiler. Of course
it is not without caveats: no compiler bugs, no bugs in the specification etc. But the possibly most
important caveat is that of ``unsafe`` code. ``unsafe`` code needs to follow certain rules in order
for safe code to enjoy the no-memory-bugs privilege. A simple example of such a rule is that
references must be valid for the duration of their lifetime. If any rule is violated, it can lead
to undefined behavior even in safe code! The term undefined behavior in Rust has a lot stricter
meaning than in C or C++: UB in Rust is totally forbidden. In C one might rely on the compiler
implementation to ensure correct code generation, but that is not the case for Rust. You can read
more about UB in Rust
`here <https://doc.rust-lang.org/reference/behavior-considered-undefined.html>`_.

If ``unsafe`` code makes our life this difficult, one might ask the question "why do we even need
it?" and the answer to that is that it gives users an escape hatch to do things that the compiler
normally forbids. ``unsafe`` code is a tool that enables programmers to write more performant code,
or code that interacts with hardware or C. These things are particularly important in kernel
development.

The most effective way to prevent issues in ``unsafe`` code is to just not write ``unsafe`` code in
the first place. That is why minimizing the amount of ``unsafe`` code is very important. For
example, drivers are not allowed to directly interface with the C side. Instead of directly
communicating with C functions, they interact with Rust abstractions. This concentrates the usage
of ``unsafe`` code, making it easy to fix issues, since only the abstraction needs to be fixed.
Abstractions also allow taking advantage of other Rust language features. Read more in
:ref:`rust-abstractions`.

Since the correctness of the abstractions is integral for safe code to also be correct, extra effort
is expended to get them right. Part of that is good safety documentation.

The goals of safety documentation are:

* reduce the amount of bugs in ``unsafe`` code,
* help readers know why a given piece of ``unsafe`` code is sound,
* help writers write ``unsafe`` code with confidence,
* simplify the work of reviewers.

This document standardizes safety documentation. The necessity for this is simple, only a common
language that all parties understand is effective at the above task. We want to avoid
misunderstandings in safety related matters. An additional benefit is that programmers will not have
to ponder for the correct phrasing, since they can find it here.

This document assumes that the reader is familiar with Rust code and understands the most important
concepts of ``unsafe`` Rust. It is recommended that the reader has read the `Rust Book`_. Since this
document is about safety documentation, almost all examples are going to contain ``unsafe`` code.
For this reason it is also recommended to read the `Rustonomicon`_, one of the best resources on
``unsafe`` code.

.. _Rustonomicon: https://doc.rust-lang.org/nomicon/index.html
.. _Rust Book: https://doc.rust-lang.org/stable/book/

If you need help coming up with an abstraction, or with writing the safety documentation for an
abstraction, feel free to reach out on `zulip`_ or the `list`_.

.. _zulip: https://rust-for-linux.zulipchat.com
.. _list: https://lore.kernel.org/rust-for-linux

Soundness
=========

``unsafe`` operations (e.g. ``unsafe`` functions, dereferencing raw pointers etc.) have certain
conditions that need to be fulfilled in order for the operation to not be UB.
To evaluate if the ``unsafe`` code usage is correct, one needs to consider the API that wraps said
``unsafe`` code. If under all possible safe uses of the API, the conditions for the ``unsafe``
operation are fulfilled, the API is *sound*. Otherwise it is *unsound*. Here is a simple example::

    pub struct Data {
        a: usize,
    }

    pub fn access_a(data: *mut Data) -> usize {
        unsafe { (*data).a }
    }

    fn main() {
        let mut d = Data { a: 42 };
        println!("{}", access_a(&mut d));
    }

While this example has no UB, the function ``access_a`` is unsound. This is because one could just
write the following safe usage::

    println!("{}", access_a(core::ptr::null_mut()));

And this would result in a dereference of a null pointer.

In its essence, a sound API means that if someone only writes safe code, they can never encounter UB
even if they call safe code that calls ``unsafe`` code behind the scenes.

For more examples of unsound code see examples.rst.

Because unsoundness issues have the potential for allowing safe code to experience UB, they are
treated similarly to real UB. Their fixes should also be included in the stable tree.

Safety Documentation
====================

No matter how hard one tries to remove ``unsafe`` code, it is impossible to completely get rid of it
in the Kernel. There are things that are impossible for safe code. For example interacting with the
C side. So one can never be completely sure that there are no memory issues lurking somewhere.

This is where safety documentation helps: it meticulously documents the various requirements and
justifications for every line of ``unsafe`` code. That way the risk of writing unsound ``unsafe``
code is reduced drastically.

The gist of the idea is this: every ``unsafe`` operation documents its requirements and every
location that uses an ``unsafe`` operation documents for every requirement a justification why they
are fulfilled. If now all requirements and justifications are correct, then there can only be sound
``unsafe`` code. Reducing the global problem of correctness of the whole kernel to the correctness
of each and every ``unsafe`` code block makes it a local problem. Local problems are a lot easier to
handle, since each instance can be fixed/reviewed independently.

The ``unsafe`` keywords has two different meanings depending on the context it is used in:

* granting access to an unchecked operation,
* declaring that something is an unchecked operation.

In both cases we have to add safety documentation. In the first case, we have to justify why we can
always guarantee that the requirements of the unchecked operation are fulfilled. In the second case,
we have to list the requirements that have to be fulfilled for the operation to be sound.

In the following sections we will go over each location where ``unsafe`` can be used.

.. _unsafe-Functions:

``unsafe`` Functions
--------------------

``unsafe`` on function declarations is used to state that this function has special requirements
that callers have to ensure when calling the function::

    unsafe fn foo() {
        // ...
    }

These requirements are called the safety requirements of the function. These requirements can take
any shape and range from simple requirements like "``ptr_arg`` is valid" (``ptr_arg`` refers to some
argument with the type matching ``*mut T`` or ``*const T``) to more complex requirements like
"``ptr`` must be valid, point to a ``NUL``-terminated C string, and it must be valid for at least
``'a``. While the returned value is alive, the memory at ``ptr`` must not be mutated.".

The safety requirements have to be documented in the so called safety section::

    /// <oneline description of the function>
    ///
    /// <full description of the function>
    ///
    /// # Safety
    ///
    /// <safety requirements>
    unsafe fn foo() {
        // ...
    }

.. _unsafe-Blocks:

``unsafe`` Blocks
-----------------

``unsafe`` code blocks are used to call ``unsafe`` functions and perform built-in ``unsafe``
operations such as dereferencing a raw pointer::

    unsafe { foo() };

In order to ensure that all safety requirements of ``unsafe`` operations are upheld, a safety
comment is mandatory for all ``unsafe`` blocks. This safety comment needs to provide a correct
justification for every safety requirements of every operation within the block::

    // SAFETY: <justifications>
    unsafe { foo() };

For transparency it is best practice to have only a single ``unsafe`` operation per ``unsafe``
block, since then it is more clear what the justifications are trying to justify. Safe operations
should not be included in the block, since it adds confusion as to which operation is the ``unsafe``
one. In certain cases however it makes it easier to understand if there is only a single ``unsafe``
block. For example::

    // SAFETY: `ptr` is valid for writes.
    unsafe {
        (*ptr).field1 = 42;
        (*ptr).field2 = 24;
        (*ptr).field3 = 2442;
    }

In this case it is more readable to not split the block into multiple parts.

``unsafe`` Traits
-----------------

When ``unsafe`` is on a ``trait`` declaration::

    unsafe trait Foo {}

The ``trait`` has special requirements for implementing it. Similar to :ref:`unsafe-Functions`, these
are called safety requirements and need to be documented in the same way::

    /// <oneline description of the trait>
    ///
    /// <full description of the trait>
    ///
    /// # Safety
    ///
    /// <safety requirements>
    unsafe trait Foo {}

``unsafe`` Impls
----------------

When ``unsafe`` is on an ``impl`` item::

    unsafe impl Foo for Bar {}

The ``Foo`` ``trait`` has to be ``unsafe`` and its safety requirements need to be justified
similarly to :ref:`unsafe-Blocks`::

    // SAFETY: <justification>
    unsafe impl Foo for Bar {}

Guarantees
==========

Functions are also allowed to declare certain guarantees that ``unsafe`` code is able to rely upon.
For example when returning a raw pointer, a common guarantee would be to state that it is valid. See
guarantee.rst for more info. Importantly, guarantees can also be given by safe functions.

Type Invariants
---------------

Type invariants are a kind of guarantee. Like their name suggests, they always hold (invariant --
never changing). They can only be specified on ``struct``, ``enum`` or ``union`` types. See
type-invariants.rst for more info.

General Rules
=============

The general thought behind all rules in the safety standard is that everything that cannot be
statically checked by the Rust compiler and guaranteed, needs to be either checked at runtime, or
have to have safety documentation.

The Kernel uses ``deny(unsafe_op_in_unsafe_fn)``, disallowing ``unsafe`` operations to be contained
in ``unsafe`` functions without a surrounding ``unsafe`` block, an example violating that would be::

    unsafe fn zero_ptr(ptr: *mut u32) {
        *ptr = 0;
    }

Denying code like this is becoming the default in modern editions of the Rust language. It is also
easy to see why we would want to deny such code: where would we put the ``SAFETY`` comment for the
pointer dereference?

Further Pages
-------------

.. toctree::
   :maxdepth: 1

   examples
   guarantee
   type-invariants

.. only::  subproject and html

   Indices
   =======

   * :ref:`genindex`
