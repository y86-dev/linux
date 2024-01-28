.. SPDX-License-Identifier: GPL-2.0
.. highlight:: rust

===================
Safety Requirements
===================

There are many different kinds of safety requirements. The simplest example is the validity of raw
pointers. But there is no limit to what they may require.

Safety requirements are listed in an unordered markdown list in the ``# Safety`` section on
``unsafe fn`` and ``unsafe trait`` items. Each list item should only contain a single requirement.
The items should not specify the same requirement multiple times, especially not by expressing it in
different terms.  The ``# Safety`` section should only consist of the list of safety requirements,
if there is additional information, it should be documented in a different section.

Common Safety Requirements
==========================

+------------------------+---------------------+---------------------------------------------------+
| Syntax                 | Meta Variables      | Meaning                                           |
|                        |                     |                                                   |
+========================+=====================+===================================================+
| ``ptr`` is valid for   |                     | Abbreviation for:                                 |
| reads and writes.      |                     |                                                   |
|                        | * ``ptr: *mut T``   | * ``ptr`` is valid for reads.                     |
|                        |                     | * ``ptr`` is valid for writes.                    |
+------------------------+---------------------+---------------------------------------------------+
| ``ptr`` is valid for   |                     | Abbreviation for:                                 |
| reads.                 |                     |                                                   |
|                        | * ``ptr: *const T`` | * ``ptr`` is valid for reads up to                |
|                        |                     |   ``size_of::<T>()`` bytes for the duration of    |
|                        |                     |   this function call.                             |
+------------------------+---------------------+---------------------------------------------------+
| ``ptr`` is valid for   |                     | Abbreviation for:                                 |
| writes.                |                     |                                                   |
|                        | * ``ptr: *mut T``   | * ``ptr`` is valid for writes up to               |
|                        |                     |   ``size_of::<T>()`` bytes for the duration of    |
|                        |                     |   this function call.                             |
+------------------------+---------------------+---------------------------------------------------+
| ``ptr`` is valid for   |                     | For the duration of ``'a``:                       |
| reads up to ``size``   |                     |                                                   |
| bytes for the duration | * ``ptr: *const T`` | * The pointer ``ptr`` is dereferenceable for      |
| of ``'a``.             | * ``size: usize``   |   ``size`` bytes: all bytes with offset           |
|                        |                     |   ``0..size`` have to be part of the same         |
|                        |                     |   allocated object and it has to be alive.        |
|                        |                     | * No concurrent write operation may occur to      |
|                        |                     |   ``ptr`` at any offset between ``0..size``.      |
|                        |                     | * The value at ``ptr`` is a valid instance of     |
|                        |                     |   the type ``T``.                                 |
|                        |                     |                                                   |
|                        |                     | Additionally ``ptr`` must be:                     |
|                        |                     |                                                   |
|                        |                     | * non-null,                                       |
|                        |                     | * aligned to ``align_of::<T>()`` i.e.             |
|                        |                     |   ``ptr.addr() % align_of::<T>() == 0``.          |
+------------------------+---------------------+---------------------------------------------------+
| ``ptr`` is valid for   |                     | For the duration of ``'a``:                       |
| writes up to ``size``  |                     |                                                   |
| bytes for the duration | * ``ptr: *mut T``   | * The pointer ``ptr`` is dereferenceable for      |
| of ``'a``.             | * ``size: usize``   |   ``size`` bytes: all bytes with offset           |
|                        |                     |   ``0..size`` have to be part of the same         |
|                        |                     |   allocated object and it has to be alive.        |
|                        |                     | * No concurrent read or write operation may occur |
|                        |                     |   to ``ptr`` at any offset between ``0..size``.   |
|                        |                     |                                                   |
|                        |                     | Additionally ``ptr`` must be:                     |
|                        |                     |                                                   |
|                        |                     | * non-null,                                       |
|                        |                     | * aligned to ``align_of::<T>()`` i.e.             |
|                        |                     |   ``ptr.addr() % align_of::<T>() == 0``.          |
+------------------------+---------------------+---------------------------------------------------+


Custom Safety Requirements
==========================

There are of course situations where the safety requirements listed above are insufficient. In that
case the author can try to come up with their own safety requirement wording and ask the reviewers
what they think. If the requirement is common enough, it should be added to the list above.
