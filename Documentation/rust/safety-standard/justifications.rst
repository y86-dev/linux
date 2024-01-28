.. SPDX-License-Identifier: GPL-2.0
.. highlight:: rust

==============
Justifications
==============

Since there are so many different safety-requirements.rst, there are also many different ways to
justify them.

Justifications are listed in an unordered markdown list in the ``SAFETY`` comments on ``unsafe``
blocks and ``unsafe impl``. The order and elements of the list must match the list present in the
``# Safety`` section on the respective ``unsafe`` item (e.g. the function or the trait).

Common Justifications
=====================

In order to use the justifications from the table below, first repeat the safety requirement and
then write ``by <justification>`` where justification is from the table below.
If you need the conjunction of multiple justifications, then you just intersperse them with "and".

The term "goal safety requirement" is referring to the requirement that you are trying to justify.

+---------------------------+----------------------------------------------------------------------+
| Syntax                    | Meaning/Justified Safety Requirement                                 |
+===========================+======================================================================+
| function requirements     | The goal safety requirement is provided by the surrounding function, |
|                           | as it also has it (or a stronger statement) as a safety requirement. |
+---------------------------+----------------------------------------------------------------------+
| type invariant of ``T``   | The given safety requirement is provided by the type invariant of    |
|                           | ``T``, as it also has it (or a stronger statement) as a type         |
|                           | invariant.                                                           |
+---------------------------+----------------------------------------------------------------------+
| reference validity        | When turning a (mutable) reference into a pointer, that pointer will |
|                           | be valid for reads (and writes).                                     |
+---------------------------+----------------------------------------------------------------------+
| function guarantee of     | The goal safety requirement is provided by the called function       |
| ``$function``             | ``$function``, as it has it (or a stronger statement) listed as a    |
|                           | :doc:`guarantee <guarantee>`.                                        |
+---------------------------+----------------------------------------------------------------------+
