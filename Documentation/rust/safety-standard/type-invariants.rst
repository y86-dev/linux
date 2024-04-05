.. SPDX-License-Identifier: GPL-2.0

Type Invariants
===============

``struct``, ``enum`` and ``union`` types can list type invariants. They are a kind of
:doc:`guarantee <guarantee>` that ``unsafe`` code can rely upon. They are listed in an unordered
list in the ``## Invariants`` subsection of the ``# Guarantees`` section. The wording of invariants
is identical to the wording of requirements.rst. Invariants hold for the entire lifetime of an
object. During the call of the ``drop`` function these invariants may be violated, since objects
that are being dropped can never be observed.

Objects with invariants need ``INVARIANT`` comments whenever they are constructed or a field with an
invariant is modified. The comment is similar to ``SAFETY`` comments and needs to justify that the
invariant holds. See justifications.rst for how to justify requirements.

Sometimes it is needed to violate an invariant temporarily. For example when inside of a function
one can temporarily violate the invariant, as long as it is later reestablished and no external code
can observe the violation. These violations must also be documented using the ``INVARIANT``
comments.
