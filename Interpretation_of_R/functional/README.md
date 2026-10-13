# Functional R — Theorem 7 development

Theorem 7 is **not complete**. This directory contains its original
four-constructor interpretation, not a replacement by the relational carrier.
`DirectRFunctionalAudit.v` checks the implemented components and their
transitive assumptions; it is not a completed interpretation theorem.

Checked components include R1/R2/R3, the entire finite observation telescope,
ground equality/order proofs and internal refutations, and zero, successor and
addition closure of the uniform positive bounded-case invariant.

Remaining: multiplication invariant closure (including both zero-factor laws
and positive-factor conditions), instantiate Good and project the bounded case,
derive R4/R5, preserve an independently defined first-order deduction system,
and package the unconditional theorem. `Kernel.Theorem5Target` is the legacy
axiom-realization target, not evidence that these obligations are solved.

This library imports only the shared parent library and original kernel, not
the relational interpretation. Generic iteration and finite-selector
certificates formerly housed in unary modules are shared directly.

Build and audit from the repository root:

```sh
dune build @Interpretation_of_R/functional/audit
```

Example import:

```coq
From Interpretation_of_R.functional Require Import DirectRFunctionalAddition.
Check FunctionalAddition.addition_invariant_realized.
Print Assumptions FunctionalAddition.addition_invariant_realized.
```
