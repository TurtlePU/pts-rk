# Functional R — Theorem 7 development

Theorem 7 is **not complete**. This directory contains its original
four-constructor interpretation, not a replacement by the relational carrier.
`DirectRFunctionalAudit.v` checks the implemented components and their
transitive assumptions; it is not a completed interpretation theorem.

Checked components include all five original axiom schemes (uniformly in their
indices), the entire finite observation telescope,
ground equality/order proofs and internal refutations, and zero, successor,
addition and multiplication closure of the uniform positive bounded-case invariant.

Multiplication uses both zero-factor laws and retains the positive-factor
conditions on its order bounds. Good is now instantiated at the rank-10
invariant, yielding uniform bounded cases and R4/R5.
The independent functional deduction system now includes all primitive logical
connectives, eigenvariable-correct quantifier rules and equality replacement.
Checked infrastructure includes source weakening, translation substitution
(including instantiation), formation and classical stability for every formula,
and realization of all independently defined source axiom schemes. Functional
R4 is the original implication, not the relational biconditional.
Remaining: prove preservation of this first-order deduction system and
package the unconditional theorem. FunctionalAxioms.all_axioms_realized gives
Prop-valued existence of original typing witnesses; the legacy Type-valued
`Kernel.Theorem5Target` record and generator contracts are not thereby filled.

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
