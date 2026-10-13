# Functional R — Theorem 7

`Theorem7.theorem7` proves the harmonized manuscript's `thm:direct-R` with the
original four-constructor interpretation, not the relational carrier.
`DirectRFunctionalAudit.v` prints the final types and transitive assumptions.

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
Equality transport and full preservation of this first-order deduction system
are now checked. FunctionalDeduction.sentence_preservation constructs original
PTS inhabitants for every derivable source sentence, including all primitive
logical and equality rules.
FunctionalCountermodel proves source order-reflexivity underivable; its
translation has an internal proof, establishing nonfaithfulness. This source
countermodel is NOT a set model of PTS.

The Type-valued `Theorem7.theorem5_target : Kernel.Theorem5Target` is also
constructed, along with `effective_axiom`, `effective_source_axiom`,
`effective_deduction`, `effective_ground_true`, and `effective_ground_false`.
These return annotated proof terms paired with original typing proofs.
They use exhaustive finite derivation-certificate enumeration and constructive
unbounded search whose termination follows from the proved existence theorems.
No choice axiom or typing-decidability assumption is used. This is an effective
but intentionally inefficient interface; use the native checker for concrete
small terms. The old bounded optional generator's contracts remain separate.

This library imports only the shared parent library and original kernel, not
the relational interpretation. Generic iteration and finite-selector
certificates formerly housed in unary modules are shared directly.

Build and audit from the repository root:

```sh
dune build @Interpretation_of_R/functional/audit
```

Example import:

```coq
From Interpretation_of_R.functional Require Import DirectRTheorem7.
Check Theorem7.theorem7.
Check Theorem7.theorem5_target.
Check Theorem7.effective_deduction.
Print Assumptions Theorem7.theorem7.
Print Assumptions Theorem7.theorem5_target.
Print Assumptions Theorem7.effective_deduction.
```
