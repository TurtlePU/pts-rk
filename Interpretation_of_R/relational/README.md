# Relational R — Theorem 4

Entry point:

```coq
From Interpretation_of_R.relational Require Import DirectRTheorem4.
Check Theorem4.theorem4.
Print Assumptions Theorem4.theorem4.
```

The unconditional theorem packages all relational axiom realizations,
preservation of the independently defined classical deduction system, ground
truth proofs and falsehood refutations, and a nonfaithfulness witness.
The target is the original `PTSrk.Typing.typ` at `Ranks.RankSorts`.

This directory includes the unary carrier, its evaluation, separation and
bounded-case proofs, and the relational source syntax, translation, equality,
axioms, deduction and countermodel proofs. It has no functional-library
dependency. Shared finite-selector machinery is in the parent directory.

Build and audit from the repository root:

```sh
dune build @Interpretation_of_R/relational/audit
```
