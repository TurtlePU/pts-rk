# Direct interpretations of arithmetic R

The [arithmetic development](../theories/Interpretation_of_R/README.md) has
three Rocq libraries: shared infrastructure, the relational interpretation,
and the functional interpretation. Neither interpretation imports the other,
and neither depends on the separate set model. All use the unchanged original
`PTSrk` typing judgment and annotated syntax.

## Relational Theorem 4

```coq
From Interpretation_of_R.relational Require Import DirectRTheorem4.
Check Theorem4.theorem4.
Print Assumptions Theorem4.theorem4.
```

The unconditional result combines realization of every relational axiom
scheme, preservation of an independently defined classical first-order
deduction system, ground proofs and internal refutations, and a concrete
nonfaithfulness witness. See the
[relational README](../theories/Interpretation_of_R/relational/README.md).

## Functional Theorem 7 and the original target

```coq
From Interpretation_of_R.functional Require Import DirectRTheorem7.
Check Theorem7.theorem7.
Check Theorem7.theorem5_target.
Check Theorem7.effective_deduction.
Print Assumptions Theorem7.theorem7.
Print Assumptions Theorem7.theorem5_target.
```

The functional result uses the original four-constructor carrier and all five
axiom schemes uniformly in their indices. It includes independent classical
deduction preservation, ground correctness, and nonfaithfulness.
`Theorem7.theorem5_target : Kernel.Theorem5Target` provides the Type-valued
effective interface: annotated terms paired with original typing proofs.

Constructive exhaustive derivation-certificate search turns the proved
existence results into witness functions without a choice axiom. This is not
a complexity guarantee. The optional bounded generator's legacy contracts
remain separate and are not premises of these theorems. See the
[functional README](../theories/Interpretation_of_R/functional/README.md).

## Checker and verification

The shared native evaluator retains lambda annotations and reduces inside
annotations and products. The fuel-bounded checker proves successful results
against original typing; exhaustion is inconclusive, not untypability.
Numerical side-condition proofs in native Prop are not PTS inhabitants.

From the repository root in the [pinned toolchain](DirectR-CI.md):

```sh
dune build @theories/Interpretation_of_R/relational/audit
dune build @theories/Interpretation_of_R/functional/audit
bash tools/check-local-ci.sh
```

Use a fresh absolute `--build-dir` for fresh assumption output.
[STATE.md](direct-r-handoff/STATE.md) and its dated verification directories
record actual commands and results. Historical draft limitations and old
filesystem paths remain in the handoff archives, not current status.
