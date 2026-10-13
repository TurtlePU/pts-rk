# Direct R interpretation

The development is split into three libraries under `Interpretation_of_R/`:
shared infrastructure at the parent level, the completed relational
interpretation in `relational/`, and the functional development in `functional/`.
Neither interpretation imports the other. The original kernel is unchanged in
`theories/`. See `../Interpretation_of_R/README.md` for imports and independent
build/audit targets. Functional Theorem 7 is proved in `DirectRTheorem7.v`.

## Current checked result — 2026-10-13

The harmonized manuscript's unary relational **Theorem 4** is proved as
`Theorem4.theorem4` in `Interpretation_of_R/relational/DirectRTheorem4.v`. Import it with
`From Interpretation_of_R.relational Require Import DirectRTheorem4.` Its unconditional statement combines
all relational axiom schemes, preservation of the independently defined
classical deduction system, ground proofs/internal refutations, and a concrete
nonfaithfulness witness. It uses the original annotated PTS typing judgment.

`DirectRRelationalAudit.v` checks the final types and transitive assumptions.
A fresh isolated build succeeds; all assumption reports are closed. Exact
commands, logs and the separate legacy full-suite timeout status are in
`direct-r-handoff/STATE.md` and `direct-r-handoff/verification/`.
The functional result `Theorem7.theorem7` now includes all original functional
axioms, independent classical deduction preservation, ground correctness and
nonfaithfulness. Its effective sigma-valued witness functions use exhaustive
certificates for the unchanged typing rules; constructive search also builds
`Theorem7.theorem5_target : Kernel.Theorem5Target`. There is no choice axiom.
The old bounded generator contracts are not used by these results.
PTS set-model soundness remains unfinished and separate in `ZFC_model/`.

## Historical modular draft snapshot (superseded status below)

Target: TurtlePU/pts-rk, commit `723cf2ec61c737ae82ba33d2e7db44f650122b0e`.
Prepared 2026-10-13. This replaces the earlier monolithic DirectR package.

## Read the status correctly

**No file in this contribution has been compiled with Rocq here.** `Qed` is
source text awaiting compilation, not an observed kernel acceptance. Theorem 5
is NOT completed. The new checker has successful-run proof scripts directly
against the existing `PTSrk.Typing.typ`; those scripts also await compilation.

The container has no `rocq`, `coqc`, `dune`, `opam`, or OCaml executable. A direct
network probe fails DNS resolution, so obtaining repository files through the
GitHub connector did not provide a usable compiler toolchain. This is one
verification limitation, not the whole explanation for the unfinished theorem.
The uniform mathematical formalization obligations are in DirectR-obligations.md.

No source kernel, sort rule, conversion rule, or normalization theorem is changed.
No new axiom or admitted proof is inserted. There is no answer-type nontriviality
proof, consistency premise, primitive eliminator, or set-theoretic model.

## Files and dependencies

| File | Role |
| --- | --- |
| `DirectRKernel.v` | Thin wrappers for the original typing and beta-equivalence judgments; no arithmetic. |
| `DirectREval.v` | Fuel-bounded head/full reduction on `Term nat n`, preserving lambda annotations; conversion-success proof scripts. |
| `DirectRCheck.v` | Syntax-directed inference, context/type validation, and `run_check_sound` with original `typ` as its conclusion. |
| `DirectRCodes.v` | Named assembler, arithmetic-expression carrier, domain/observation types, fixed candidate terms, axiom types. |
| `DirectRSymbolic.v` | Previous proof-producing Ltac, isolated for symbolic-index induction goals using typing hypotheses. |
| `DirectRProofs.v` | Fixed certificates checked with the native checker; retained uniform numeral/ground-calculation scripts. |
| `DirectRGenerated.v` | Pure variable-arity selector/table/invariant/axiom witness generators. |
| `DirectRFirstOrder.v` | Scoped source syntax and its guarded negative translation. No deduction relation/soundness theorem yet. |
| `DirectRObligations.v` | Explicit generator contracts and conditional assembly of the existing Theorem5Target. No contract is assumed. |
| `DirectRArithmetic.v` | Separate native-Prop arithmetic and capped-table mathematics; not a PTS realization proof. |
| `DirectRTests.v` | Concrete reflection examples and Print Assumptions commands, built separately. |
| `DirectR.v` | Small public facade; it does not import tests or the Prop-only arithmetic. |

The facade preserves `DirectR.Codes`, `DirectR.Kernel`, `DirectR.Generated`,
and `DirectR.FirstOrder`. Concrete examples moved from `Generated.R4_0`, etc.,
to `DirectRTests.DirectRTests.R4_0`, etc. The mathematical definitions and
witness-generator expressions are unchanged by the split.

## What the native checker changes

The evaluator checks syntactic equality before normalization and uses weak-head
reduction to inspect sorts/products. Beta contraction does not first evaluate its
argument. Fuel exhaustion returns `Undecided`, not a theorem of untypability.
Full conversion still includes reductions in lambda annotations and products.

The supplied `run_check_sound` script has conclusion

```coq
run_check fuel Gamma p A = Accepted tt -> Core.Typed Gamma p A
```

`Core.Typed` is precisely the upstream `typ` at `RankSorts`. The entry point
checks the context and expected type. In particular, the type-correctness and
subject-reduction theorems justify formation of an exposed product before
conversion is used; a bare equality test does not justify formation.

No declarative/bidirectional bridge from the lab repository is assumed. No
completeness or negative-result soundness theorem is claimed for this checker.

The fixed certificates in `DirectRProofs.v` now use `RkCheck.certify_with 4096`.
Concrete R3–R5 tests use explicit fuel 65536. These budgets are proposed, not
measured successful Rocq budgets; a timeout may require increasing them. The
symbolic ground-calculation induction scripts retain the old constructor
assembler, because Gallina evaluation cannot inspect a meta-level symbolic
numeral index. Replacing that symbolic layer with generic telescope lemmas is
still useful work. It is not hidden behind a claim that the whole refactor is a
finished uniform proof.

## Build in an existing working repository toolchain

Use the same Rocq/Equations switch that builds the unchanged upstream. The
pinned dune-project requires Dune 3.23, Rocq language 0.13, and rocq-equations.
The upstream does not pin one exact Rocq version; this package does not invent
a tested version constraint.

```sh
dune build theories/Ranks.vo                  # unchanged upstream baseline
dune build Interpretation_of_R/DirectREval.vo Interpretation_of_R/DirectRCheck.vo
dune build Interpretation_of_R/functional/DirectR.vo
dune build Interpretation_of_R/functional/DirectRArithmetic.vo Interpretation_of_R/functional/DirectRTests.vo
```

Or run `bash tools/check-direct-r.sh` from the repository root. It stops on the
first failure and retains logs. A failure is a development issue to fix, not a
reason to insert `Admitted`. Print Assumptions commands are in DirectRTests.v;
inspect their actual output after a successful build. Touching that file forces
its commands to run again when the build is otherwise cached.

## Independent checks

The package includes a Python evaluator of a restricted pure subset of the
actual SPLIT generator source. Twelve small object-code checks passed, together
with rejection of two invalid inequality indices. They do not execute Gallina
proof scripts, Ltac, or the Rocq kernel. The attempted full run timed out after
240 seconds and is NOT counted as a successful full rerun.

Static checks compare the definition bodies and generators to the previous
source, verify module dependencies, inspect for explicit axioms/admissions,
and apply both the aggregate patch and the three-patch series to the exact
upstream Dune scaffold. These are not a replacement for a repository build.
