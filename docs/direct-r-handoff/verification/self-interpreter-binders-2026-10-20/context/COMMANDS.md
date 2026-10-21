# Tarski signature under dependent binders — 20 October 2026

Base commit: `e822cd62df393faf4d5e4ed0c4c8fed173ccba6f`.
This task added only `theories/self_interpreter/TarskiContext.v` and its
evidence; parent owns Dune/Audit and shared documentation. No Git/index
mutation or frozen-source edit was made.

## Checked contracts

`environment k n G` is a METALEVEL record of an actual typed VARIABLE
renaming from the finite signature to original context G. `base_environment`,
`rename_environment` and `weaken_environment` construct it. The record does
not assume quotation, recovery, or source-conversion coherence. All six
inherited fields retain their bounded original typings and variable normality.

The concrete `spine k n G` starts at the actual finite signature and extends
it by arbitrary ORIGINAL declarations with independent sort derivations.
No quotation/normality result is inserted into the declaration domain.
Its computations produce:

- `depth`: the number of new dependent binders, with
  `n = depth + TarskiSignature.width k`;
- `spine_environment`: the actual injective variable inclusion;
- `identity_context`: the source-binder context obtained by specializing
  each declaration in its already constructed prefix;
- `identity_fill`: the original finite identity substitution, extended by
  `transpose` at each binder, so each newly bound variable stays a variable.

`spine_wf`, `identity_fill_typed` and `identity_context_wf` prove original
well-formedness/TypedSub, rather than assuming those conclusions.
`spine_normal` retains the independent declaration-normality premise.
NO normality is claimed for the instantiated context: specialization may
introduce administrative beta redexes. `identity_fill_embedding` and
`identity_fill_inherited` commute actual instantiation with the inclusion;
all six exact field equations follow. Fresh-variable, weakening and direct
original typing transport are also proved.

The generic product/law/Abs/App operations accept arbitrary terms in the
NEW ambient scope, including inputs depending on freshly bound variables.
Their original typing follows from independently typed inputs and the
actual inherited law field. After replacement by the computed spine fill,
product/law computation and Abs/App recovery preserve the literal substituted
inputs, including their redexes. No precomputed value or eta law is used.

This supplies a binder/context bridge, not a derivation-directed full
dependent quoter or global source-conversion theorem. All 34 own transitive
assumption reports are closed.

Independent read-only review by the separate paper-analysis agent passed
against the frozen hash below. It checked the noncircular environment/spine
premises, computed identity context/fill, fresh-variable preservation, six
field equations, injective inherited inclusion and fresh-scope operation
contracts. No correction was requested.

## Commands, versions and every attempt

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
timeout 1200 opam exec -- dune build \
  --build-dir=/tmp/pts-rk-self-tarski-context.ruXLqi \
  --display=short --no-buffer -j 2 theories/self_interpreter/TarskiContext.vo
```

Raw local-only ignored artifacts:
`_build/self-interpreter-tarski-context.kVJpRJ/`, containing `RUN.sh`,
`VERSIONS.sh`, `versions.log`, `status.tsv` and every attempt log.
Versions: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2,
Dune 3.23.1 and opam 2.6.1; full installed-package listing retained.

| Attempt | Exit | First actual result |
| --- | --- | --- |
| 01 | 1 | Dune registration pending; unknown target. |
| 02 | 1 | Typed-renaming composition needed the variable explicitly displayed as a renamed term. |
| 03 | 1 | Indexed inductive parameter must be `_` in constructor patterns. |
| 04 | 1 | Target-context formation needed the existing declaration sort supplied explicitly. |
| 05 | 0 | Complete environment/spine/substitution bridge; 12 closed reports. |
| 06 | 1 | Generic weakening statement needed its original `Term nat` annotation. |
| 07 | 1 | Dependent Fin constructor injection produced a sigma equality; replaced by an explicit homogeneous predecessor map. |
| 08 | 0 | Final operations, recovery and binder laws; 34 closed reports. |

No axioms, admitted proofs, disabled checks, weakened theorem or timeout.
Known logical-loadpath remapping warnings remain in the logs. No standalone
recursive kernel/full-CI claim is made by module compilation alone; the
aggregate verification is recorded separately for the frozen milestone.

Frozen source SHA-256:

```text
225d392d065f8cb57ad15955ca64791cb341b02bce8ba0d568477a95e090ed17  theories/self_interpreter/TarskiContext.v
```
