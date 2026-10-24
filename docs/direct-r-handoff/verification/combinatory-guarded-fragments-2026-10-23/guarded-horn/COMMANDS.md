# Guarded Horn worker — 2026-10-23

Only `theories/CombinatoryLogic-rk/GuardedHornFragments.v` and this worker
evidence directory were changed. No source-directory compiler artifacts,
staging, commits, or edits to shared documentation/Dune were performed.

The root and development README, newest STATE/DECISIONS/BUILD, scoped Dune
diff, previous quantified-model audit commands/status, and pinned compiler
were inspected before editing. The independent generic development imports
only GroundHorn and Stdlib. The 19 public theorem reports are all closed.

The Type-valued Proof/Proofs syntax computes proof height and the maximum of
each supplied atom cost. Bounded derivations impose only these numeric costs,
retain the independent original Rules relation, and advance premise stratum h
to conclusion stratum S h. All-budget coverage and common-envelope coverage
for every finite family are proved. Fixed H rejects overflow. The zero-cost
chain example refutes same-stratum closure even without syntax growth.

Environment used on every compiler/kernel invocation:

```sh
OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
OPAMSWITCH=pts-rk-ci
```

The executable is `/Users/akuklev/.local/share/pts-rk-ci/bin/opam`.
Compiler version: Rocq 9.2, compiled with OCaml 4.14.2. The isolated directory
was created by `mktemp -d /tmp/pts-rk-guarded-horn.XXXXXX`, yielding
`/tmp/pts-rk-guarded-horn.VJZbDb`.

For each numbered attempt, the source was copied to that isolated directory,
then the following command ran, with stdout/stderr archived in its log:

```sh
opam exec -- rocq compile \
  -Q /tmp/pts-rk-quantified-models.uhpkYv/default/theories/CombinatoryLogic-rk PTSrk.Combinatory \
  -Q /tmp/pts-rk-guarded-horn.VJZbDb PTSrk.Combinatory \
  /tmp/pts-rk-guarded-horn.VJZbDb/GuardedHornFragments.v
```

| Attempt | Exit | Result |
| --- | --- | --- |
| 01 | 1 | `bounded_step`: `eauto` did not use the iff helper |
| 02 | 1 | external mutual induction scheme needed explicit parameters |
| 03 | 1 | partial scheme application still insufficient for induction tactic |
| 04 | 1 | same external scheme issue in the independent chain example |
| 05 | 0 | first complete compilation, 17 closed reports |
| 06 | 0 | final compilation with finite-family coverage, 19 closed reports |

The final recursive kernel check (no dependency skips/admissions) is:

```sh
opam exec -- rocq check -silent -o \
  -Q /tmp/pts-rk-quantified-models.uhpkYv/default/theories/CombinatoryLogic-rk PTSrk.Combinatory \
  -Q /tmp/pts-rk-guarded-horn.VJZbDb PTSrk.Combinatory \
  PTSrk.Combinatory.GuardedHornFragments
```

It exits 0. The complete context inventory has no axioms and no unsafe
entries. Its output is `kernel.log`. `source.sha256` records the final source hash;
`versions.log` retains the compiler version. The root agent separately runs
the fresh integrated audit and compares the full inherited context inventory.
