# Guarded beta graphs worker — 2026-10-23

Only `theories/CombinatoryLogic-rk/GuardedBetaGraphs.v` and this worker's
evidence directory were changed for this continuation. Compiler artifacts
remain outside the repository. No staging, commit, or shared Dune/doc edits.

All 36 public reports are closed. The final compile (attempt 08) and complete
recursive kernel check both exit 0. The kernel's entire inherited inventory
contains functional_extensionality_dep only; there are no unsafe entries.
The root integrated audit separately compares that inventory with pristine.

The evaluator enumerates every original one-beta successor, including lambda
annotations. `Reach xs k t u` is independently generated, requires every state
in xs, and bounds the path by k steps. `reaches` decides it exactly. Composition
uses k+l, not k. `joins` searches a common reduct in xs. Neither definition
uses typing, normalization, or semantic correctness as an admission premise.
Every original reduction/conversion has a finite support and is covered by
computed size/depth/label bounds on a prefix-alphabet syntax enumeration.
The existential all-budget equivalence does not decide unrestricted conversion.
The bounds constrain represented path states, not host runtime allocations or
all terms temporarily built while computing the one-step successor list.

Environment on all invocations:

```sh
OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
OPAMSWITCH=pts-rk-ci
```

Executable `/Users/akuklev/.local/share/pts-rk-ci/bin/opam`; Rocq 9.2 compiled
with OCaml 4.14.2. `mktemp -d /tmp/pts-rk-guarded-beta.XXXXXX` returned
`/tmp/pts-rk-guarded-beta.LXnPKw`.

Each attempt copies the source into that directory and runs:

```sh
opam exec -- rocq compile \
  -Q /tmp/pts-rk-quantified-models.uhpkYv/default/theories PTSrk \
  -Q /tmp/pts-rk-quantified-models.uhpkYv/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
  -Q /tmp/pts-rk-quantified-models.uhpkYv/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q /tmp/pts-rk-quantified-models.uhpkYv/default/theories/CombinatoryLogic-rk PTSrk.Combinatory \
  -Q /tmp/pts-rk-guarded-beta.LXnPKw PTSrk.Combinatory \
  /tmp/pts-rk-guarded-beta.LXnPKw/GuardedBetaGraphs.v
```

| Attempt | Exit | Result |
| --- | --- | --- |
| 01 | 1 | `in_map` inferred the wrong dependent binder argument |
| 02 | 1 | tactic branching count after destructing a reflexive path budget |
| 03 | 1 | missing explicit inclusion into the extended finite support |
| 04 | 0 | complete core graph/path/common-reduct development |
| 05 | 1 | numeric envelope lemma needed its definition unfolded in induction |
| 06 | 1 | common-reduct monotonicity needed explicit source budgets |
| 07 | 0 | complete numeric-envelope extension, 31 closed reports |
| 08 | 0 | five executable regressions, all 36 reports closed |

Full recursive kernel check, no skips/admissions:

```sh
opam exec -- rocq check -silent -o \
  -Q /tmp/pts-rk-quantified-models.uhpkYv/default/theories PTSrk \
  -Q /tmp/pts-rk-quantified-models.uhpkYv/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
  -Q /tmp/pts-rk-quantified-models.uhpkYv/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q /tmp/pts-rk-quantified-models.uhpkYv/default/theories/CombinatoryLogic-rk PTSrk.Combinatory \
  -Q /tmp/pts-rk-guarded-beta.LXnPKw PTSrk.Combinatory \
  PTSrk.Combinatory.GuardedBetaGraphs
```

`kernel.log` records the first successful kernel result. After the five
regressions were added, the same recursive check was rerun as
`kernel-final.log`. The regressions cover a one-step success, zero-step
rejection, missing destination/absent reflexive source, common-reduct
search in both directions with unequal budgets, and annotation-only beta
reduction. All five compute by reflexivity on explicit small state lists.
`source-before-regressions.sha256` preserves the earlier verified hash.
The existing logical-loadpath
remapping warning is retained verbatim. `source.sha256` and `versions.log`
retain the exact verified source and tool version. Scoped whitespace and hash
checks pass.
