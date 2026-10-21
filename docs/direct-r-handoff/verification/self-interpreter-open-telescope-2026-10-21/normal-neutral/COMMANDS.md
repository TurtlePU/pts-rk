# Normal neutral substitution

Date: 2026-10-21. Repository: `/Users/akuklev/air/pts-rk`.
Source: `theories/self_interpreter/NormalNeutralSubstitution.v`, 109 lines.
Frozen SHA-256:
`dc7cf2ab749df8980c5ef21917dbd66dcd687b0b24ccce2188a93b3293bf3bab`.
Only this new source and scoped evidence were edited; coordinator owns
Dune/Audit. No Git mutation or frozen-source edit.

## Contract

For a pointwise normal substitution whose images are not lambdas,
`normalb_replace` proves EXACT equality of the original annotated term's
normality bit before and after ordinary substitution. Source terms need not
be normal. `isLambda_replace` preserves the original outer-lambda test under
the weaker neutral-image premise. Both facts lift through every binder,
retaining annotations. Composition, single-variable substitution and direct
original TypedSub typing/normality corollaries are proved.

This does not prove that any particular full PHOAS compiler has neutral
outputs or coherent type-code substitution. It supplies a structural tool
for that later invariant. No normalization, hereditary substitution,
annotation erasure, bidirectional replacement typing or output-normality
premise is used.

## Exact verification

Fresh directories were obtained with `mktemp -d`:
`/tmp/pts-rk-normal-neutral-substitution.wCLGCz` and
`_build/normal-neutral-substitution.R4SRIk`.
Each attempt used retained `RUN.sh NN`, with output in `attempt-NN.log`
and exact exit in `status.tsv`:

```sh
cd /Users/akuklev/air/pts-rk
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
timeout 1200 opam exec -- dune build \
  --build-dir=/tmp/pts-rk-normal-neutral-substitution.wCLGCz \
  --display=short --no-buffer -j 2 \
  theories/self_interpreter/NormalNeutralSubstitution.vo
```

Attempt01 exited1: exact structural preservation proofs compiled, then
`TypedSub` was unavailable because the Morphisms import was missing.
Attempt02 added that import and exited0 with all TEN own reports CLOSED.
No other failed attempt, timeout, interruption or disk failure occurred.

Retained `CHECK.sh` exited0; `kernel.exit` is0. It ran:

```sh
timeout 1200 opam exec -- rocq check -silent -o \
  -Q /tmp/pts-rk-normal-neutral-substitution.wCLGCz/default/theories PTSrk \
  -Q /tmp/pts-rk-normal-neutral-substitution.wCLGCz/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
  -Q /tmp/pts-rk-normal-neutral-substitution.wCLGCz/default/theories/self_interpreter PTSrk.SelfInterpreter \
  PTSrk.SelfInterpreter.NormalNeutralSubstitution
```

The recursive inventory contains only unchanged upstream dependent functional
extensionality, distinct from the ten CLOSED own reports. No type-in-type,
unsafe fixpoint or assumed positivity. Forbidden-declaration scan exit1
(no matches) is retained in `safety.exit`; exact source hash in `source.sha256`.

The same driver recorded `git rev-parse HEAD`, `rocq -v`, `dune --version`,
`ocamlc -version`, `opam --version`, and complete installed package versions
in `versions.log`: Rocq9.2.0, Stdlib9.1.0, Equations1.3.2+9.2,
OCaml4.14.2, Dune3.23.1, opam2.6.1. HEAD remains
`e822cd62df393faf4d5e4ed0c4c8fed173ccba6f`.
Later aggregate/pristine comparison is a separate coordinated check.
Raw scripts/logs are local generated evidence, not committed artifacts.

Independent read-only review by the source-validity/telescope-recovery owner
passed against the frozen hash. The normal/non-lambda substitution guard is
essential and explicit; no general normal-substitution claim is made.
