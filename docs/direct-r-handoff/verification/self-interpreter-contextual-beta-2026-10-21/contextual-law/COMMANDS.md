# Arbitrary supplied-telescope contextual beta law

Date 2026-10-21; working directory `/Users/akuklev/air/pts-rk`.
Source `theories/self_interpreter/ContextualBeta.v`, SHA256
`9e16dea560b32d237179fdf6b2821477a353f621e4c0d64bee865932466436b0`.
Independent read-only audit: PASS. No original source or Git index changed.

## Contract

For an independently formed original telescope D with rank vector rs,
`equation` closes the carrier by literal products and both endpoints by
literal lambdas, then forms original Leibniz equality. Its exact formation
rank is `max(CT.rank rs b+2,d+1)`. `beta_type` specializes the endpoints to
the actual casted App/Abs roundtrip and f u, with independent original
input typings. `identity_witness` is actual reflexivity at the literal
multi-lambda and plain result carrier. Direct typing at the identity-specialized
beta field uses explicit original type conversion, not subject expansion,
pointwise extensionality, or an assumed equality witness.

Literal replacement, type reduction, witness transport computation and
annotation-aware normality are checked. Normality of the abstract cast field
retains the decoded-product annotation premise and neutral-head guards;
the identity witness requires normal telescope annotations and neutral B/f
heads. No normality after arbitrary specialization is inferred. This module
handles every independently supplied telescope, but does not itself generate
one uniform polymorphic field for all concrete telescopes.

## Builds

Fresh build `/tmp/pts-rk-contextual-beta.Pp1d1l`; raw ignored artifacts
`_build/contextual-beta.DU87Uk`. Exact runner `RUN.sh` invoked as
`bash _build/contextual-beta.DU87Uk/RUN.sh NN`:

```sh
attempt="$1"
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-contextual-beta.Pp1d1l --display=short --no-buffer theories/self_interpreter/ContextualBeta.vo > "_build/contextual-beta.DU87Uk/attempt-$attempt.log" 2>&1
build_status=$?
printf '%s\n' "$build_status" > "_build/contextual-beta.DU87Uk/attempt-$attempt.exit"
tail -n 45 "_build/contextual-beta.DU87Uk/attempt-$attempt.log"
exit "$build_status"
```

- 01: exit 0, seven own closed reports (formation/replacement/type reduction).
- 02: exit 0, eleven own closed reports (actual typed identity witness).
- 03: exit 1, a `pose proof` of neutral-cast normality could not infer its
  rank placeholder without a target goal. Supplied exact max(a+1,b).
- 04: exit 0, final fourteen own closed reports. No statement weakening,
  timeout, admission, or disabled check.

Recursive check exits 0, recorded in `kernel.log` and `kernel.exit`:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-contextual-beta.Pp1d1l/default/theories PTSrk -Q /tmp/pts-rk-contextual-beta.Pp1d1l/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-contextual-beta.Pp1d1l/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.ContextualBeta > _build/contextual-beta.DU87Uk/kernel.log 2>&1
```

Loaded inventory retains only upstream functional extensionality; unsafe,
type-in-type and assumed-positivity inventories are empty. New theorem-level
reports are closed. Pinned Rocq 9.2.0/Stdlib 9.1.0/Equations 1.3.2+9.2,
OCaml 4.14.2, Dune 3.23.1; same environment as the aggregate audit.
