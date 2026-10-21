# Executable full-source substitution

Date: 2026-10-21. Working directory: `/Users/akuklev/air/pts-rk`.
Owned source: `theories/self_interpreter/SourceSubstitution.v`, 259 lines.
SHA-256: `2198863c000673c55be4ff7c9c76cefbf9e9cd608bca10b51c67380ee11eafa7`.
Only this new source and scoped evidence were edited by this subtask;
the coordinator owns registration, aggregate audit, prose and live handoff.
No existing proof source, original kernel, Git index or reference was changed.

## Checked boundary

`step_rename` and `step_replace` construct all seven original source-step
cases, retaining reductions inside annotations and using the exact original
beta substitution. Both transformations use one fixed renaming/substitution;
no heterogeneous one-step substitution assertion is made. Forward chains
and finite symmetric conversion paths are transformed structurally.

Strict lookup-preserving renaming constructs computational weakening first.
`substitution_data G D sigma` then supplies an actual Type-valued original
source derivation for every substituted variable. `substitution_lift`
constructs the fresh-variable and weakened old-variable cases explicitly.
`derivation_replace` transforms all six FullSource rules, preserving literal
terms, types, contexts, annotations and conversion paths. General typed
renaming is the variable-substitution specialization. No well-formedness
guard restricts the original source deduction domain.

`substitution_data_iff` relates INHABITATION of the finite pointwise data to
the existing original `Morphisms.TypedSub`. The finite-choice argument lives
entirely in Prop. It does not extract a computational source derivation from
an opaque original typing proof or conversion oracle. The transformations
themselves consume supplied Type-valued evidence and are transparent.

`beta_contractum_derivation` consumes the supplied original body and argument
derivations and returns a derivation of the literal `subst body u` at literal
`subst B u`. `beta_redex_derivation` additionally consumes the domain formation
derivation. `beta_source_preservation` certifies original typings of redex and
contractum and their original beta step. There is no quotation, internal
target equality, target-substitution coherence or full-interpreter claim.

## Verification

Fresh absolute Dune build: `/tmp/pts-rk-source-substitution.SxI3EX`.
Ignored raw evidence: `_build/source-substitution.ZiIubK/`.
Final compilation exits 0 with TEN closed own assumption reports. Independent
read-only review by the audit agent passes without correction. No new axiom
is introduced. The logical-loadpath remapping warning remains visible.
Recursive kernel checking exits 0; its loaded-library inventory lists only
the existing upstream functional-extensionality declaration, with no unsafe
fixpoints, type-in-type or assumed positivity. This inventory is distinct
from the ten closed theorem-level reports.

Each attempt ran `bash _build/source-substitution.ZiIubK/build.sh NN`.
The retained runner is exactly:

```sh
#!/usr/bin/env bash
set -u
cd /Users/akuklev/air/pts-rk
attempt="$1"
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-source-substitution.SxI3EX --display=short --no-buffer theories/self_interpreter/SourceSubstitution.vo > "_build/source-substitution.ZiIubK/attempt-${attempt}.log" 2>&1
build_status=$?
printf '%s\n' "$build_status" > "_build/source-substitution.ZiIubK/attempt-${attempt}.exit"
tail -60 "_build/source-substitution.ZiIubK/attempt-${attempt}.log"
exit "$build_status"
```

| Attempt | Exit | First outcome |
| --- | --- | --- |
| 01 | 1 | Coordinator had not yet registered the new Dune target. |
| 02 | 1 | Conversion map needed an explicit supplied step to determine its middle endpoint. |
| 03 | 1 | Broad context-index simplification hid the strict lookup equation. |
| 04 | 1 | Dependent Fin elimination needed an explicit predecessor-variable name. |
| 05 | 1 | Fresh-variable derivation needed explicit context and index arguments. |
| 06 | 1 | Higher-order `var` argument needed explicit eta expansion. |
| 07 | 1 | Beta variable lookup needed controlled rather than broad simplification. |
| 08 | 1 | Dependent Fin elimination renamed the scope; infer it from the context. |
| 09 | 1 | Final beta soundness application needed its supplied derivation arguments. |
| 10 | 0 | Entire final source, ten closed reports. |

No timeout occurred and no theorem/domain weakening repaired these elaboration
failures. The final successful build reran the source's reports rather than
relying on a cached no-op.

Version command (exit 0; `versions.log`/`.exit`):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam list --switch=pts-rk-ci --installed --columns=name,version --short rocq-core rocq-stdlib rocq-equations ocaml dune > _build/source-substitution.ZiIubK/versions.log 2>&1
version_status=$?
printf '%s\n' "$version_status" > _build/source-substitution.ZiIubK/versions.exit
sed -n '1,30p' _build/source-substitution.ZiIubK/versions.log
exit "$version_status"
```

Actual versions: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2 and Dune 3.23.1.

Recursive checking uses the retained `check.sh`, with `kernel.log` and
immediate `kernel.exit`:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-source-substitution.SxI3EX/default/theories PTSrk -Q /tmp/pts-rk-source-substitution.SxI3EX/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-source-substitution.SxI3EX/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.SourceSubstitution > _build/source-substitution.ZiIubK/kernel.log 2>&1
kernel_status=$?
printf '%s\n' "$kernel_status" > _build/source-substitution.ZiIubK/kernel.exit
tail -30 _build/source-substitution.ZiIubK/kernel.log
exit "$kernel_status"
```

Scoped `git diff --check` exits 0. Source identity is recorded with
`shasum -a 256`. Aggregate audit, full CI and pristine comparison remain
coordinator checks, not consequences of this targeted compilation.
