# Finite typed quotation caches

2026-10-21; working directory `/Users/akuklev/air/pts-rk`.
Source `theories/self_interpreter/QuotationCache.v`, 376 lines,
SHA256 `20839aa1361f22e20e32a6a6f4dd5c85a8050f972d010771c29779e56215391a`.
Only new owned source/evidence edited; no Git/index mutation or frozen edit.

## Contract

`code_view` is finite Type-valued recursive data. A literal product retains
independently originally typed domain/codomain code views in the actual decoded
domain context. Its root code may differ from the constructed product code;
no unproved equality between them is stored. `shape_view` records a term's
literal product children without assuming that the term is a type.
`view_from_shape` uses independently typed root evidence and ORIGINAL sort
uniqueness to reconstruct a type view after a variable hit. It does not quote
a generated typing proof. `build_product_view` constructs actual typed normal
product code, with strong recovery of both annotations and body.

`realization` records original wf contexts, actual TypedSub, and literal
identity filling of inherited signature variables. `spine_realization` is an
actual instance. `extend_realization` preserves literal source annotations
using original subject reduction and context transport, without assuming the
new typed substitution. Root certificates and views are output invariants;
this module does NOT assert full-source quotation coverage.

## Commands and all attempts

Fresh initial build `/tmp/pts-rk-quotation-cache.ddlOA9`; ignored raw logs and
retained runners `_build/quotation-cache.LE7E0N/`. Each attempt was
`bash _build/quotation-cache.LE7E0N/build.sh NN`, executing:

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-quotation-cache.ddlOA9 --display=short --no-buffer theories/self_interpreter/QuotationCache.vo > "_build/quotation-cache.LE7E0N/attempt-${attempt}.log" 2>&1
build_status=$?
printf '%s\n' "$build_status" > "_build/quotation-cache.LE7E0N/attempt-${attempt}.exit"
```

| Attempt | Exit | First result |
| --- | --- | --- |
| 01 | 1 | Target not yet Dune-registered. |
| 02 | 1 | cbn unfolded decoder before the identity-fill rewrite. |
| 03 | 0 | Mechanical substitution and actual sort certificates, three closed. |
| 04 | 0 | Recursive product views, seven closed. |
| 05 | 1 | Dependent product constructor indices needed explicit arguments. |
| 06 | 1 | sort_rank_unique needed explicit RedexRanks import. |
| 07 | 0 | Shape-to-view reconstruction, ten closed. |
| 08 | 1 | Spine wf proof required explicit k argument. |
| 09 | 0 | Final realization interface, thirteen closed. |

`bash _build/quotation-cache.LE7E0N/check.sh` exited0; exact recursive command:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-quotation-cache.ddlOA9/default/theories PTSrk -Q /tmp/pts-rk-quotation-cache.ddlOA9/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-quotation-cache.ddlOA9/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.QuotationCache
```

Kernel log/exit retained. Loaded inventory contains only unchanged upstream
dependent functional extensionality, no unsafe fixpoint/type-in-type/positivity.
All thirteen public transitive assumption reports are CLOSED.
`bash _build/quotation-cache.LE7E0N/versions.sh` exited0: Rocq9.2.0,
Stdlib9.1.0, Equations1.3.2+9.2, OCaml4.14.2, Dune3.23.1. Exact opam-list
runner/output/exit retained. Scoped git diff --check exited0. No timeout.
The coordinator owns aggregate/pristine checks and shared handoff updates.
