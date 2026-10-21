# Sort and universe-view operations

Date: 2026-10-20. Working directory: `/Users/akuklev/air/pts-rk`.
Source: `theories/self_interpreter/TarskiSorts.v`, 201 lines.
SHA-256: `0dcc393aa1edaedd9fe165cce5195295d87f2c99de4c7a45b8cd1fdf830d679a`.
Only the new source and this scoped evidence are owned by the subtask.
The coordinating agent owns registration, aggregate checks and live handoff.

## Contracts and orientation

The actual signature field has type
`law_r : Eq_1(U0, El0 u_r, C_r)`. Thus `code_to_term` uses the BACKWARD
cast to send `A:C_r` to a term at `El0 u_r`; `term_to_code` uses the
FORWARD cast in the other direction. Both functions are ordinary original
PTS applications. Their arrow types have original sort U1 because both
endpoints have sort U0, independently of the external label r. The law
type itself retains its previously proved sort U2; no level is lowered.

The code and law fields are variables, so `El0 u_r` and the cast
annotations are normal. Normality of either cast application follows from
normality of its input. There is no hidden arbitrary-family normality
assumption in these universe operations.

`sort_quote k r = code_to_term k 0 (u_r)` uses law ZERO, correctly
representing the original axiom `U_r:U0`. It is originally typed at
`El0 u_0`, is normal, and actual replacement by the finite identity fill
beta-recovers literal `U_r` for `r<=k+1`. Replacing either direction of
the general cast similarly recovers its literal replaced input, without
typing or normality premises on that input.

`closed_sort_quote` closes this body over the actual finite signature.
Original closed typing and normality are proved. `closed_sort_run_typed`
directly types the actual identity application at U0 in every target
context, using typed telescope application and original conversion.
`closed_sort_quote_recovers` independently proves its reduction to U_r.
Typing is not inferred by subject expansion from recovery.

The bounded contract covers every external sort label by choosing a
sufficient finite ceiling (for example k=r); it does not claim that one
fixed palette covers unbounded literals. No generic neutral-cast
roundtrip is asserted definitionally equal, no normal semantic payload is
supplied, and this sort fragment is not a full dependent quoter.

## Toolchain and exact commands

Fresh Dune directory: `/tmp/pts-rk-tarski-sorts.oFok2A`.
Ignored raw evidence: `_build/tarski-sorts.7XbL8b`.
Each numbered attempt used `bash _build/tarski-sorts.7XbL8b/RUN.sh NN`;
the retained runner is exactly:

```sh
#!/usr/bin/env bash
attempt="$1"
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-tarski-sorts.oFok2A --display=short --no-buffer theories/self_interpreter/TarskiSorts.vo > "_build/tarski-sorts.7XbL8b/attempt-$attempt.log" 2>&1
build_status=$?
printf '%s\n' "$build_status" > "_build/tarski-sorts.7XbL8b/attempt-$attempt.exit"
tail -45 "_build/tarski-sorts.7XbL8b/attempt-$attempt.log"
exit "$build_status"
```

| Attempt | Exit | First outcome |
| --- | --- | --- |
| 01 | 1 | Target not yet registered in Dune. |
| 02 | 1 | `universe_cast_types_sort`: a `change` placeholder did not infer the term; replace the numeral rank instead. |
| 03 | 1 | Normality application needed its law argument explicitly instantiated before reflexivity evidence. |
| 04 | 1 | Closed weakening needed the source context epsilon explicitly supplied to `typing_rename`. |
| 05 | 0 | Entire source compiled; seventeen closed assumption reports. |

While registration was pending, dependencies were compiled successfully
with the following command (exit 0, `dependencies-01.log`/`.exit`):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-tarski-sorts.oFok2A --display=short --no-buffer theories/self_interpreter/TarskiSignature.vo > _build/tarski-sorts.7XbL8b/dependencies-01.log 2>&1
build_status=$?
printf '%s\n' "$build_status" > _build/tarski-sorts.7XbL8b/dependencies-01.exit
tail -20 _build/tarski-sorts.7XbL8b/dependencies-01.log
exit "$build_status"
```

Version command, exit 0 (`versions.log`/`.exit`):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam list --switch=pts-rk-ci --installed --columns=name,version --short rocq-core rocq-stdlib rocq-equations ocaml dune > _build/tarski-sorts.7XbL8b/versions.log 2>&1
version_status=$?
printf '%s\n' "$version_status" > _build/tarski-sorts.7XbL8b/versions.exit
```

Actual versions: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2 and Dune 3.23.1. All failures are retained; no timeout,
theorem weakening or suppressed check/warning occurred. Final source
compilation reran its reports, not a cached no-op.
Scoped `git diff --check` exits 0. No admission, axiom, disabled guard or
universe check, or diagnostic Show occurs. Source hashing uses `shasum -a 256`.
Recursive kernel, pristine inventory, aggregate audit and full CI are
separate coordinating-agent checks, not inferred from this targeted build.

## Assumption reports

All seventeen endpoints printed `Closed under the global context`:
`decoded_universe_sort`, `universe_casts_typed`, `universe_cast_types_sort`,
`code_to_term_typed`, `term_to_code_typed`, `code_to_term_normal`,
`term_to_code_normal`, `decoded_universe_recovers`, `code_to_term_recovers`,
`term_to_code_recovers`, `sort_quote_typed`, `sort_quote_normal`,
`sort_quote_recovers`, `closed_sort_quote_typed`, `closed_sort_quote_normal`,
`closed_sort_run_typed`, and `closed_sort_quote_recovers`.
