# Full original source derivation data

Date: 2026-10-21. Working directory: `/Users/akuklev/air/pts-rk`.
Owned source: `theories/self_interpreter/FullSource.v`, 334 lines.
SHA-256: `a742200604c651f8344cb6811c28f1bc91f0ecb57e47b18ac30dbd211854f46d`.
Only this new source and its scoped evidence were edited by this subtask.
The coordinator owns Dune/Audit registration, prose and live handoff.
No original kernel, existing proof module, Git index or reference was changed.

## Domain and computational boundary

`step_data n t u : Type` has exactly the seven original step constructors:
product domain/body, lambda annotation/body, application function/argument,
and beta contraction with the original `subst`. `reduction n t u : Type`
is an explicit finite forward chain. Transparent append/map and product,
lambda and application congruences construct actual chain data.
`conversion n t u : Type` is a finite path of explicitly forward or backward
steps, with executable append/reversal and a forward-chain inclusion.
No opaque `def_equiv` proof is a field or an executable oracle.

`derivation n G t T : Type` has all six original typing rules. Sorts use
the actual axiom U_r:U0; product ranks are exactly max(S a,b); variables use
the unchanged scoped Context.index; lambdas retain their literal annotation;
application uses original substitution; conversion includes an independent
target-sort derivation and explicit conversion data. In particular, variable
and sort rules have no added wf guard. This preserves the literal domain of
original Typing.typ, including judgments in arbitrary original contexts.

The four iff theorems equate INHABITATION of these datatypes with the original
step/reduction/conversion/typing judgments. Completeness is a proposition
`original_judgment -> inhabited data`; it does not eliminate an opaque Prop
proof into Type. Supplied data can be traversed and interpreted computationally.
There is no assumed target quotation, normality, coherence or normalization
result. Conversion intermediates may be untyped, exactly as in original
unrestricted beta conversion; typed forward conversion is a separate module.

`literal_indices` visits every derivation judgment's full context, term and
type, including annotations, and the whole intermediate terms in all supplied
conversion paths. Entries are literal ceilings calculated by the existing
`maxRankLiteral`, not a runtime-cost model. `rule_indices` records the explicit
product input/output formation ranks, lambda domain rank and conversion target
sort. `source_budget` bounds both finite lists. Current judgment/sort bounds
and conversion-intermediate bounds are proved, and every original typing has
such finite data as a Prop existence statement. These bounds do NOT establish
all inferred semantic subterm ranks, nor adequacy of an unconstructed target
quotation palette. `rule_count`, `conversion_count`, chain/path lengths and the
explicit conversion-term list are executable independent traversals.

## Verification and exact commands

Fresh absolute Dune build: `/tmp/pts-rk-full-source.G37O42`.
Ignored raw evidence: `_build/full-source.5vO9QU/`.
The final source compilation exits 0 with ELEVEN closed assumption reports.
No theorem report adds an axiom. A separate read-only mathematical/domain
review by the audit agent passes; no correction was requested.
Recursive kernel checking also exits 0. The loaded-library inventory has
only the existing upstream functional-extensionality declaration and no
unsafe fixpoints, type-in-type or assumed positivity; this inventory is
distinct from the eleven closed theorem-level reports.

Every attempt used `bash _build/full-source.5vO9QU/RUN.sh NN`.
The retained runner is exactly:

```sh
#!/usr/bin/env bash
attempt="$1"
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-full-source.G37O42 --display=short --no-buffer theories/self_interpreter/FullSource.vo > "_build/full-source.5vO9QU/attempt-$attempt.log" 2>&1
build_status=$?
printf '%s\n' "$build_status" > "_build/full-source.5vO9QU/attempt-$attempt.exit"
tail -45 "_build/full-source.5vO9QU/attempt-$attempt.log"
exit "$build_status"
```

| Attempt | Exit | First outcome |
| --- | --- | --- |
| 01 | 1 | FullSource target not yet registered by the coordinator. |
| 02 | 1 | Append needed an explicit dependent match return for the second chain. |
| 03 | 0 | All source/trace datatypes and original iff theorems compile; four closed reports. |
| 04 | 1 | New budget traversal needed the existing RankEstimate namespace imported. |
| 05 | 1 | Conversion branch needed its own inferred scope rather than the outer derivation scope. |
| 06 | 1 | Current-judgment membership proof needed explicit reduction of List.In. |
| 07 | 0 | Entire final source compiles; eleven closed reports. |

The final successful build reran the source's reports, not a cached no-op.
The known logical-loadpath remapping warning remains visible; no check or
warning was disabled. No timeout occurred. No theorem/domain weakening was
used to repair these elaboration/proof-script failures.

Version command (exit 0, `versions.log`/`.exit`):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam list --switch=pts-rk-ci --installed --columns=name,version --short rocq-core rocq-stdlib rocq-equations ocaml dune > _build/full-source.5vO9QU/versions.log 2>&1
version_status=$?
printf '%s\n' "$version_status" > _build/full-source.5vO9QU/versions.exit
sed -n '1,30p' _build/full-source.5vO9QU/versions.log
exit "$version_status"
```

Actual versions: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2 and Dune 3.23.1.

Recursive kernel command is retained in `CHECK.sh`, with full `kernel.log`
and immediate `kernel.exit`:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-full-source.G37O42/default/theories PTSrk -Q /tmp/pts-rk-full-source.G37O42/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-full-source.G37O42/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.FullSource > _build/full-source.5vO9QU/kernel.log 2>&1
kernel_status=$?
printf '%s\n' "$kernel_status" > _build/full-source.5vO9QU/kernel.exit
tail -30 _build/full-source.5vO9QU/kernel.log
exit "$kernel_status"
```

Scoped `git diff --check` exits 0. A source search for admissions, axioms,
disabled guard/universe checking and diagnostic Show returns no matches
(expected rg exit 1). Source identity uses `shasum -a 256`; no generated
cache or raw log is a source artifact. Aggregate audit, full CI, and pristine
comparison are coordinating-agent checks, not inferred from the targeted build.
