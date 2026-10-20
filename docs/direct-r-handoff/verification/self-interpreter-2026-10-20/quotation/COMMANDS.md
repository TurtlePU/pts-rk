# RankedQuotation development and independent kernel verification

Date: 2026-10-20. Working directory for every command below:
`/Users/akuklev/air/pts-rk`.

Only `theories/self_interpreter/RankedQuotation.v` was edited by this
subagent. Dune membership was added by the parallel decoder subagent.
The existing dirty repository and its other developments were preserved.
No commit, push, dependency installation, timeout, or interrupted compilation
occurred in this subtask.

## Environment and versions

Every Rocq/Dune command used this exact prefix:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci --
```

Recorded in `versions.log`, exit 0:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- bash -c 'rocq --version; rocq c --version; dune --version; ocamlc -version; opam list --installed --short --columns=name,version rocq-core rocq-stdlib rocq-equations' > /tmp/pts-rk-self-quote.tP1YlZ/versions.log 2>&1
```

Resolved versions: Rocq core 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2, Dune 3.23.1. The Rocq executable prints version 9.2;
the installed-package query supplies the exact 9.2.0 patch version.

The fresh absolute build workspace was created with:

```sh
mktemp -d /tmp/pts-rk-self-quote.XXXXXX
```

Its returned path was `/tmp/pts-rk-self-quote.tP1YlZ`. Subsequent attempts
reused its `build` subdirectory incrementally. The initial dependency build
was fresh; source edits caused later RankedQuotation compilations to rerun.
This is not a claim that every incremental attempt rebuilt every dependency.

## Exact compilation commands

For each NN in `01 02 03 04 05 06 07 08 09 10 11 12 13 14`, the command
was exactly the following, with that literal two-digit NN substituted in
the log filename:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-self-quote.tP1YlZ/build --display=short --no-buffer theories/self_interpreter/RankedQuotation.vo > /tmp/pts-rk-self-quote.tP1YlZ/attempt-NN.log 2>&1
```

The interactive shell wrapper for attempt 01 then ran `tail -n 30` on
the log without preserving the compiler exit code. Its shell-tool exit
was therefore 0, while the Dune diagnostic reported that the requested
target was unavailable. Its Dune numeric exit was not captured separately.
All attempts 02--14 captured `$?` into `task_quote_exit`, printed the last
25 or 30 log lines, and executed `exit "$task_quote_exit"`; the recorded
tool exit therefore equals the build exit in those attempts.

| Attempt | Build exit | First failure or verified milestone |
| --- | --- | --- |
| 01 | failure; numeric code not separately captured | Dune did not yet know the new module target; concurrent Dune registration had not completed. Wrapper exit was 0 as explained above. |
| 02 | 1 | `every_source_has_budget`: `lia` could not solve an existential application-domain metavariable; made `A` explicit in `bt_app`. |
| 03 | 1 | `blocker_application`: a broad reverse rewrite changed both type-argument and result occurrences; proved the application with an explicit substituted result, then simplified that result. |
| 04 | 1 | `quotation_typed` binder case: rewrite did not match the ground variable beneath `weak`. |
| 05 | 1 | Same binder case: restricted simplification still retained a reflexive `eq_rect`. |
| 06 | 1 | Diagnostic print exposed that residual `eq_rect`; replaced restricted simplification with ordinary `cbn` and removed the diagnostic print. |
| 07 | 1 | `code_typed` could not infer the simple arrow type from its unfolded PTS product; supplied `arrow A B` explicitly. |
| 08 | 1 | `quotation_recovery`: incorrect explicit arguments to a congruence projection; switched to the existing parallel congruence lemma. |
| 09 | 1 | Binder substitution retained a reflexive transport; ordinary `cbn` exposed the required substitution equation. |
| 10 | 0 | Generic quotation existence, normality, typing, strong recovery, and structural-erasure injectivity compiled. No new `Print Assumptions` commands yet. |
| 11 | 1 | New finite-telescope `unpack_typed`: application result needed its explicit substitution form before simplification. |
| 12 | 1 | New finite-budget endpoint: recovery theorem concluded an identity renaming; introduced that explicit intermediate result and simplified it afterward. |
| 13 | 0 | Concrete finite telescope, actual blocker context, typing, normality, and recovery compiled; six new assumption reports were closed. |
| 14 | 0 | Packaged syntactic injectivity, coverage of every independently typed STLC source at some budget, and the closed-source ground-binder corollary compiled; nine new assumption reports were closed. |

All fourteen raw logs are preserved unchanged. Failures were corrected in
the source without weakening specifications or suppressing checks.

## Independent recursive kernel check

The following command checks RankedQuotation and recursively checks all of
its imported libraries. It does not use `-admit` or `-norec`:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-self-quote.tP1YlZ/build/default/theories PTSrk -Q /tmp/pts-rk-self-quote.tP1YlZ/build/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-self-quote.tP1YlZ/build/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.RankedQuotation > /tmp/pts-rk-self-quote.tP1YlZ/kernel-check.log 2>&1
```

Exit: 0. The context inventory reports only
`Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep` in
the imported dependency universe. It reports no type-in-type constants,
unsafe fixpoints/cofixpoints, or assumed positivity, and states that Set
is predicative and rewrite rules are not allowed. The nine newly printed
RankedQuotation theorem assumption reports are individually closed.
The dependency-wide inventory and the individual theorem reports are
different reports; neither is substituted for the other. Comparison with
the pristine upstream inventory is performed by the root audit, not by
this subtask's kernel command.

## Exact scope and source identity

The source is the existing independent `ChurchSTLC.has_type` relation.
`bounded_type` adds only a numeric upper bound on the simple function
type at every application. `bounded_type_source` forgets that bound;
`every_source_has_budget` proves coverage at some external natural-number
budget for every source typing derivation.

`finite_budget_quotation` constructs an actual finite context containing
rank-indexed identity blockers and abstracts all blockers into a package.
It proves full original-PTS beta normality, original `Typing.typ` typing,
typed interpretation by the expanded identity-application spine, and
strong original beta reduction to the exact annotated source.
No already-existing quotation, normality, or recovery premise defines
the source domain.

`finite_package_injective` proves syntax-level injectivity at each FIXED
budget, source environment, ground-type variable, and source scope.
Its proof uses a structural eraser plus the concrete variable retraction;
it does not infer syntax equality from beta-convertibility. It does not
assert injectivity across different budget indices.

`every_source_has_normal_representation` supplies a budget and normal
package for every independent STLC source derivation in a compatible
original PTS context. `closed_source_normal_representation` explicitly
abstracts the ground type with the original `lambda o:U0` constructor.
The quotation construction is relational in Rocq Prop, not an extracted
executable quoter. Full dependent quotation/conversion coherence remains
open. The fixed finite-telescope decoder is a separate parallel module;
its verification is not included in these RankedQuotation logs.

Source SHA-256, computed with
`shasum -a 256 theories/self_interpreter/RankedQuotation.v` after attempt 14:

```text
453a46f4935a33712d797357332656f5595a1389b306df5ea3c91373a7d80afc  theories/self_interpreter/RankedQuotation.v
```

This command document and the verification logs were written outside the
repository for transfer into the root agent's durable evidence package.
