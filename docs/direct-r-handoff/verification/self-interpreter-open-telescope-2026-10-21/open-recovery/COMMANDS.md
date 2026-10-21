# Arbitrary open-body telescope recovery

Date: 2026-10-21. Working directory: `/Users/akuklev/air/pts-rk`.
Source: `theories/self_interpreter/OpenTelescopeRecovery.v`, 493 lines.
SHA-256: `e59f197846642f6e9099410f7df5424bd32406c22c0a9063f16cb8ff12c7321f`.
Only this new proof module and scoped evidence were edited. Prior telescope
sources remain byte-identical at the hashes below. Coordinator owns Dune,
Audit and shared prose/handoff. No Git mutation.

## Mathematical contract

`accumulate_body` and `realized_body` are executable scope-index transports.
They eliminate proved equalities of natural scopes and do not alter any
original term constructor, variable meaning or annotation. Exact arbitrary
body equations `accumulate_close_term` and `accumulate_close_type` generalize
the earlier U_s-only closure result. `realize_term_recovers` and
`realize_type_recovers` prove original forward beta recovery to the LITERAL
concrete lambda/product closure for EVERY open body. The only assumption is
independent original declaration formation of the supplied telescope W;
normality and body typing are not smuggled into these reduction statements.

`realized_spine_recovers` proves that applying the literal concrete lambda
closure to the generated fresh-variable spine reduces to its scope-reindexed
body. It needs no typing or formation premise. `realize_base` proves that the
actual parameter realization preserves every original base variable.
`realized_body_base` commutes with embedding an original base term beneath
the domain telescope. Scope transport preserves applications, full normality
and exact annotated syntax injectivity.

The additional `realized_body_as_rename` characterizes that transport as an
actual original renaming `realized_ren`. Its executable `realized_unren` is
proved inverse in BOTH directions; injectivity and base-variable compatibility
are explicit. Renaming the transported body by that inverse returns the
literal original body. Consequently the existing original syntax naturality
lemmas for decoded products and arrows can be reused without introducing
new operation-specific binder casts.

`telescope_identity_substitutions` constructs BOTH original identity TypedSub
directions across annotation-wise forward reduction, provided each telescope
has independently proved original formation and the bases already have those
identity substitutions. This uses the original variable/conversion rules,
not an equality primitive or a context-validity oracle. Specializing it gives
`realized_identity_substitutions`, `realized_body_typed`, original formation
of the realized domains, and direct original typing of generated lambda/type
closures. No ambient wf restriction is added.

`concrete_argument_typed` types the LITERAL concrete lambda closure at the
instantiated generated product type. Its premises are original formation of
W and original body/type judgments t:T and T:U_s in that telescope. The desired
product is sorted independently; original TYPE conversion then uses the
proved reduction to the literal concrete product. The witness term is not
expanded, eta-contracted, normalized or replaced by a target-typing premise.

This discharges arbitrary open-body/lambda-closure scope recovery. It is not
itself application of a uniform contextual-beta field, a recursive source
quotation, a proof of full dependent coherence, or a full interpreter.
Concrete parameter instantiation may create redexes: no unconditional
normality of the instantiated telescope is asserted.

## Fresh build and attempts

Fresh directories were created by:

```sh
mktemp -d /tmp/pts-rk-open-telescope.XXXXXX
mktemp -d _build/open-telescope.XXXXXX
```

Resolved build: `/tmp/pts-rk-open-telescope.TxPmfc`.
Ignored raw logs: `_build/open-telescope.h03S50/`.
Each attempt ran `bash _build/open-telescope.h03S50/build.sh NN`:

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-open-telescope.TxPmfc --display=short --no-buffer theories/self_interpreter/OpenTelescopeRecovery.vo > "_build/open-telescope.h03S50/attempt-${attempt}.log" 2>&1
build_status=$?
printf '%s\n' "$build_status" > "_build/open-telescope.h03S50/attempt-${attempt}.exit"
tail -60 "_build/open-telescope.h03S50/attempt-${attempt}.log"
exit "$build_status"
```

| Attempt | Exit | First outcome |
| --- | --- | --- |
| 01 | 1 | New target had not yet been registered. |
| 02 | 1 | Coordinator had registered ContextualTelescopeRun before creating its source. |
| 03 | 1 | Same temporary missing sibling source; no proof rejection. |
| 04 | 1 | First real compilation: rewrite could not infer dependent scope in normality lemma. |
| 05 | 1 | Equality transitivity exposed remaining ambiguity between the tail and full rank vector. |
| 06 | 0 | Four initial open lambda/product closure reports closed; normality and raw typing transport also compiled. |
| 07 | 1 | Universe transport rewrite did not match the dependent argument scope. |
| 08 | 1 | Supplying the equality explicitly was insufficient for rewrite matching. |
| 09 | 1 | Equality transitivity and congruence left a tail-vector inference ambiguity. |
| 10 | 0 | Explicit tail indices fixed it; all thirteen typing/closure reports closed. |
| 11 | 1 | Backward rewrite in application-spine recovery did not infer the dependent source index. |
| 12 | 0 | Rewrote the separately instantiated closure-recovery theorem; sixteen reports closed. |
| 13 | 0 | Base-variable preservation added; seventeen reports closed. |
| 14 | 0 | Exact scope transport of lifted base terms added; all eighteen final reports closed. |
| 15 | 1 | Coordinator-requested renaming/bijection extension: dependent vector inference in the inverse equation needed explicit tail indices. |
| 16 | 1 | The inverse proof needed to unfold realized_ren/unren before rewriting their recursive equations. |
| 17 | 0 | All twenty-three final reports closed, including the exact renaming and both inverse equations. |

Before attempt04, one preflight command
`test -f theories/self_interpreter/ContextualTelescopeRun.v && bash _build/open-telescope.h03S50/build.sh 04`
returned1 because the placeholder was still absent; no build ran then. Once
the coordinator created it, the explicit attempt04 above ran and retained
its own compiler log. No timeout or interruption occurred. Existing loadpath
warnings remain visible. No admitted proof, disabled check, axiomatic cast,
or weakened theorem was used.

## Kernel, toolchain and source checks

Final recursive kernel check uses retained check.sh and kernel.log/.exit:

It exited0 after attempt14 and again after attempt17, following the
coordinator's requested renaming interface. The retained final kernel log
is the attempt17 version.
The loaded-library inventory contains only the existing upstream
dependent functional-extensionality entry, distinct from the twenty-three CLOSED
own theorem reports. No type-in-type, unsafe fixpoint or assumed positivity
appears. The scoped diff check exits0; the forbidden-declaration rg scan exits1
(no matches), and its wrapper exits0.

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-open-telescope.TxPmfc/default/theories PTSrk -Q /tmp/pts-rk-open-telescope.TxPmfc/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-open-telescope.TxPmfc/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.OpenTelescopeRecovery > _build/open-telescope.h03S50/kernel.log 2>&1
kernel_status=$?
printf '%s\n' "$kernel_status" > _build/open-telescope.h03S50/kernel.exit
tail -30 _build/open-telescope.h03S50/kernel.log
exit "$kernel_status"
```

Versions command (versions.log/.exit, exit0):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam list --switch=pts-rk-ci --installed --columns=name,version --short rocq-core rocq-stdlib rocq-equations ocaml dune > _build/open-telescope.h03S50/versions.log 2>&1
version_status=$?
printf '%s\n' "$version_status" > _build/open-telescope.h03S50/versions.exit
sed -n '1,30p' _build/open-telescope.h03S50/versions.log
exit "$version_status"
```

Rocq9.2.0, Stdlib9.1.0, Equations1.3.2+9.2, OCaml4.14.2, Dune3.23.1.
The retained source-check.sh records exact scoped diff-check and forbidden
declaration scan commands. Hashes and line counts use shasum -a256 and wc -l.
The three untouched frozen dependency hashes remain:

- ContextualTelescope: `1d3e86333e00942a12264d1507bf041e67a23d952b5b3b7d56a4a8faa1021eaa`.
- UniformTelescope: `bc22e3ce60f501a8ab5021895ab0ca4dff292fd300c5c5135ce039c78a57de8b`.
- UniformTelescopeRecovery: `9bff20445692168310b6dfa17a714f099b4bf0bbf76e3952ab84b9d342f883e6`.

No aggregate, pristine or full-CI claim is inferred from this targeted check.
