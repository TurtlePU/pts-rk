# Incremental combinatory-fold evidence — 22 October 2026

This records the focused development checks of `CombinatoryFold.v` and
`CombinatoryAlgebra.v`. It is **not** a fresh aggregate Dune build, pristine
comparison or full CI claim. The enclosing `AUDIT.sh` records that separate
verification. No existing combinatory source, original PTS rule, shared
documentation or build configuration was changed by this subtask.

## Final result and boundaries

- `CombinatoryFold`: 29 public `Print Assumptions` reports, all closed.
  Finite-dictionary Church trees have code-type sort `r+2`, independently
  of tree size and dictionary arity. Original typing, forward beta folding,
  normality, and literal/conversion injectivity of the tree code are proved.
- Concrete nonidentity interpretations include first-leaf selection, a
  finite-selector constructor test, and a typed CBV continuation algebra.
  `cps_fold_beta` and `cps_fold_apply_beta` compute the original homogeneous
  tree interpretation inside the continuation. `cps_and_test_same_code`
  proves that CPS and the appropriately ranked finite observer accept the
  **same** code, without cumulativity.
- `CombinatoryAlgebra`: 4 public reports, all closed. It constructs the
  actual finite telescope filling and proves literal equality between the
  shared `Algebra.fold` and the tree fold's application spine.
- `finitise_exact` is an executable finite-dictionary bridge for Hilbert
  codes. `catalogue_finite_fold` specializes extraction to the existing
  concrete 65-shape `CatalogueEconomy`, using its proved atom soundness.
  This is syntax/extraction, not an internal evaluator for heterogeneous
  dependent subjects or original-PTS-to-Hilbert completeness.
- Fidelity fixes the dictionary: independently finitised universe atoms
  can have the same one-leaf tree and different dictionaries. The new CPS
  algebra interprets homogeneous applicative trees, not unrestricted
  dependent source conversion. No raw HOAS tag or object-level numeral
  conversion is used by these operations.

Final source SHA-256, checked after the final kernel run:

```text
f6eb001d490754a9f04e10e4c871718f086c21568bc9c60b8408507ebf5f1768  theories/self_interpreter/CombinatoryFold.v
53b5332e0f9b172be9b5b44fd565af8b2a48de3f3e195e9b5db77c982306cc52  theories/self_interpreter/CombinatoryAlgebra.v
```

## Environment and exact command templates

Working directory: `/Users/akuklev/air/pts-rk`.
Pinned environment used for every compilation/check:

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
```

Version checks, all exit 0: `opam exec -- rocq -v` reports Rocq 9.2
compiled with OCaml 4.14.2; `opam exec -- ocamlc -version` reports 4.14.2;
`opam exec -- dune --version` reports 3.23.1. The installed package query
`opam list --installed --columns=name,version` reports `rocq-core 9.2.0`,
`rocq-stdlib 9.1.0`, `rocq-equations 1.3.2+9.2`, and `rocq-prover meta.1`.
Dune was queried, not used by these incremental checks.

Raw logs and generated local `.vo`/`.glob` artifacts are retained at
`/tmp/pts-rk-combinatory-fold.X5L2Jd`, created by
`mktemp -d /tmp/pts-rk-combinatory-fold.XXXXXX` (exit 0).
Each `compile-NN.log` was produced by the following command, substituting
the attempt number `NN`:

```sh
opam exec -- rocq compile \
  -Q _build/default/theories PTSrk \
  -Q _build/default/theories/self_interpreter PTSrk.SelfInterpreter \
  -Q /tmp/pts-rk-combinatory-church-finite.aVVCMj/default/theories/CombinatoryLogic-rk PTSrk.Combinatory \
  -Q /tmp/pts-rk-combinatory-fold.X5L2Jd PTSrk.SelfInterpreter \
  -o /tmp/pts-rk-combinatory-fold.X5L2Jd/CombinatoryFold.vo \
  theories/self_interpreter/CombinatoryFold.v \
  > /tmp/pts-rk-combinatory-fold.X5L2Jd/compile-NN.log 2>&1
```

Each `algebra-NN.log` used this command:

```sh
opam exec -- rocq compile \
  -Q _build/default/theories PTSrk \
  -Q _build/default/theories/self_interpreter PTSrk.SelfInterpreter \
  -Q /tmp/pts-rk-combinatory-church-finite.aVVCMj/default/theories/CombinatoryLogic-rk PTSrk.Combinatory \
  -Q /Users/akuklev/air/pts-rk/_build/unified-algebra-2026-10-22 PTSrk.SelfInterpreter \
  -Q /tmp/pts-rk-combinatory-fold.X5L2Jd PTSrk.SelfInterpreter \
  -o /tmp/pts-rk-combinatory-fold.X5L2Jd/CombinatoryAlgebra.vo \
  theories/self_interpreter/CombinatoryAlgebra.v \
  > /tmp/pts-rk-combinatory-fold.X5L2Jd/algebra-NN.log 2>&1
```

After each invocation the shell saved `$?`, displayed a bounded prefix of
the log with `sed`, and exited with the saved status. Thus the statuses
below are the compiler's, not the display command's. All commands used
existing dependency artifacts; neither incremental success nor the absence
of an error is presented as a fresh dependency audit. Direct load-path
setup prints a remapping warning for the physical `self_interpreter`
directory; it does not disable any compiler check. No timeout occurred.
Start/end timestamps were not captured in these incremental logs; their
numbered order is the retained chronology.

## Complete attempt chronology

`compile-01` through `compile-32` were run in that order. Every failed
attempt exited **1**, and every listed success exited **0**.

| Attempt(s) | Exit | First diagnostic or milestone |
| --- | ---: | --- |
| 01 | 1 | Congruence tactic failed in substitution of tree interpretation. |
| 02 | 1 | Closure beta cleanup could not find the expected literal closure. |
| 03 | 1 | Same closure mismatch, with an explicit printed residual goal. |
| 04 | 1 | Closure beta endpoint remained unsolved. |
| 05 | 1 | Incorrect explicit argument placement for original `typ_app`. |
| 06 | 1 | Remaining `typ_app` argument order/scope mismatch. |
| 07 | 1 | Substituted binary-arrow type not yet rewritten. |
| 08 | 1 | Attempted `subst_shift` rewrite after unfolding `subst`. |
| 09 | 0 | Initial original-typed code and beta-fold core; no public assumption reports yet. |
| 10 | 1 | Dependent finite-branch index required an explicit scope argument. |
| 11 | 1 | Attempted named implicit scope in an `apply` invocation. |
| 12 | 1 | Shifted formation-rank premise was not inferred. |
| 13 | 1 | Variable typing did not match the unreconciled double shift. |
| 14 | 1 | Explicit variable target was not definitionally convertible. |
| 15 | 0 | Normality, intrinsic fidelity and first observer core; 14 closed reports. |
| 16 | 1 | Unspecified scope for the final `normalb` conjunct. |
| 17 | 0 | Generic Hilbert finite-dictionary bridge added; 17 closed reports. |
| 18 | 0 | Concrete finite first-leaf interpretation added; 19 closed reports. |
| 19 | 1 | Invalid unfolding occurrence in continuation-handler typing. |
| 20 | 0 | Continuation carrier, return and combination typing; 19 printed reports. |
| 21 | 1 | Rewriting shifted continuation types also changed the local context. |
| 22 | 1 | Residual shifted substitutions in the CPS handler beta law. |
| 23 | 1 | Residual `fin_match` functions prevented variable-substitution cleanup. |
| 24 | 0 | CPS handler typing and beta law; 19 printed reports. |
| 25 | 1 | Invalid unfolding occurrence while proving the return-combination equation. |
| 26 | 0 | Diagnostic proof script printed a residual goal and **aborted that lemma**; not evidence of its proof. Other 19 reports remained closed. |
| 27 | 0 | Second diagnostic residual-goal/aborted-lemma run; likewise not evidence of the unfinished equation. |
| 28 | 0 | Return-combination equation completed with `Qed`; diagnostic abort removed. |
| 29 | 1 | Generic application congruence needed explicit relation/scope arguments. |
| 30 | 1 | Final continuation application needed the explicit reduction congruence instance. |
| 31 | 0 | Full homogeneous CPS fold typing and beta correctness; 25 closed reports. |
| 32 | 0 | Final exact-rank shared-code observer and concrete 65-shape catalogue instance; **29 closed reports**. |

The adaptor was then compiled:

| Attempt | Exit | First diagnostic or milestone |
| --- | ---: | --- |
| algebra-01 | 1 | Generic telescope-run induction rewrite could not infer the changed scope. |
| algebra-02 | 1 | Same mismatch, with its residual goal printed. |
| algebra-03 | 0 | Explicit induction instantiation proves shared-fold equality; **4 closed reports**. |

No failed proof was retained as an axiom, admission, opaque hypothesis or
disabled check. The final files contain no `Abort` or diagnostic `idtac`.

## Recursive kernel check and source hygiene

This command completed with exit **0**, with output retained as `kernel.log`:

```sh
opam exec -- rocq check -silent -o \
  -Q _build/default/theories PTSrk \
  -Q _build/default/theories/self_interpreter PTSrk.SelfInterpreter \
  -Q /tmp/pts-rk-combinatory-church-finite.aVVCMj/default/theories/CombinatoryLogic-rk PTSrk.Combinatory \
  -Q /Users/akuklev/air/pts-rk/_build/unified-algebra-2026-10-22 PTSrk.SelfInterpreter \
  -Q /tmp/pts-rk-combinatory-fold.X5L2Jd PTSrk.SelfInterpreter \
  PTSrk.SelfInterpreter.CombinatoryFold \
  PTSrk.SelfInterpreter.CombinatoryAlgebra \
  > /tmp/pts-rk-combinatory-fold.X5L2Jd/kernel.log 2>&1
```

Its imported-library inventory contains only the existing upstream
`Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep`.
Set remains predicative; no type-in-type constants, unsafe fixpoints or
assumed positivity are reported. This checks the loaded import closure but
does not independently establish a pristine-upstream comparison.

`git diff --check -- theories/self_interpreter/CombinatoryFold.v
theories/self_interpreter/CombinatoryAlgebra.v` exited 0. A scoped `rg` scan
for admissions, axiom/parameter declarations, aborts, diagnostic printing and
disabled guard/universe/positivity checks returned no matches. The source
hashes above were independently read again while writing this record.
No source edits, builds, staging, commits or pushes were performed while
preparing this evidence note; only read-only version/hash/log checks and
this new documentation file were added.
