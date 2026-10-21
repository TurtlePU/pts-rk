# Uniform telescope naturality and constructive realization

Date: 2026-10-21. Working directory: `/Users/akuklev/air/pts-rk`.
Source: `theories/self_interpreter/UniformTelescopeRecovery.v`, 402 lines.
SHA-256: `9bff20445692168310b6dfa17a714f099b4bf0bbf76e3952ab84b9d342f883e6`.
Only this new source and scoped evidence were edited. Prior ContextualTelescope
and UniformTelescope sources remain frozen. Coordinator owns Dune/Audit/shared
prose/handoff. No Git mutation.

## Mathematical contract and boundary

The first group proves literal substitution/renaming laws for the original
dependent telescope syntax. In particular, `parameters_replace` and
`domains_replace` prove that the uniform generator has no free dependence on
its ambient base variables. Equalities of substitutions are pointwise; no
functional extensionality is used. `telescope_subst_shift` deletes an actual
weakening using the original substitution.

`telescope_reduces` records original forward beta reduction of each literal
domain annotation at its original scope. Both lambda and product closure
preserve this relation, simultaneously with a supplied body reduction.
`parameter_argument E A` is the actual lambda closure of the next declaration
A over its concrete earlier prefix E. `parameter_step_typed` derives its
original typing, including the necessary conversion from the instantiated
generic prefix. `parameter_step_recovers` reduces the freshly generated domain
application to literal A. Neither theorem assumes a quotation/realization law.

`instantiate` recursively computes all parameter values from the supplied
concrete telescope, independently of typing evidence. `realize W` starts with
the empty prefix and the original variable substitution. For EVERY supplied
concrete telescope W with original declaration-formation evidence,
`realize_correct` proves an actual TypedSub from the generated parameter context
to the original context and annotation-wise beta recovery of the generated
domains. No well-formedness restriction on the ambient context is added.
The transparent scope rebasing changes only Rocq indices, never the original
constructors or lambda annotations.

`accumulate_close_type` identifies the accumulated original declarations with
their literal original product closure. `realize_closure_recovers` therefore
recovers the complete original product ending in any U_s, for every formed W.
This is concrete-telescope universality for domain annotations, not merely
formation of a generic template or a finite example. The exported final
closure endpoint ends in U_s; arbitrary open-body/lambda-closure transport
through the accumulated scope equality is NOT claimed. Integrating that
transport with recursive full-source quotation remains separate. No eta,
extensionality, source quoter, or all-index coherence premise is introduced.

## Verification and exact commands

Fresh absolute Dune build directory: `/tmp/pts-rk-uniform-recovery.K4yVKo`.
Ignored raw logs: `_build/uniform-recovery.H2yPjr/`.
Final attempt17 exits 0 with NINETEEN closed own assumption reports. All
attempts, including first failures, remain recorded. Independent read-only
review passes without correction. Recursive kernel checking exits 0: only
the pre-existing upstream functional-extensionality entry appears in the
loaded-library inventory; own reports are closed. No unsafe fixpoint,
type-in-type or assumed positivity appears.

Each build ran `bash _build/uniform-recovery.H2yPjr/build.sh NN`. The retained
runner sets the working directory above, exports the pinned environment, then:

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-uniform-recovery.K4yVKo --display=short --no-buffer theories/self_interpreter/UniformTelescopeRecovery.vo > "_build/uniform-recovery.H2yPjr/attempt-${attempt}.log" 2>&1
build_status=$?
printf '%s\n' "$build_status" > "_build/uniform-recovery.H2yPjr/attempt-${attempt}.exit"
tail -60 "_build/uniform-recovery.H2yPjr/attempt-${attempt}.log"
exit "$build_status"
```

| Attempt | Exit | First outcome |
| --- | --- | --- |
| 01 | 1 | Module target not yet registered by coordinator. |
| 02 | 1 | Over-unfolding under a lifted substitution hid the pointwise square rewrite. |
| 03 | 1 | Generator pair needed explicit fst reduction before rewriting the induction hypothesis. |
| 04 | 1 | Temporary diagnostic printed that pair goal; same match failure, subsequently fixed. |
| 05 | 0 | Six initial naturality reports closed. |
| 06 | 0 | Ten reports, including identity/rename/substitution helpers. |
| 07 | 0 | Fourteen reports, including actual one-step typed parameter realization. |
| 08 | 1 | A nondependent match did not retain the original telescope scope. |
| 09 | 1 | Explicit transparent telescope projection needed the actual surviving tail name. |
| 10 | 1 | Rewrite did not infer the dependent closure index; explicit equality transitivity fixed it. |
| 11 | 0 | Transparent scope rebasing and literal accumulated closure compiled. |
| 12 | 1 | Dependent elimination renamed the rank binder used by the recursive proof. |
| 13 | 1 | Elimination pattern needed the qualified CT.tcons constructor. |
| 14 | 1 | Remaining rank list was renamed; read its actual type for the final generated pair. |
| 15 | 1 | Identity-substitution helper is replace_var, not replace_id; used proved rename equations. |
| 16 | 1 | Reflexive reduction needed an actual proof assertion, not the tactic name as a term. |
| 17 | 0 | All nineteen final reports closed, including every formed concrete telescope. |

No timeout or interruption occurred in this module's attempts. The diagnostic
print from attempt04 is absent from the final source. No weakened statement,
admission or disabled check was used. Existing loadpath warnings are retained.

Versions (versions.log/.exit, exit0):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam list --switch=pts-rk-ci --installed --columns=name,version --short rocq-core rocq-stdlib rocq-equations ocaml dune > _build/uniform-recovery.H2yPjr/versions.log 2>&1
version_status=$?
printf '%s\n' "$version_status" > _build/uniform-recovery.H2yPjr/versions.exit
sed -n '1,30p' _build/uniform-recovery.H2yPjr/versions.log
exit "$version_status"
```

Rocq9.2.0, Stdlib9.1.0, Equations1.3.2+9.2, OCaml4.14.2, Dune3.23.1.
Recursive kernel check (`bash _build/uniform-recovery.H2yPjr/check.sh`, exit0):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-uniform-recovery.K4yVKo/default/theories PTSrk -Q /tmp/pts-rk-uniform-recovery.K4yVKo/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-uniform-recovery.K4yVKo/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.UniformTelescopeRecovery > _build/uniform-recovery.H2yPjr/kernel.log 2>&1
kernel_status=$?
printf '%s\n' "$kernel_status" > _build/uniform-recovery.H2yPjr/kernel.exit
tail -30 _build/uniform-recovery.H2yPjr/kernel.log
exit "$kernel_status"
```

`source-check.sh` retains exact scoped diff-check and forbidden-declaration scan
commands for all three owned telescope modules. Diff-check exits0; rg exits1
(no matches), and the wrapper exits0. Source hash and line count use
`shasum -a 256` and `wc -l`. Aggregate/pristine/full-CI claims belong to the
coordinator and are not inferred from this targeted build.
