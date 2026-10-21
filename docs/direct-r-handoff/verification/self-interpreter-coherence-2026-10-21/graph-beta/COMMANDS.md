# Actual finite beta witnesses in dependent graph equality

Date: 2026-10-21. Working directory: `/Users/akuklev/air/pts-rk`.
Owned source: `theories/self_interpreter/TarskiGraphBeta.v`, 174 lines.
SHA-256: `f67b71589ca645e6cd83d675395f86d7a8dd973344e6fa7114fb6fbbfc887d29`.
Only this new source and its scoped evidence were edited by this subtask.
The coordinator owns registration, aggregate audit, prose and live handoff.
No frozen proof source, original kernel, Git index or reference was changed.

## Checked contract

The actual decoded family is `F = lambda x:El_a A. El_b (B x)`.
`decoded_family_typed` derives original `F : El_a A -> U_b` from independent
original decoder/code/family typings. `decoded_family_beta` is the literal
original beta step `F u -> El_b (B u)`; replacement naturality is exact.

`fiber_congruence_convertible` consumes actual forward fiber reduction
`F u ->* C` and original `e : Eq_d(C,y,z)`. Inside the predicate binder it
retypes `P u : F u -> U_d` to `P u : C -> U_d`, using the independently
supplied formation of C and original type conversion. Thus it constructs
`GraphEq_d(A,F,u,y,u,z)` without extracting endpoint typings from an equality
witness, adding a coherence field, or relying on subject expansion. The
motive-type formation rank is exactly b+1 because U_d itself has sort U0.

`beta_graph` applies this operation to the ACTUAL `TarskiBetaSignature`
beta field. Under a,b,d <= k and the independently supplied original input
typings, `beta_graph_typed` proves equality between the actual casted
application-of-abstraction and literal f u, synchronized with the same u.
`filled_beta_graph_typed` uses the actual independently constructed typed
signature substitution, not assumed semantic field realization.

`beta_graph_recovers` replaces all signature variables by that actual fill,
reduces the beta-field evidence to its proved reflexivity value, and reduces
the graph congruence to graph reflexivity. Its endpoint retains the LITERAL
substituted domain and lambda-valued decoded family, substituted u, and
application of substituted f to substituted u. It does not eta-contract the
family, normalize the inputs, assume cast cancellation, or assert normality.
In particular the lambda family introduces administrative beta redexes in
predicate annotations. Full recursive quotation/coherence remains open.

## Verification and exact commands

Fresh absolute Dune build: `/tmp/pts-rk-graph-beta.v7gRB2`.
Ignored raw evidence: `_build/graph-beta.RLeawX/`.
Attempt 02 exits 0 with SEVEN closed own assumption reports. Independent
read-only review by the dependent-equality agent passes without correction.
No source edit was needed after the initial implementation.
Recursive kernel checking exits 0. Its loaded-library inventory contains only
the existing upstream functional-extensionality declaration, no type-in-type,
no unsafe fixpoints and no assumed positivity. This loaded inventory is
distinct from the seven closed theorem-level assumption reports.

Each attempt used `bash _build/graph-beta.RLeawX/build.sh NN`. The runner sets
the working directory above, exports the pinned PATH and OPAMROOT below, and
executes exactly:

```sh
opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-graph-beta.v7gRB2 --display=short --no-buffer theories/self_interpreter/TarskiGraphBeta.vo > "_build/graph-beta.RLeawX/attempt-${attempt}.log" 2>&1
build_status=$?
printf '%s\n' "$build_status" > "_build/graph-beta.RLeawX/attempt-${attempt}.exit"
tail -60 "_build/graph-beta.RLeawX/attempt-${attempt}.log"
exit "$build_status"
```

- Attempt 01: exit 1, target not yet registered by the coordinator.
- Attempt 02: exit 0, final source and all seven reports.

Between those attempts, while waiting for registration, the same fresh
directory built the two direct dependencies (exit 0; dependencies.log/.exit):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-graph-beta.v7gRB2 --display=short --no-buffer theories/self_interpreter/TarskiBetaSignature.vo theories/self_interpreter/DependentEquality.vo > _build/graph-beta.RLeawX/dependencies.log 2>&1
dependency_status=$?
printf '%s\n' "$dependency_status" > _build/graph-beta.RLeawX/dependencies.exit
tail -30 _build/graph-beta.RLeawX/dependencies.log
exit "$dependency_status"
```

No timeout or theorem weakening occurred. Existing logical-loadpath remapping
and dependency deprecation warnings remain visible. No check was disabled.

Version command (exit 0; versions.log/.exit):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam list --switch=pts-rk-ci --installed --columns=name,version --short rocq-core rocq-stdlib rocq-equations ocaml dune > _build/graph-beta.RLeawX/versions.log 2>&1
version_status=$?
printf '%s\n' "$version_status" > _build/graph-beta.RLeawX/versions.exit
sed -n '1,30p' _build/graph-beta.RLeawX/versions.log
exit "$version_status"
```

Actual versions: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2 and Dune 3.23.1.

Recursive kernel command is retained in check.sh, with kernel.log and the
immediately captured kernel.exit:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-graph-beta.v7gRB2/default/theories PTSrk -Q /tmp/pts-rk-graph-beta.v7gRB2/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-graph-beta.v7gRB2/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.TarskiGraphBeta > _build/graph-beta.RLeawX/kernel.log 2>&1
kernel_status=$?
printf '%s\n' "$kernel_status" > _build/graph-beta.RLeawX/kernel.exit
tail -30 _build/graph-beta.RLeawX/kernel.log
exit "$kernel_status"
```

Source hash uses `shasum -a 256`; scoped `git diff --check` exits 0.
The source scan for admissions, new axioms or disabled checks finds no
matches (expected rg exit 1). Aggregate audit, pristine comparison and
full CI are separate coordinating-agent checks.
