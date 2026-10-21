# Uniform dependent-domain parameter generator

Date: 2026-10-21. Working directory: `/Users/akuklev/air/pts-rk`.
Source: `theories/self_interpreter/UniformTelescope.v`, 292 lines.
SHA-256: `bc22e3ce60f501a8ab5021895ab0ca4dff292fd300c5c5135ce039c78a57de8b`.
Only this new source and scoped evidence were edited; prior modules remain
frozen. Coordinator owns Dune/Audit/prose/handoff. No Git mutation.

## Mathematical boundary

`apply_under D f` is the actual original application spine applying the shifted
base term f to the fresh variables of D, in declaration order. Original typing,
literal replacement/renaming, reduction, neutral-normality and beta recovery
from `CT.close_term D t` are checked. Its syntax depends on the vector/scope,
not the domain annotations. `base_ren`, `base_typing` and `lift_sub_base`
transport actual base terms and commute with the original lifted substitution.
The computational `snoc` retains all earlier annotations and adds one actual
dependent declaration, with formation and exact normality proofs.

`generate_from D todo` adds one family parameter Xi for each rank ri in todo.
Its type is the product closure of U_ri over the accumulated domains. This
parameter's own formation rank is CT.rank(prefix,0), since U_ri:U0. The next
domain annotation is Xi applied to all previous fresh variables. These are
neutral actual application spines, not stored concrete domain syntax.
`parameters n rs` and `domains n rs` instantiate the generator at the empty
prefix over an arbitrary base scope. Both actual telescopes have independently
proved original formation and normal annotations. The generated domain rank
vector equals rs; the number of domain-family parameters is exactly length rs.

If source ranks are at most k, parameter declaration ranks are at most k+1,
and closure over those parameters has rank at most max(k+2,s). No telescope
length bound follows from rank. This module alone does NOT prove that a given
concrete telescope is recovered by a typed parameter substitution; that
universality/reification theorem is a separate subsequent development.
It supplies no full source quoter, extensionality, eta or coherence assumption.

## Verification and exact commands

Fresh build: `/tmp/pts-rk-uniform-telescope.lmNLhB`.
Ignored raw logs: `_build/uniform-telescope.YgVkpR/`.
Final attempt13 exits 0 with EIGHTEEN closed own reports. Independent read-only
review passes without correction. Recursive kernel checking exits 0; loaded
inventory contains only existing upstream functional extensionality, with no
type-in-type, unsafe fixpoints or assumed positivity. Own theorem reports are
closed, distinct from that loaded-library inventory.

Each build ran `bash _build/uniform-telescope.YgVkpR/build.sh NN`. The runner
sets the working directory above, exports the pinned environment, and runs:

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-uniform-telescope.lmNLhB --display=short --no-buffer theories/self_interpreter/UniformTelescope.vo > "_build/uniform-telescope.YgVkpR/attempt-${attempt}.log" 2>&1
build_status=$?
printf '%s\n' "$build_status" > "_build/uniform-telescope.YgVkpR/attempt-${attempt}.exit"
tail -60 "_build/uniform-telescope.YgVkpR/attempt-${attempt}.log"
exit "$build_status"
```

| Attempt | Exit | First outcome |
| --- | --- | --- |
| 01 | 1 | Backward repeated rename-composition rewrite did not terminate promptly. Interrupted only the owned compiler process after about 90 seconds. |
| 02 | 1 | Explicit backward rewrite still did not match the dependent scoped goal. |
| 03 | 1 | Retained diagnostic printed that exact goal; same match failure. |
| 04 | 1 | Fully explicit scopes did not fix rewrite matching. |
| 05 | 1 | Using forward composition on the IH result fixed base typing; application constructor uses explicit U, not T. |
| 06 | 1 | Spine replacement needed explicit equality composition instead of rewriting beneath dependent scope. |
| 07 | 1 | Diagnostic printed that replacement goal; same match failure. |
| 08 | 1 | Explicit IH parameters alone did not fix rewriting. |
| 09 | 1 | Equality transitivity fixed naturality; closure recovery needed the explicit tail telescope and supplied body. |
| 10 | 1 | Replacing the target also rewrote inside the source; use the actual beta step first. |
| 11 | 1 | Generator fresh-parameter type needed a concrete closure-renaming equation at U_r. |
| 12 | 0 | All fifteen initial core/generator reports closed. |
| 13 | 0 | All eighteen final reports closed, including vector rank bounds and annotation-independent spine. |

Attempt01 was an agent-interrupted proof tactic, not a typing rejection or
external timeout. Exact diagnostic/interrupt commands:

```sh
ps -ax -o pid,ppid,etime,%cpu,command | rg 'uniform-telescope|UniformTelescope'
kill -INT 70385
```

PID70385 was confirmed as this attempt's Rocq compiler before interruption.
No diagnostic print remains in the final source. No weakened statement,
admission or disabled check was used. Existing loadpath warnings remain visible.

Versions command (versions.log/.exit, exit0):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam list --switch=pts-rk-ci --installed --columns=name,version --short rocq-core rocq-stdlib rocq-equations ocaml dune > _build/uniform-telescope.YgVkpR/versions.log 2>&1
version_status=$?
printf '%s\n' "$version_status" > _build/uniform-telescope.YgVkpR/versions.exit
sed -n '1,30p' _build/uniform-telescope.YgVkpR/versions.log
exit "$version_status"
```

Rocq9.2.0, Stdlib9.1.0, Equations1.3.2+9.2, OCaml4.14.2, Dune3.23.1.
Recursive kernel command (retained check.sh, kernel.log/.exit, exit0):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-uniform-telescope.lmNLhB/default/theories PTSrk -Q /tmp/pts-rk-uniform-telescope.lmNLhB/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-uniform-telescope.lmNLhB/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.UniformTelescope > _build/uniform-telescope.YgVkpR/kernel.log 2>&1
kernel_status=$?
printf '%s\n' "$kernel_status" > _build/uniform-telescope.YgVkpR/kernel.exit
tail -30 _build/uniform-telescope.YgVkpR/kernel.log
exit "$kernel_status"
```

Hash uses shasum -a256; scoped diff check and no-admission/axiom/disabled-check
scan are separate local checks. Aggregate/pristine/full-CI results belong to
the coordinator, not this targeted build.
