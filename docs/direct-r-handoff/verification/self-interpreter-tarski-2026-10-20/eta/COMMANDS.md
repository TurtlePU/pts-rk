# Beta-only eta boundary — 20 October 2026

Base commit: `e822cd62df393faf4d5e4ed0c4c8fed173ccba6f`.
Only `theories/self_interpreter/EtaBoundary.v` and this evidence report were
added by this task. Dune/Audit integration belongs to the parent task. No
commit, push, original-rule change, or unrelated worktree edit was made.

## Exact result and boundary

Let `D = U0 -> U0`, `direct = lambda f:D.f`, and
`expanded = lambda f:D.lambda x:U0.f x`.

- `closed_functions_typing` gives both ORIGINAL closed typing judgments at
  `D -> D`, whose exact sort is `U2`.
- `closed_functions_normal_distinct` and
  `closed_functions_not_convertible` prove both annotated terms normal,
  syntactically distinct, and not convertible by original beta conversion.
- `pointwise_recovery` proves that `direct f x` and `expanded f x` both reduce
  to `f x`, for all raw arguments and scopes. `pointwise_typed` independently
  supplies original typing and beta conversion under the original argument
  typing premises; the domain contains no promised conclusion.
- `dependent_context_wf` constructs the ORIGINAL well-formed context
  `f:D, K:D->U0`. `dependent_indices_typed` gives both `K f` and
  `K (lambda x:U0.f x)` type `U0` there. The final two endpoints establish
  their normality, syntax distinction, and non-convertibility.

Thus pointwise beta agreement is not beta equality of functions and cannot
silently replace beta equality of dependent type indices. This does NOT
assert nonexistence of an internally encoded extensionality theorem, or
impossibility of dependent PHOAS, and adds no eta rule or object-language
extensionality principle. Proofs use the existing common-reduct theorem and
uniqueness of normal forms. All nine public assumption reports are closed.

## Reproduction and retained local evidence

Pinned environment:

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
```

Resolved versions: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2, Dune 3.23.1, opam 2.6.1. Complete package listing and commands:
`_build/self-interpreter-tarski-eta.BmNdln/versions.log` and `VERSIONS.sh`.
Raw outputs are local-only ignored artifacts, not committed evidence files.

Fresh absolute Dune directory: `/tmp/pts-rk-self-tarski-eta.CYUI2p`.
Exact build command, retained in the raw directory's `RUN.sh`:

```sh
timeout 1200 opam exec -- dune build \
  --build-dir=/tmp/pts-rk-self-tarski-eta.CYUI2p \
  --display=short --no-buffer -j 2 theories/self_interpreter/EtaBoundary.vo
```

All attempts:

| Log | Exit | Result |
| --- | --- | --- |
| `attempt-01.log` | 1 | Before Dune registration: unknown target; no compiler invocation. |
| `attempt-02.log` | 0 | First actual compilation succeeds, nine own closed reports. |
| `kernel.log` | 0 | Fresh recursive kernel check below succeeds. |

There were no proof failures, timeouts, theorem weakenings, or unsafe checks.
Known logical-loadpath remapping warnings are retained in the logs.

Exact recursive check, also retained in `CHECK.sh`:

```sh
timeout 1200 opam exec -- rocq check -silent -o \
  -Q /tmp/pts-rk-self-tarski-eta.CYUI2p/default/theories PTSrk \
  -Q /tmp/pts-rk-self-tarski-eta.CYUI2p/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
  -Q /tmp/pts-rk-self-tarski-eta.CYUI2p/default/theories/self_interpreter PTSrk.SelfInterpreter \
  PTSrk.SelfInterpreter.EtaBoundary
```

The loaded-library inventory lists only the already existing upstream
`Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep`.
Type-in-type, unsafe fixpoint, and assumed-positivity inventories are empty;
the nine new theorem assumption reports themselves are closed. The parent
task independently checks the full aggregate against pristine upstream.

`git diff --check -- theories/self_interpreter/EtaBoundary.v` exits 0.
The safety scan for admitted proofs, new axioms/parameters, disabled checks,
or unchecked casts returns no matches (`rg` exit 1).

Frozen source SHA-256:

```text
51d22f51e2724052580fc665fdf7f567f3bbac31beb4c0ecda83b7ba320b316b  theories/self_interpreter/EtaBoundary.v
```
