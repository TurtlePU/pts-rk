# Actual operations over the finite Tarski signature

Date: 2026-10-20. Working directory: `/Users/akuklev/air/pts-rk`.
Source: `theories/self_interpreter/TarskiOperations.v`, 283 lines.
SHA-256: `dd6b69c39e36712ce29df26626f80a0c3d179687193d11c7cee87bf9491311c9`.
Only this new source and evidence are owned by this subtask. The
coordinating agent owns registration, aggregate checks and live handoff.

## Exact endpoint scope

`product_code` and `product_evidence` are the actual two applications of
the finite signature's product and polymorphic law fields to A and B.
The latter is derived from `TarskiLawFamily.family_specialize`: no extra
operation premise assumes the resulting law. For `a,b<=k`, original
input typings `A:C_a` and `B:El_a A -> C_b` establish both operation
typings. The decoded product and decoding the product code both have
the exact original sort `U_c`, where `c=max(a+1,b)`.

`abstract_term` and `application_term` use the actual forward/backward
casts and that specialized law evidence. Their original typings follow
directly from signature lookup and application/conversion rules. Recovery
is not used for subject expansion.

Six recovery endpoints apply the ACTUAL simultaneous substitution
`TarskiSignature.fill` to the original generated term. For every target
scope and bounded rank pair, they reduce product codes and both product
type expressions to the plain dependent product on the replaced inputs;
law evidence to the actual `TarskiIdentity.identity_law`; abstraction to
the literal replaced f; and application to the application of the literal
replaced f and u. No input typing or input normality is needed for these
reduction theorems. Existing input redexes are retained, and no precomputed
normal semantic payload is supplied.

Normal product/law inputs give normal neutral-headed applications.
Normality of casted Abs/App additionally requires the EXPLICIT condition
`normalb (decoded k a b A B) = true`, covering the annotations in the cast
motives and identity functions. A normal lambda-valued B may create a
redex in B x, so normality of B alone is not silently substituted for
this condition. These are local conditional normality results, not a full
dependent quotation theorem or source-conversion generator.

No changed PTS rules, erased annotations, eta, cumulativity, new primitives,
assumed coherence theorem, or function-extensionality premise is introduced.

## Exact commands and all attempts

Fresh absolute Dune directory: `/tmp/pts-rk-tarski-operations.msZgRE`.
Ignored raw evidence: `_build/tarski-operations.hnuCAC`.
Each attempt used `bash _build/tarski-operations.hnuCAC/RUN.sh NN`.
The retained runner is exactly:

```sh
#!/usr/bin/env bash
attempt="$1"
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-tarski-operations.msZgRE --display=short --no-buffer theories/self_interpreter/TarskiOperations.vo > "_build/tarski-operations.hnuCAC/attempt-$attempt.log" 2>&1
build_status=$?
printf '%s\n' "$build_status" > "_build/tarski-operations.hnuCAC/attempt-$attempt.exit"
tail -45 "_build/tarski-operations.hnuCAC/attempt-$attempt.log"
exit "$build_status"
```

| Attempt | Exit | First outcome |
| --- | --- | --- |
| 01 | 1 | Target not yet registered in Dune. |
| 02 | 1 | Concurrent dependency `TarskiSignature.product_at_typed`: hidden finite scope blocked the nth-index rewrite; reported to its owning agent. |
| 03 | 1 | Dependencies compiled; `application_term_normal` needed an explicit cast rank in a local `pose proof`. |
| 04 | 1 | The explicit Boolean calculation required importing `Bool.Bool`. |
| 05 | 0 | Entire operation module compiled, with fifteen closed assumption reports. |

All failures remain recorded. No timeout, theorem weakening, disabled
check or suppressed warning occurred. Final source recompilation reran the
reports rather than relying on a cached success.

Version command, exit 0 (`versions.log`, `versions.exit`):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam list --switch=pts-rk-ci --installed --columns=name,version --short rocq-core rocq-stdlib rocq-equations ocaml dune > _build/tarski-operations.hnuCAC/versions.log 2>&1
version_status=$?
printf '%s\n' "$version_status" > _build/tarski-operations.hnuCAC/versions.exit
```

Actual versions: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2, Dune 3.23.1. Scoped `git diff --check` exits 0.
Safety scanning finds no admissions, axioms, disabled guards/universe
checks or diagnostic Show (rg exit 1). Hashing uses `shasum -a 256`.
The final recursive kernel, pristine inventory comparison, aggregate audit
and full CI are separate coordinating-agent checks, not inferred here.

## Closed assumption reports

All fifteen reports say `Closed under the global context`:

- `product_code_typed`, `product_evidence_typed`, `product_sorts`,
  `abstract_term_typed`, `application_term_typed`;
- `product_code_normal`, `product_evidence_normal`, `abstract_term_normal`,
  `application_term_normal`;
- `product_code_recovers`, `product_evidence_recovers`, `decoded_recovers`,
  `encoded_recovers`, `abstract_term_recovers`, `application_term_recovers`.
