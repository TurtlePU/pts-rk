# Structurally common-map binder congruence — 21 October 2026

Base commit `e822cd62df393faf4d5e4ed0c4c8fed173ccba6f`.
Only new `theories/self_interpreter/BinderCongruence.v` and scoped evidence
were edited by this task. Parent owns Dune/Audit and shared prose. No Git/index
mutation or edit to frozen source APIs.

## Mathematical boundary

For D:U_s, X:U_a and C:U_c, a separately originally typed body in
`G,z:D,x:X` defines the actual term
`common_map = lambda z:D.lambda x:X.body(z,x)`.
Its type `D -> (X -> C)` has exact sort `max(s+1,max(a+1,c))`.
The body may depend on BOTH z and x; X and C do not depend on z.
`family_at X body u` is the literal lambda obtained by the actual lifted
substitution for z, and `common_map_beta` proves the original beta step.

An input e:Eq_d(D,u,v), supplied OUTSIDE the x binder, produces an actual
object witness of Eq_d(X->C, family_at(u), family_at(v)). Its equality type
has exact sort `max(max(a+1,c)+2,d+1)`. Original typing is derived from the
independent input typings and original wf G, not a requested output premise.
Reflexive input reduces to literal reflexivity at `family_at(u)`, including
its annotation; no eta equation is used. Exact substitution naturality of
the constructor and its doubly lifted body is proved.

The dependent product-code specialization fixes A:C_a and lets the family
body depend on x:El_a(A) and z:D. It maps the resulting FUNCTION-level
equality through the actual constructor p A. Result equality lives over
C_c:U0 and therefore has exact sort `max(2,d+1)`. The actual identity
product constructor plus reflexive input reduces to reflexivity at the
literal product `Pi x:A.body[u/z]`, with the source annotation retained.

This is a restricted structural binder congruence law. It does NOT lift an
arbitrary family of proofs e_x into function equality, prove general
function extensionality, or translate beta redexes whose only supplied
equality evidence depends on x. It does not construct full source quotation
or internal source-conversion coherence. These map-based proof terms may
contain administrative beta redexes; NO quotation-normality claim is made.

All 14 own transitive Print Assumptions reports are closed.

Independent read-only review by the source-substitution agent passed at the
frozen hash below. It checked the outside-binder equality and fixed D/X/C,
the exact lifted substitution, explicit wf use for preservation, original
rank arithmetic, actual product application and literal annotated product
recovery. No correction was requested; no claim covers a z-dependent domain
or arbitrary pointwise family equality.

A second independent review by the dependent-equality agent also passed at
the same frozen hash. It checked the dependent product specialization,
original rank arithmetic and literal reflexivity computation, and confirmed
that no arbitrary pointwise lift, normality or global-translation claim is made.

## Exact compilation and attempts

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
timeout 1200 opam exec -- dune build \
  --build-dir=/tmp/pts-rk-self-binder-congruence.tkK21j \
  --display=short --no-buffer -j 2 theories/self_interpreter/BinderCongruence.vo
```

Ignored, local-only raw evidence:
`_build/self-interpreter-binder-congruence.UYGHs4/` containing RUN.sh,
VERSIONS.sh, versions.log, status.tsv and every attempt log. Versions:
Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2,
Dune 3.23.1 and opam 2.6.1; complete package inventory retained.

| Attempt | Exit | First actual result |
| --- | --- | --- |
| 01 | 1 | Dune registration pending; target unknown. |
| 02 | 1 | Bare var in fin_match required explicit nat/scope parameters. |
| 03 | 1 | Nested arrow weakening needed the proved arr_shift equation, not definitional conversion. |
| 04 | 1 | Family-at typing application required the source domain/ranks explicitly; unification selected an unrelated sort premise. |
| 05 | 0 | Complete common-map binder core; 9 closed reports. |
| 06 | 0 | Added product-code typing, exact rank, identity/reflexivity and substitution; 14 closed reports. |
| 07 | 0 | Final explicit non-normality boundary comment; 14 closed reports. |

No timeout, axiom, admit, unchecked cast, disabled kernel check or weakened
theorem. Known logical-loadpath warnings remain in the logs. Fresh aggregate,
recursive kernel/pristine and full local CI evidence is separate and is not
claimed from this module compilation alone.

Frozen source SHA-256:

```text
144e1177c901bc2ce6d748d430aa574077ef08394e3c4a6cdaeb6c7dec05f875  theories/self_interpreter/BinderCongruence.v
```
