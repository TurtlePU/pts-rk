# Recursively scoped smart Tarski operations — 21 October 2026

Base commit: `e822cd62df393faf4d5e4ed0c4c8fed173ccba6f`.
This task added only `theories/self_interpreter/ScopedTarski.v` and its
scoped evidence. Parent owns Dune/Audit and shared documentation. No Git/index
mutation or frozen-source edit was made.

## Checked contracts

Every operation accepts an existing `TarskiContext.environment k n G`,
which records an actual typed VARIABLE renaming of the finite signature,
not a source quotation/coherence hypothesis. Inputs range over all original
terms in the current ambient scope, including freshly bound variables.

The smart decoded product reuses `TarskiBinders.bound_apply`. Original
typing of smart Abs/App follows from independently typed inputs and original
well-formedness of G; the concrete spine supplies that well-formedness.
Normality follows from normal A, B and payloads, with normality of the
smart annotation derived rather than assumed separately. Instantiation by
the actual recursively computed `identity_fill` recovers the literal
substituted f, or f applied to u, with no normalization payload or eta law.

`family` and `binder` accept arbitrary family/term bodies in the newly
extended context. Their premises use the actual weakened environment.
`extend_code` constructs the next concrete spine from A:C_a and the existing
decoder typing. Its environment is the weakening; its identity substitution
is literally `transpose` of the parent's substitution. The resulting
identity context retains the literal substituted declaration El_a(A).
`nested_binder_typed` consumes the child environment produced by this
constructor; it needs no extra context-well-formedness premise. This interface
can be used again at the next binder, not merely renamed from a fixed scope.

`binder_recovers` retains the substituted decoder annotation;
`binder_annotation_recovers` additionally beta-reduces its identity decoder
and reaches `lam (replace sigma A) (replace (transpose sigma) body)`.
That reduction does NOT claim that the computed identity context itself is
syntactically canonical. Exact binder-input injectivity, and conversion
injectivity for normal inputs, are local operation properties, not global
source-quotation faithfulness.

Scoped code/term universe views use actual inherited universe laws. The
sort quote correctly uses law ZERO for the original axiom U_r:U_0.
Original typing, normality and literal identity-fill recovery hold at every
spine depth. Exact variable-renaming laws cover smart products, Abs/App,
family/binder, code/term views and sort quotation; binder/sort weakening
corollaries are literal equations. No false arbitrary-substitution equality
for `bound_apply` is asserted.

This is a recursively nestable local interface, NOT a full derivation-directed
dependent quoter or proof of global source-conversion coherence. All 43 own
transitive assumption reports are closed.

Independent read-only review by the paper-analysis agent passed against
the frozen hash below. It checked fresh-scope bodies and the concrete child
spine, arbitrary-depth fill recovery, the additional annotation beta step,
original typing without subject expansion, exact renaming, and the local
(not global-source) fidelity boundary. No correction was requested.

## Commands, versions and every attempt

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
timeout 1200 opam exec -- dune build \
  --build-dir=/tmp/pts-rk-self-scoped-tarski.qA1Bug \
  --display=short --no-buffer -j 2 theories/self_interpreter/ScopedTarski.vo
```

Ignored local-only raw evidence:
`_build/self-interpreter-scoped-tarski.09ttE1/`, containing `RUN.sh`,
`VERSIONS.sh`, `versions.log`, `status.tsv`, and every attempt log.
Versions: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2,
Dune 3.23.1 and opam 2.6.1; full installed-package listing retained.

| Attempt | Exit | First actual result |
| --- | --- | --- |
| 01 | 1 | Dune registration pending; unknown target. |
| 02 | 0 | Generic smart typing/normality and actual spine recovery; 9 closed reports. |
| 03 | 1 | Annotation-reduction proof used ASCII `lam_cong_l`; original helper is `λ_cong_l`. |
| 04 | 0 | Fresh dependent binder, local injectivity and spine extension; 20 closed reports. |
| 05 | 1 | Universe-cast normality application needed its S/e terms explicit before checking reflexivity. |
| 06 | 0 | Scoped universe views and sort quotation; 31 closed reports. |
| 07 | 1 | Evidence-renaming rewrite needed explicit target-context/TypedRen proof arguments. |
| 08 | 0 | Exact renaming/weakening laws; 39 closed reports. |
| 09 | 1 | Concrete spine corollary needed explicit spine argument for `spine_wf`. |
| 10 | 0 | Final concrete-spine corollary and all view-renaming laws; 43 closed reports. |

No timeout, axiom, admitted proof, disabled check or weakened theorem.
Known logical-loadpath remapping warnings remain in the logs. Module
compilation alone is not claimed as a fresh aggregate/pristine/full-CI
verification; that evidence is recorded separately after the milestone freeze.

Frozen source SHA-256:

```text
244dcd3bbb11963ff2c2c0b52ac31e3ef683b69fda42ec98c15b7660ab14fe90  theories/self_interpreter/ScopedTarski.v
```
