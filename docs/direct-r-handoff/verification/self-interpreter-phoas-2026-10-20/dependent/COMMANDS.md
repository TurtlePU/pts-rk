# Dependent indexed PHOAS: local operations

Source: theories/self_interpreter/DependentPHOAS.v.
SHA-256: 13ea13586b288fd8a96a29285a1f1dc160892682506624b51d4c3e9da881387b.
Working directory: /Users/akuklev/air/pts-rk.
Fresh build: /tmp/pts-rk-dependent-phoas.c2ILfZ.
Raw local evidence: _build/dependent-phoas.x8vKes.

## Exact commands and attempts

Every compilation used this command, redirecting stdout/stderr to
attempt-NN.log and immediately recording its numeric exit in attempt-NN.exit:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-dependent-phoas.c2ILfZ --display=short --no-buffer theories/self_interpreter/DependentPHOAS.vo
```

Attempt 01 used the literal command above. Attempts 02–14 used
`bash _build/dependent-phoas.x8vKes/RUN.sh NN`; that retained runner exports
the same PATH/OPAMROOT and OPAMSWITCH=pts-rk-ci, invokes the exact command,
and records both outputs and status. No timeout occurred.

| Attempt | Exit | First result/error |
| --- | --- | --- |
| 01 | 1 | New module not registered in Dune yet; no Rocq check attempted. |
| 02 | 1 | Family application needed explicit input rank b. |
| 03 | 1 | Application helper needed explicit shifted domain. |
| 04 | 1 | Compact multi-goal constructor tactic selected an unsuitable constructor. |
| 05 | 1 | Over-reduced max expression hid the arithmetic rule goal from lia. |
| 06 | 1 | Nonexistent numbered occurrence in shift unfolding. |
| 07 | 0 | Dependent product/case/polymorphic typing and plain identity handlers. |
| 08 | 0 | Complete identity specialization/recovery and universe decoder interface. |
| 09 | 1 | Applied-handler substitution equality needed shift normalization. |
| 10 | 1 | Redundant reflexivity after syntax_simp had closed its goal. |
| 11 | 1 | Second substitution equality retained variable-replacement versus renaming. |
| 12 | 1 | Same remaining equality displayed explicitly for diagnosis; no admission. |
| 13 | 0 | Complete source, fourteen closed public assumption reports. |
| 14 | 0 | Comment-only clarification of the candidate sort-interpretation convention; same fourteen closed reports. |

Recursive kernel checks, kernel.log/kernel.exit after attempt13 and
kernel-final.log/kernel-final.exit after comment-only attempt14, both exit 0:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-dependent-phoas.c2ILfZ/default/theories PTSrk -Q /tmp/pts-rk-dependent-phoas.c2ILfZ/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-dependent-phoas.c2ILfZ/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.DependentPHOAS
```

Loaded-context inventory contains only existing upstream
functional_extensionality_dep; no unsafe fixpoints, assumed positivity,
type-in-type or additional axioms. All fourteen new printed reports are
closed. Independent read-only source/contract review passes.

Actual installed versions were recorded by the following command
(versions.log/versions.exit, exit 0):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam list --switch=pts-rk-ci --installed --columns=name,version --short rocq-core rocq-stdlib rocq-equations ocaml dune
```

Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2,
Dune 3.23.1. Source SHA recorded with shasum -a 256. Source safety scan
for admissions, axioms and disabled checks has no matches (rg exit 1);
scoped git diff --check exits 0. Parent owns aggregate audit/CI integration;
those additional checks are not inferred from these targeted results.

## Exact positive contract and remaining gap

For Fa:U_a->U_a, Fb:U_b->U_b, Fc:U_c->U_c, c=max(a+1,b),
A:U_a and B:(Fa A)->U_b, the actual original product is
D=Pi x:Fa A. Fb(B x). B may genuinely depend on x.
product_sort and dependent_handler_type_sorts prove D:U_c and the
polymorphic Abs/App interface types at U_(c+1), including the dependent
family binder. dependent_abs_operation_typing and
dependent_app_operation_typing are the corresponding original typing rules.

dependent_indexed_identity_handlers_typing constructs the real closed
identity-specialized Abs/App inhabitants. dependent_abs_recovers and
dependent_app_recovers prove their strong original beta behavior, without
normalizing the supplied source. dependent_identity_application_typed
derives the actual applied App handler's original dependent result type
B u DIRECTLY from original typing premises, not by subject expansion.

Under the candidate convention interpreting sort literals by themselves,
the local universe decoder El_b:F0(U_b)->U_b is well-sorted at U_1,
because every U_b:U_0. This convention is not forced on every possible
translation by rank alone. universe_decode_identity_typed constructs its actual
identity instance and universe_decode_identity_recovers proves its beta law.

This is NOT yet a full dependent PHOAS quotation construction. The family
B:Fa A->U_b is an explicit parameter; no source-to-represented-family
translation for arbitrary B:A->U_b has been silently assumed or established.
No generic conversion coherence law for neutral El/Abs/App is assumed.
The first remaining obligation is a recursive, substitution- and conversion-
coherent interpretation of original dependent types and contexts. The
shared-map obstruction is separate; these local positive results do not
rule out another indexed dependent representation. No core rule changed,
no semantic source payload was used, and no commit/push was performed.
