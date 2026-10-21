# Actual checked alignment beneath local dependent binders

Source: theories/self_interpreter/LocalCodeAlignment.v (226 lines).
SHA-256: 9d1973a21363f551f2ac924d2e5465418e85da945d073c7521166320f49360bc.
Working directory: /Users/akuklev/air/pts-rk.
Raw evidence: _build/local-code-alignment.TmZ8O9.
Build directory: /tmp/pts-rk-checked-contextual.vLMi7j, same-phase reuse;
this new module had no prior output. Large module aliases were expanded
mechanically to fully qualified references before the first build.

Every attempt used `bash _build/local-code-alignment.TmZ8O9/RUN.sh NN`:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-checked-contextual.vLMi7j --display=short --no-buffer theories/self_interpreter/LocalCodeAlignment.vo
```

- 01: exit 1, generic unbody_filled required an explicit presentation argument.
- 02: exit 1, application commutation through a proof-only scope cast needed body_app rather than definitional conversion.
- 03: exit 1, unfold next_presentation before applying its exact naturality theorem.
- 04: exit 1, supply the actual presentation explicitly to the unbody_filled rewrite.
- 05: exit 1, unfold the contextual filled-term wrapper before comparing scope equality proofs.
- 06: exit 1, dependent rewriting failed to recognize the displayed identical body_filled right-hand side.
- 07: exit 1, retained diagnostic printed the exact reduction and confirmed the same issue.
- 08: exit 1, explicit rewrite arguments did not resolve that dependent rewrite matcher issue; replaced it by direct equality elimination along independently proved body_filled.
- 09: exit 1, nested record's term_shape needed its singleton budget vector explicitly supplied.
- 10: exit 1, outer root/rank equations were generated before the inner judgment fields.
- 11: exit 1, inner fields were shelved, not automatically proved; added Unshelve.
- 12: exit 1, restored fields were inside the last bullet; solve both outer equations without bullets before Unshelve.
- 13: exit 0, final frozen source, seven distinct closed assumption reports. All inner original-typing, normality, neutrality and literal-recovery obligations explicitly solved.

All logs/exits retained. Temporary diagnostic removed. No timeout, admission,
new axiom, unsafe cast, disabled guard/universe check or Git mutation. Scoped
git diff --check exits 0.

Recursive command (`CHECK.sh`):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-checked-contextual.vLMi7j/default/theories PTSrk -Q /tmp/pts-rk-checked-contextual.vLMi7j/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-checked-contextual.vLMi7j/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.LocalCodeAlignment
```

kernel.log/kernel.exit: exit 0. The loaded inventory contains only unchanged
upstream dependent functional extensionality; no type-in-type, unsafe
fixpoints or assumed positivity. All own reports are closed.
Aggregate/pristine verification is separate.

Version command (versions.log/exit, exit 0):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam list --switch=pts-rk-ci --installed --columns=name,version --short rocq-core rocq-stdlib rocq-equations ocaml dune
```

Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2,
Dune 3.23.1.

align_judgment consumes an independently constructed local state, actual
quotation judgment, actual destination code view and original source
conversion. Nat.eq_dec computes the rank comparison; original rank uniqueness
only refutes the impossible negative branch. Actual originally typed normal
carrier/endpoints and their recovered common reduct justify the real finite
lookup. The output contains a computed singleton numeric budget and a
judgment in the exact extended local state, with literal equations for the
renamed destination root and rank. Its neutral normal transport erases under
the real identity fill to the literal old payload, not a normal form.

The scope adapters transport only equal natural-number indices. Constructive
Nat.eq_dec UIP identifies proof-only scope equalities; it adds no axiom and no
object-language eta or extensionality. No equality oracle, source-context
normalization or global quotation-success premise is used. This module supplies
actual local conversion to the recursive quoter; it does not itself assert
all-source recursion coverage. Independent root and audit read-only reviews
PASS; audit reconfirmed the final frozen hash and explicit inner record proofs.
