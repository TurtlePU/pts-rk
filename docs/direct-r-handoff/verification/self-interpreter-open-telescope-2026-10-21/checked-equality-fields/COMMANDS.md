# Checked equality-only finite layer

Source: theories/self_interpreter/CheckedEqualityFields.v (312 lines).
SHA-256: 6e1242fab00205dd091cc9be69e419d0f447c25c8062ad789dd2369bdc7aac42.
Working directory: /Users/akuklev/air/pts-rk.
Raw evidence: _build/checked-equality-fields.CRhb68.
Fresh Dune build: /tmp/pts-rk-checked-equality-fields.gkXJMa.

Each attempt used `bash _build/checked-equality-fields.CRhb68/RUN.sh NN`:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-checked-equality-fields.gkXJMa --display=short --no-buffer theories/self_interpreter/CheckedEqualityFields.vo
```

All attempt-NN.log/exit files retained:

- 01: exit 1, nested flat-map membership required successive existential elimination.
- 02: exit 1, descriptor numerical budget definitions remained opaque to lia.
- 03: exit 1, explicit bound conjunction elimination did not unfold those definitions.
- 04: exit 1, temporary goal diagnostic confirmed the same opaque budget; diagnostic removed and definitions explicitly unfolded.
- 05: exit 1, fill typing needed the preceding original context G supplied explicitly.
- 06: exit 1, destructing recursive lookup had already rewritten the induction hypothesis; reflexivity was required instead of the original equation.
- 07: exit 1, lookup typing rewrite needed the abstract entry equality, not indiscriminate unfolding.
- 08: exit 0, 23 closed reports, actual finite context/fill/lookup complete.
- 09: exit 0, frozen source, 24 closed reports, including computed maximum field rank.

Recursive command, scripted in CHECK.sh:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-checked-equality-fields.gkXJMa/default/theories PTSrk -Q /tmp/pts-rk-checked-equality-fields.gkXJMa/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-checked-equality-fields.gkXJMa/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.CheckedEqualityFields
```

kernel.log/kernel.exit: exit 0. The loaded inventory contains only the unchanged
upstream dependent functional extensionality axiom, no type-in-type, unsafe
fixpoints or assumed positivity. All own reports are closed. No timeout,
admission, new axiom, disabled check, frozen-core edit or Git mutation.

Versions command (versions.log/exit, exit 0):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam list --switch=pts-rk-ci --installed --columns=name,version --short rocq-core rocq-stdlib rocq-equations ocaml dune
```

Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2,
Dune 3.23.1. Scoped git diff --check exits 0. Full aggregate/pristine
checking is a separate parent-agent step.

Scope: every descriptor consists ONLY of predicate level and original carrier/
endpoint syntax. The finite vocabulary is source-independent and complete at
computed node/literal budgets. The executable filter checks original typing,
normality, and actual filled-endpoint conversion. Every accepted field is an
equality declaration, independently originally sorted and normal. Its actual
normal realization is an eraser whose full application returns the LITERAL
payload. The finite block has proved original wf, normal context, TypedSub fill,
executable lookup with computed coverage, and computed maximum field rank.
The target context may be empty, yielding closed realizations. Every new field
depends only on the preceding context, never another field in this block.

This is a NONCONTEXTUAL fixed-base layer. It does not yet enumerate hoisted
dependent telescopes, iterate a finite DAG, or prove the global dependent
quotation invariant. It contains no arbitrary semantic-value table.
