# Executable original-context reification

Source: theories/self_interpreter/ContextReification.v (119 lines).
SHA-256: ff42deabcd555dacf166236d86b81c5f364c1462e482b4ee809b81ba338c6cf1.
Working directory: /Users/akuklev/air/pts-rk.
Raw evidence: _build/context-reification.2SXE3x.
Dune directory: /tmp/pts-rk-checked-contextual.vLMi7j (same-phase reuse;
this new module had no prior compiled output).

All attempts used `bash _build/context-reification.2SXE3x/RUN.sh NN`:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-checked-contextual.vLMi7j --display=short --no-buffer theories/self_interpreter/ContextReification.vo
```

- 01: exit 1, recursive fixpoint call needed explicit scope before its implicit-argument declaration was established.
- 02: exit 1, dependent elimination renamed the original wf constructor hypotheses; replaced named arguments by original evidence inference.
- 03: exit 1, dependent presentation proof fields prevented direct context rewriting before simplifying the transported body.
- 04: exit 1, temporary diagnostic confirmed that issue; supplied the exact definitionally equal original-typing goal before rewriting.
- 05: exit 0, frozen source, ten distinct closed reports.

Complete attempt logs/exit files retained. Diagnostic removed. No admission,
new axiom, unsafe cast, disabled guard/universe check or Git mutation.

Recursive command (CHECK.sh):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-checked-contextual.vLMi7j/default/theories PTSrk -Q /tmp/pts-rk-checked-contextual.vLMi7j/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-checked-contextual.vLMi7j/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.ContextReification
```

kernel.log/exit: exit 0. Only unchanged upstream dependent functional
extensionality occurs in the loaded inventory; no type-in-type, unsafe
fixpoints or assumed positivity. All own reports are closed. No timeout.
Scoped git diff --check exits 0. Aggregate/pristine checking is separate.

Version command (versions.log/exit, exit 0):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam list --switch=pts-rk-ci --installed --columns=name,version --short rocq-core rocq-stdlib rocq-equations ocaml dune
```

Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2,
Dune 3.23.1.

reify computes from ORIGINAL Ctx syntax only. Each declaration rank is
OriginalTypecheck.type_sort (default zero on malformed contexts); original wf
independently proves those computed ranks correct and the telescope formed.
The literal original context is preserved up to its structural scope equality.
Body and fill transports are ordinary equality elimination along that proved
natural-number equality, not unsafe casts or semantic conversion. They preserve
original typing/TypedSub, exact filled syntax, normality and injectivity.
Normal telescope annotations agree exactly with normal_context. The U17
regression computes declaration sort rank zero, respecting the original cycle.
No original typing proof is used to compute a rank or eliminate a Prop witness
into executable data; no source quotation coverage is claimed.
