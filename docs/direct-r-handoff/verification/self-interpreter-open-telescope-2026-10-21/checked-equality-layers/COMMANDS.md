# Numeric-vector equality-only DAG layers

Source: theories/self_interpreter/CheckedEqualityLayers.v (230 lines).
SHA-256: 5f1e847ed58ab8878fab9d2327c818869ad7b9cf57dc10bcece86f1263690ce4.
Working directory: /Users/akuklev/air/pts-rk.
Raw evidence: _build/checked-equality-layers.3bssvV.
Dune directory: /tmp/pts-rk-checked-contextual.vLMi7j (reused from the same
phase to conserve disk space; this new module had no cached .vo).

Every attempt used `bash _build/checked-equality-layers.3bssvV/RUN.sh NN`:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-checked-contextual.vLMi7j --display=short --no-buffer theories/self_interpreter/CheckedEqualityLayers.vo
```

Complete logs/exit statuses retained:

- 01: exit 1, module had not yet been registered in parent-owned Dune.
- 02: exit 1, ChurchSyntaxFaithful has no inner same-name module.
- 03: exit 1 after scoped SIGINT to the identified worker (PID 90447): reverse repeated rename-composition rewriting ran without progress; no other process was stopped.
- 04: exit 1, a 10-second diagnostic tactic timeout confirmed the reverse-rewriting loop. Diagnostics/timeout removed; proof changed to forward normalization of an independently constructed induction result.
- 05: exit 1, destruct on Fin 0 could not generalize the dependent empty-context typing goal.
- 06: exit 1, same empty-context goal after the independently typed allocation tranche was added.
- 07: exit 0, 21 closed reports.
- 08: exit 0, same reports plus executable layer/slot regressions.
- 09: exit 0, frozen source, 23 closed reports including literal context-index preservation.

Recursive check (CHECK.sh):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-checked-contextual.vLMi7j/default/theories PTSrk -Q /tmp/pts-rk-checked-contextual.vLMi7j/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-checked-contextual.vLMi7j/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.CheckedEqualityLayers
```

kernel.log/exit: exit 0. Loaded inventory has only unchanged upstream
dependent functional extensionality; no type-in-type, unsafe fixpoints or
assumed positivity. Every own report is closed. No admission, new axiom,
disabled kernel check or Git mutation. Scoped git diff --check exits 0.
Aggregate/pristine CI remains a separate parent-agent task.

Version command (versions.log/exit, exit 0):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam list --switch=pts-rk-ci --installed --columns=name,version --short rocq-core rocq-stdlib rocq-equations ocaml dune
```

Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2,
Dune 3.23.1.

An independently fixed realized base and a finite vector of numeric
(telescope-length,node,literal) budgets determine the entire signature and
closed identity fill. Every step appends the COMPLETE checked contextual
equality-only layer at that budget. Actual wf, normal context and TypedSub
are preserved. Existing syntax embeds injectively with exact original
lookup/typing, normality and literal fill preservation; old programs are
not regenerated, normalized or merged.

allocate_original computes the numeric bounds of an independently formed,
typed, normal contextual descriptor with convertible filled endpoints. It
case-splits the executable lookup to return an actual finite slot in Type.
Coverage only refutes the None branch; no witness is extracted from Prop.
The corresponding field has original typing and its exact closed fill.
vm_compute regressions confirm an actual one-field numeric layer and slot.
This is sequential signature infrastructure, not a completed source-directed
recursive quoter or a claimed uniform single-rank budget for all sources.
