# Executable full conversion certificates — 2026-10-21

Source: `theories/self_interpreter/FullConversion.v`, SHA256
`ca5561a92c99882955cb6608a2b23a3a5b3591bf4579a6afa59a53501b829bd5`.
No original kernel or normalization source changed. Independent audit-agent
review passes: actual forward trace constructors, original source typing,
computed structural equality and safe equality transport only.

## Targeted compilation

Working directory `/Users/akuklev/air/pts-rk`; fresh absolute Dune directory
`/tmp/pts-rk-full-conversion.oEqhgU`; raw evidence `_build/full-conversion.HC5pVR`.
For NN = 01 through 05, the exact command was:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-full-conversion.oEqhgU --display=short --no-buffer theories/self_interpreter/FullConversion.vo > _build/full-conversion.HC5pVR/attempt-NN.log 2>&1
status=$?
printf '%s\n' "$status" > _build/full-conversion.HC5pVR/attempt-NN.exit
tail -n 35 _build/full-conversion.HC5pVR/attempt-NN.log
exit "$status"
```

Attempts 01–04 exit 1; 05 exits 0 with 15 own closed reports. No timeout.
First errors, repaired before proceeding:

- 01: `No such bound variable u`; expose the implicit intermediate endpoint
  with explicit `@FS.reduction_append` rather than named eapply argument.
- 02: dependent Fin elimination renamed `j`; give both constructors explicit
  names.
- 03: dependent Fin induction renamed `n`; remove the unnecessary annotation
  on the predecessor projection, leaving its type inferred.
- 04: destructed sort variable was not named `l0`; give all syntax
  constructors explicit names.

The final source is also included in the fresh aggregate assumption and
recursive kernel audit recorded in `../final-review/COMMANDS.md`. Pinned
environment: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2,
Dune 3.23.1, opam 2.6.1; exact version output is in the aggregate raw runner.

## Contract

`greedy_trace`, `rounds_trace` and `normalization_trace` are executable
Type-valued forward reduction evidence for raw original annotated syntax.
`join_attempt` compares computed normalizer outputs structurally and returns
actual joining paths on success. Success is sound for all raw inputs.
Completeness, normality and every-stage original typing require the original
well-formed context and independently typed endpoints. The boolean decision
does not replace `Typing.typ` or purport to decide untyped conversion.

`supplied_conversion_certified` combines independently supplied source data
with the executable attempt. It never interprets arbitrary untyped zigzag
intermediates. Safe `eq_rect` in `make_join` transports the computed literal
endpoint equality; no unsafe cast, extensionality, new axiom or assumed target
quotation is used. Three `vm_compute` regressions check a one-beta trace,
successful beta comparison and rejection of distinct sort literals.

These are source-side metalevel certificates, not a target-language quoter
or generated internal equality evidence.
