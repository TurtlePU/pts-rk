# Closed original Tarski cast programs — 20 October 2026

Base commit: `e822cd62df393faf4d5e4ed0c4c8fed173ccba6f`.
This task added only `theories/self_interpreter/ClosedTarskiCasts.v` and its
evidence; parent owns Dune/Audit integration. No commit or push was made.

## Checked contract

For each external rank `c`, actual original closed terms `forward c` and
`backward c` bind `S:Uc`, `T:Uc`, and a witness of `TarskiCasts.type_law c S T`.
Their bodies invoke the already proved local forward/backward casts. An
external boolean selects direction in the shared builder; no boolean primitive
is added to original PTS syntax.

- `closed_casts_typing`: direct original judgments for both closed programs.
- `closed_cast_types_sort`: both program types have exact sort `U_(c+3)`.
- `closed_casts_normal`: both programs AND their annotated types are normal.
- `program_specializes`: three administrative beta steps expose the local
  cast, uniformly over raw arguments and scopes.
- `run_typed`: the three applications have original typing from independently
  typed inputs; this is not inferred by subject expansion from their reduction.
- `closed_casts_reflexivity`: applying either program to a reflexivity witness
  and then a term reduces to that LITERAL original term, without eta expansion
  or precomputed normalization.

The law remains a typed object input, not an assumed definitional equality.
These are local transport programs, not a full dependent PHOAS interpreter or
proof of generic neutral-cast cancellation. All six own assumption reports
are closed.

## Exact commands, environment, and all attempts

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
timeout 1200 opam exec -- dune build \
  --build-dir=/tmp/pts-rk-self-tarski-closed-casts.ibg4qq \
  --display=short --no-buffer -j 2 theories/self_interpreter/ClosedTarskiCasts.vo
```

Raw local-only ignored artifacts:
`_build/self-interpreter-tarski-closed-casts.30yf2m/`, containing `RUN.sh`,
`VERSIONS.sh`, `versions.log`, `status.tsv`, and every attempt log.
Versions: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2,
Dune 3.23.1, opam 2.6.1; full package listing retained.

| Attempt | Exit | First actual result |
| --- | --- | --- |
| 01 | 1 | Dune registration pending; unknown target, no compiler invocation. |
| 02 | 1 | Constructor tactic ambiguity in nested product formation. |
| 03 | 1 | Remaining nested substitution/renaming identity in specialization. |
| 04 | 1 | Needed explicit reduction of lifted substitution and Fin transports. |
| 05 | 1 | First applied-type substitution retained composed shifts. |
| 06 | 1 | Second applied-type substitution retained shifts of variables. |
| 07 | 0 | Complete module, six closed reports. |

Corrections only made binder/substitution calculations explicit. No theorem
was weakened and no axiom, admitted proof, unsafe check or timeout occurred.
Known logical-loadpath remapping warnings remain in the logs.

The fresh combined recursive kernel/pristine/full-CI check is recorded
separately in `../final-review/COMMANDS.md`; no standalone kernel claim is
made by the module compilation alone. Scoped whitespace check exits 0.

Frozen source SHA-256:

```text
8f582984be873f3c9d99d019158d3655aedc4b408f587242bf97ba53e2657f62  theories/self_interpreter/ClosedTarskiCasts.v
```
