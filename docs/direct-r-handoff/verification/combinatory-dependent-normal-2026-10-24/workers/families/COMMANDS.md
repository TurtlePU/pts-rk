# Normalized dependent families: worker evidence

Only new project source `theories/CombinatoryLogic-rk/agda/NormalizedFamilies.agda`
was written by this worker. No original rules, other source, aggregate import,
paper, durable handoff or Git index was changed.

Final source: 239 lines, SHA256
`48ee36886d8c7810874f80f5661c9629171e15f29fc07f653fe6b8055a708e35`.
It is byte-equal to `check-05-cast/source/NormalizedFamilies.agda`.
The original 228-line first-success checkpoint is retained in check-04,
SHA256 `153fdb3d9771861e70305e80540eb45620eb184a267f3a1de86b43e520f79887`.

The full native PTS carrier `NfAt` stores annotated normal syntax and truncated
original `Typ` witnesses. `TyNF` fixes its type to a universe. Normalization
preserves original typing and reflects/preserves native beta equality.
`pullTy` normalizes substituted types; `pullTm` returns an inhabitant of that
NORMAL pulled-back type, using original conversion. Identity/composition are
proved paths; term laws include the required dependent transport. No quotient
path constructor, assumed normalization theorem or eta rule is introduced.
The added `castNF` transports only the truncated typing field, so its normal
code is definitionally unchanged. `castNF-agrees` proves equality with ordinary
Cubical transport; its normal-family endpoints are explicit. This is an
optimization of proof elaboration, not a replacement of dependent transport.

## Exact verification

Driver `check.sh` copies all current Agda sources to a fresh trial directory,
isolates `AGDA_DIR` and `XDG_DATA_HOME`, and invokes pinned Agda with
`+RTS -M2G -RTS --safe --no-default-libraries --ignore-interfaces` on the copied
`NormalizedFamilies.agda`. Each `command.txt` is the exact shell invocation;
`check.log`, `started.txt`, `finished.txt`, `exit-code.txt`, and source snapshots
are retained per attempt. No cache result substitutes for a fresh check.

Toolchain: Agda 2.8.0-3d04bac; Cubical v0.9 revision
`b150186d2544e7efeddd31e5d14a8b9ecbb100f7`.

| Invocation | UTC start | UTC finish | Exit | Outcome |
| --- | --- | --- | --- | --- |
| `bash check.sh 01` | 2026-10-24 02:06:49 | 02:07:29 | 42 | Wrong import owner for `beta-replace`; fixed to NativeAlgebra. |
| `bash check.sh 02` | 2026-10-24 02:07:31 | 02:08:13 | 42 | Two unresolved inference families: pullTm witness and dependent truncation motive. |
| `bash check.sh 03` | 2026-10-24 02:08:28 | 02:09:14 | 42 | Explicit motive still needed explicit source/target context arguments. |
| `bash check.sh 04` | 2026-10-24 02:09:29 | 02:10:14 | 0 | Fresh full import closure, zero warnings. |
| `bash check.sh 05-cast` | 2026-10-24 02:23:41 | 02:24:28 | 0 | Final source with smart reindexing; fresh full closure, zero warnings. |

No suppressed warnings, unsafe pragmas, postulates, holes, termination overrides
or disabled universe/positivity checks. Raw failure logs remain unchanged.

The result is a normalized semantic algebra over original raw contexts, NOT
a standalone simultaneous IIRT, a directly binder-free dependent evaluator,
a full initiality proof or a raw PTS typechecking algorithm. Context/product
integration is delegated to other workers/root and is not claimed by this file.
