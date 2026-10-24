# Decidable raw original-PTS inference and checking — 24 October 2026

Owner: normal_computed_types. Edited only NEW repository source
`theories/CombinatoryLogic-rk/agda/NativeBidirectional.agda` for this task.
Earlier NormalizedInference source remains frozen; no existing native proof,
paper, README, aggregate-driver, staging, commit or push changes.

Toolchain: Agda 2.8.0-3d04bac, Cubical v0.9 commit
`b150186d2544e7efeddd31e5d14a8b9ecbb100f7`.

Each command invokes included CHECK.sh from `/Users/akuklev/air/pts-rk`.
Every attempt has source copies, isolated AGDA_DIR/XDG_DATA_HOME,
`--safe --no-default-libraries --ignore-interfaces` and a 2 GiB heap cap.
Each directory retains exact expanded command, numeric exit, UTC start/end,
complete log, source manifest and snapshots. No checks were weakened.

| Command | UTC start–finish | Exit | Result |
| --- | --- | --- | --- |
| `bash /tmp/pts-rk-native-inference.MkNbTu/CHECK.sh check01` | 02:16:26–02:16:56 | 0 | General inference/checking accepted; two UnsupportedIndexedMatch warnings in optional raw-context validation. |
| `bash /tmp/pts-rk-native-inference.MkNbTu/CHECK.sh check02` | 02:17:29–02:17:58 | 0 | Motive-based WellFormedView replaces fixed-index matching; zero warnings. |
| `bash /tmp/pts-rk-native-inference.MkNbTu/CHECK.sh check03` | 02:18:00–02:18:30 | 0 | Final source including nine executable refl tests; zero warnings. |

Final source: 271 lines; SHA256
`b273673bd07d9884e97c5b75e206791743ca775af6e28f02d2dbbab62c22bddf`.
Source matches check03 snapshot; scoped `git diff --check` passes.
Exact start/end times for all attempts are in their started.txt/finished.txt.

## Mathematical scope

`infer Γ wf t` structurally recurses on original annotated raw syntax. Its
Result either provides original typing at a sorted NORMAL inferred type,
or refutes EVERY original Typ derivation for that subject. It introduces
no separate declarative checking judgment. Recursive contexts extend by the
original raw annotation. Normalization occurs only after native typing is
constructed, using the established total native normalizer.

Negative branches use NativeInversion, uniqueness, normal-form uniqueness
and preservation of product heads. Thus product/sort inspection does not
silently assume that native typing is syntax directed or restricted to a
simple fragment. Application compares the inferred normal argument type
with the normal domain of the inferred function product.

Public decisions:

- `infer? wf t : Dec (Σ A. Typ Γ t A)`.
- `check wf t A : Dec (Typ Γ t A)` for arbitrary raw subjects AND types.
- `wellformed? Γ : Dec (WellFormed Γ)`.
- `check-context Γ t A : Dec (WellFormed Γ × Typ Γ t A)`.

The final function checks arbitrary raw contexts as well, without supplied
well-formedness evidence. All judgments remain the original native ones.

Nine refl regressions: accepted universe; rejected universe mismatch;
rejected nonfunction application; rejected unsorted lambda annotation;
rejected argument mismatch; accepted dependent polymorphic identity and its
dependent application; accepted reducible target type; accepted application
of a variable whose declared function type itself needs beta normalization.

No new axiom, unsafe option, termination override, fuel, assumed target
typing, eta rule, raw annotation erasure or normalization oracle appears.
This does not establish quadratic runtime, a binder-free dependent compiler,
or initiality/equivalence of the independent QIIRT presentation.
