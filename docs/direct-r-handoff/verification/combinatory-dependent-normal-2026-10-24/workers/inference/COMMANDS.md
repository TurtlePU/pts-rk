# Full original-PTS computed normal types — 24 October 2026

Owner: normal_computed_types. Edited only new repository source
`theories/CombinatoryLogic-rk/agda/NormalizedInference.agda`; no index, commit,
existing native proof, paper, README, or aggregate-driver changes.

Toolchain: Agda 2.8.0-3d04bac, Cubical v0.9 commit
`b150186d2544e7efeddd31e5d14a8b9ecbb100f7`.

Every invocation below runs the included `CHECK.sh`: source copies, isolated
AGDA_DIR/XDG_DATA_HOME, `--safe --no-default-libraries --ignore-interfaces`,
and a 2 GiB RTS heap cap. Exact expanded commands, numeric exits, UTC times,
logs, source manifests and source snapshots are retained per check directory.
All invocations were from `/Users/akuklev/air/pts-rk`.

| Command | UTC start–finish | Exit | Result |
| --- | --- | --- | --- |
| `bash /tmp/pts-rk-normal-inference.DmOPAJ/CHECK.sh check01` | 02:06:49–02:07:30 | 42 | Dependency NormalizedFamilies imported beta-replace from the wrong native module; one export warning and scope error. |
| `bash /tmp/pts-rk-normal-inference.DmOPAJ/CHECK.sh check02` | 02:07:44–02:08:26 | 42 | Dependency NormalizedFamilies had unsolved pullTm-sound and compose-action-sound motive metas. |
| `bash /tmp/pts-rk-normal-inference.DmOPAJ/CHECK.sh check03` | 02:09:06–02:09:52 | 42 | Dependency NormalizedFamilies needed explicit hidden contexts in compose-action-sound. |
| `bash /tmp/pts-rk-normal-inference.DmOPAJ/CHECK.sh check04` | 02:10:10–02:10:57 | 0 | Entire import closure passes; zero warnings. |

Final source is 217 lines, SHA256
`2b38ac81b79b4dac188a9b0edf4fb899d061a3de66e85d0d3ad622ed494f9ba8`.
`cmp` against the check04 snapshot and scoped `git diff --check` both exited 0.
No holes, postulates, termination overrides, or unsafe flags were introduced.

## Checked statements and scope

`Tm Γ` stores a normal original annotated term and mere original typability,
not a selected type or typing derivation. `tyOf` and `rankOf` compute its
unique normal type and that type's universe rank. Native uniqueness and
normalization coherence prove elimination of the typing truncation valid;
`wellformed-independent` also removes dependence on the supplied context
well-formedness proof. This rank is not a claimed whole-term redex bound.

`type-normal`, `type-sorted`, `has-type`, and `computed-type` retain original
typing. `fibre-iso` identifies computed-type fibres at each normal type with
NormalizedFamilies.NfAt. `normalizeTm` accepts every original derivation,
with forward reduction and exact native beta coherence/reflection across
different result types. `normalizeMere` accepts mere original typability.

`conversion?` decides native beta on these normal subjects; `check-type?`
decides original typing at a normal candidate type for an already typable
normal subject. It does not decide raw untyped typability. Three `refl`
tests check universe/identity computed types and identity rank.

Ordinary records and Sigma types suffice for this semantic interface. No
new simultaneous IIRT, binder-free dependent normalizer, QIIRT initiality,
raw inference decision, or runtime-memory bound is claimed.
