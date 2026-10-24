# Internal finite-map coherence

New source: `theories/CombinatoryLogic-rk/FiniteMapCoherence.v`.
SHA256: `9c862744aad1b8002c7b10b041591a85406b3515c66936316f572b7696c0273b`.
All 25 public assumption reports are closed. The earlier transport source
remains unchanged at SHA256
`841fd328d821e409016f0f38ae4a335b2205cb2fec671813548f560d5e002c5c`.

The ordinary original-PTS Leibniz type
`Eq_k x y = Π P : Code_k → U1. P x → P y` has rank three.
Its native formation, reflexivity, substitution, renaming and forward-beta
congruence are checked. No native equality primitive or eta law is added.

The independent `generated k 3 q` family provides finite dependent
elimination at this equality predicate. Each canonical branch is proved by
actual finite-table beta reduction and Leibniz reflexivity. The resulting
uniform consumers accept arbitrary open typed queries and generation
evidence. Their explicit types contain the desired equality, not merely
an opaque family application, and have rank at most five.

The generic metalevel `Program` description contains identity, finite-table
application and composition, and emits only original PTS terms. Pointwise
agreement of its finite maps supplies the canonical branches; it is not a
semantic equality or coherence conclusion assumed in a source typing rule.
Public specializations include:

- composition: `Eq(map_g(map_f q), map_h q)` when `g(f i) = h i`;
- retraction: `Eq(map_g(map_f q), q)` when `g(f i) = i`;
- identity: `Eq(map_id q, q)`.

Each consumer additionally requires independent rank-three generation
evidence for `q`. No exhaustiveness theorem for arbitrary bare Church codes,
uniform fragment-budget theorem or internal consistency result is claimed.

## Verification

Every compile attempt retains exact command, UTC timestamps, exit status,
source snapshot and hash. Both use the pinned Rocq 9.2 environment and the
preceding indexed-provenance fresh dependencies, with the new transport and
generated-code objects on additional loadpaths.

| Attempt | UTC start–end (2026-10-23) | Exit | Result |
| --- | --- | --- | --- |
| 01 | 22:50:57–58 | 1 | Specialization failed to infer metalevel Program indices. |
| 02 | 22:51:06–09 | 0 | Explicit indices fix elaboration; 25 closed reports. |

The complete recursive kernel check passes; exact command/timestamps/status
are retained in `kernel.command`, `kernel.start`, `kernel.end`, `kernel.exit`.
The normalized entire inventory equals the preceding fresh pristine report
byte-for-byte: inherited `functional_extensionality_dep` only, no assumed
positivity, unsafe fixpoints, type-in-type or rewrite rules. Normalization
only removes trailing whitespace and trailing blank lines.

Object loadpath: `/tmp/pts-rk-finite-map-coherence.yhY8kT`.
No existing source, Dune file, compiler setting or safety check was changed.
The parent task performs the fresh integrated audit.
