# Independent Church proof realization — 2026-10-23

This worker added only HornProofRealization.v and this evidence directory.
The source is frozen at SHA256
`40ac03611a01160f09d8f7d0e589833ada39dc0e800ae973ebcc888398c19945`.
All 13 public assumption reports are closed. Source proofs are the existing
independent FiniteModelSoundness.Proof trees, not native typing derivations.

The compiler folds in arbitrary symbolic atom types and clause handlers,
then lambda-abstracts their entire telescopes. First-match lookup selects an
actual handler variable; its otherwise-default branch is excluded by proved
selected-clause membership. No Boolean model or semantic soundness is an
admission predicate. Every finite Horn derivation is represented by an actual
original annotated PTS term of the independent HornProofEncoding proof type.

The separate introduce_typed theorem accepts arbitrary native Church proofs
of all premises, not merely compiler outputs. It lifts and eliminates each
premise in the same symbolic algebra, applies the selected clause handler,
and abstracts the result. Mismatched premise/witness lists have a total
syntactic fallback, but the theorem's ordinary Forall2 typing hypotheses
exclude that branch. Original syntax, typing and ranks remain unchanged.

## Commands and outcomes

The pinned environment is OPAMROOT
`/Users/akuklev/.local/share/pts-rk-ci/opam`, OPAMSWITCH `pts-rk-ci`.
Dependencies are the previous fresh checked tree
`/tmp/pts-rk-mm0-bridge.IH9mrh/default/theories` and the independently compiled
encoding module in `/tmp/pts-rk-horn-encoding.vF7hVq`.
The worker object directory is `/tmp/pts-rk-horn-realization.GMs4GF`.
These isolated checks reuse existing dependencies; fresh integrated checking
is performed separately by the root agent.

```sh
bash docs/direct-r-handoff/verification/combinatory-internal-horn-2026-10-23/realization/CHECK.sh attempt-13
bash docs/direct-r-handoff/verification/combinatory-internal-horn-2026-10-23/realization/KERNEL.sh kernel-final
```

Each attempt retains its exact command, source hash, start/end UTC, output
and exit code. Attempts 01--07 fail at local induction application or
dependent telescope rewrite/proof elaboration; 08 passes the initial eight
reports. Attempts 09--12 fail while elaborating the additional generic
constructor's implicit parameters and list induction; 13 passes all 13
reports in under one second. No unsafe workaround or theorem assumption was
introduced, and there were no compilation timeouts.

The first full recursive kernel command passes, exit 0,
19:51:30--19:51:43 UTC. Its wrapper then compares raw context-summary bytes
against an archived whitespace-normalized baseline and returns 1 only for
spaces on blank lines. Comparing the raw live pristine baseline is exact.
The corrected wrapper passes under the separate kernel-final label,
19:52:16--19:52:29 UTC, exit 0, preserves the earlier raw outputs, and
compares the complete inventory without skipping dependencies. Only inherited
functional_extensionality_dep occurs; no unsafe or type-in-type entries.

Generated readable evidence is whitespace-normalized only after preservation
of its exact raw bytes in adjacent .raw.gz files. This does not change any
proof source. No staging, commits, pushes, cleanup, original-kernel edits,
Agda changes or MM0 changes were performed.

## Boundary

The fragment, atom enumeration and query remain external fixed parameters.
The construction proves actual source realization and rule introduction; it
does not prove canonical beta correspondence of the compiler, arbitrary
Church code provenance for MM0 syntax, or a single internally quantified
soundness theorem over arbitrary fragments and budgets. The root's separate
consumer proves arbitrary-witness reflection for each fixed finite fragment.
