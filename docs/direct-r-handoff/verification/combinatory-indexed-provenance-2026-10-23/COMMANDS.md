# Internally indexed guarded fragments — 2026-10-23

Six new modules, 120 closed public reports:

| Module | Reports |
| --- | ---: |
| FiniteTypeDispatch | 14 |
| IndexedHornEncoding | 17 |
| IndexedHornRealization | 17 |
| MM0GuardProvenance | 33 |
| IndexedHornSoundness | 16 |
| MM0IndexedReflection | 23 |

The proof family quantifies an arbitrary rank-one predicate over Church
atom codes, independently of any model. The actual original-PTS consumer
binds both query and proof internally; its type has rank four. It returns
the syntactic family T(q) for arbitrary open q, with truth-proposition beta
reduction at canonical selectors. No selector exhaustiveness or canonicity
is used in generic typing. Exact closed inhabitation and Void specialization
retain external native canonicity. Fixed support is query-independent;
source iff uses canonical atom indices, not every duplicate support position.
An executable duplicate-alias regression proves why that boundary matters.

Independent raw guards preserve None versus Some EZ, reconstruct actual
selected source rules and sorted substitutions, and reflect arbitrary raw
derivations without introducing proofs through observation aliases. The
indexed raw bridge reconstructs literal source proofs from arbitrary closed
inhabitants and proves exact source coverage over finite budgets. Raw support
is externally query-seeded; this is not an internal raw decoder or a uniform
budget-polymorphic soundness theorem. There is no new cost bound.

## Isolated development evidence

These checks reuse the preceding fresh dependency objects, and are not fresh
full-library evidence. Exact outputs and command/timestamp/exit ledgers:

- `internal/`: type-dispatch attempts01/02/03 fail on a reserved identifier,
  an overbroad mechanical identifier rename affecting tactic syntax, and
  omitted congruence class arguments. Attempt04 passes14 closed reports,
  20:37:41UTC. Exact start/end files retain second-resolution timing.
- [encoding/COMMANDS.md](encoding/COMMANDS.md): attempts01/02 fail on native
  shifted substitution rewriting;03 passes17 reports. UTC compile timestamps
  were not captured, but original tool durations are retained. Full recursive
  kernel passes20:33:21–33UTC, inventory equal to prior fresh pristine.
- [realization ledger](../combinatory-indexed-horn-2026-10-23/realization/COMMANDS.md):
  final attempt06 passes17 reports20:38:21–23UTC; full recursive kernel
  passes20:38:53–20:39:05UTC, inventory equal to prior fresh pristine.
- [raw provenance ledger](../combinatory-guard-provenance-2026-10-23/provenance/RESULTS.md):
  final attempt17 passes33 reports20:41:40–44UTC; frozen-source kernel03
  passes20:42:33–55UTC. Earlier attempts and the earlier kernel overlapping
  a comment-only safety edit are retained, not used as final hash evidence.
- [consumer/COMMANDS.md](consumer/COMMANDS.md): attempts01–06 fail on inference
  and the literal eta-expanded shift renaming;07 passes16 reports20:45:06–08UTC.
  Full recursive kernel passes20:45:32–45UTC, inventory equal to prior pristine.
- [MM0 integration ledger](../combinatory-indexed-horn-2026-10-23/mm0/COMMANDS.md):
  final attempt05 passes23 reports20:48:21–26UTC. Temporary diagnostics are
  removed; no proof statement is weakened to repair compilation.

ARCHIVE-ISOLATED.sh preserves the encoding/consumer raw outputs and adjacent
gzip copies before whitespace-only readable normalization. Other worker
evidence folders are linked above and remain intact. The six source files
are frozen; independent read-only review found no blocking proof/rank defect.

## Fresh verification

```sh
bash docs/direct-r-handoff/verification/combinatory-indexed-provenance-2026-10-23/AUDIT.sh
```

Fresh 69-module audit PASSES all gates,exit0,20:49:13–20:52:38UTC. Live logs
`_build/combinatory-indexed-provenance-audit.rya6B6`, fresh absolute build
`/tmp/pts-rk-indexed-provenance.cjt8S0`, pristine checkout
`/tmp/pts-rk-indexed-provenance-pristine.8LBsHH`, archive `audit.emobKi`.
The driver explicitly checks1100 own/1101 aggregate closed reports,120 new;
complete recursive inventory equality with freshly built pristine; all63
preceding proof hashes; unchanged native kernel/MM0/52Agda sources; exactly
six additive Dune registrations; before/after source stability; safety and
whitespace. Compilation20:49:23–20:52:08UTC(165s) passes with the exact
1100/1101 report counts. Full recursive kernel20:52:08–35UTC(27s) passes;
the COMPLETE inventory is byte-equal to freshly built pristine, inherited
functional_extensionality_dep only, no unsafe entries. All72source hashes
are stable and every stated integrity/registration/safety/whitespace gate
passes. No failure or timeout occurred in this fresh integrated run.

## Note verification

```sh
bash docs/direct-r-handoff/verification/combinatory-indexed-provenance-2026-10-23/NOTE-CHECK.sh
```

Build and inspection PASS, exit0,20:48:12–29UTC. Logs
`_build/combinatory-indexed-provenance-note.OWcpHq`, render directory
`/tmp/pts-rk-indexed-provenance-note.dVJuNB`, archive `note.5KCYYS`.
32pages, appendix3,67Rocq/27Agda badges,44Agda links,135total links.
Every page renders and changed pages1/25/26 were visually reviewed.
All proof-link targets and new scope-boundary content checks pass.
No overfull box, undefined reference or highlighting fallback.

No full repository CI, new Agda/MM0 checker execution, commit, push, staging,
cleanup or unrelated process operation is claimed. Previous proof/kernel
and unrelated self-consistency development sources are preserved.
