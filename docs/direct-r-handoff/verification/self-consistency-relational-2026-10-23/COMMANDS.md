# Consumer-directed preservation and the obligation review

23 October 2026 local time; initial raw timestamps are 22 October UTC.

## Exact contracts and review outcome

Four new modules (488 lines), original PTS typing throughout. All 23 earlier
proof modules, original kernel, carrier/guards/lookup relations and shared
assembler/checker are unchanged. No axioms, admitted goals or unsafe checks.

- `RelationalTransport`: original terms for rank-4 predicate descent through
  Look_5 and Hist, with explicit generated-sibling descent laws; dual negative
  safety for upward-closed predicates. Look_5 uses the exact rank-5 implication
  motive. Quantified types have ranks 7, 8 or 11. These are modular theorems,
  not the source typing/normalization invariant.
- `OccurrenceSafety`: Absent(seed,a) = Ext(seed,a) -> Bottom, a rank-7
  predicate, propagates through extension, lookup and history. It factors
  through transitivity instead of eliminating Look_5 at rank 7. Actual
  nonzero-leaf and pair absence from stop is proved using the existing Stop
  observation and inhabited rank-3 padding. This is represented Ext-absence,
  not a native absence iff theorem or source Bottom rejection.
- `LookupHomomorphisms`: actual shape and generated filling preserve Look_5,
  Look_6 and Hist, opening target folds before source elimination. Root/value
  change, path stays fixed. Quantified type ranks are 8, 9 and 11. This is
  not source capture-avoiding substitution or preservation of source typing.
- `SimulationRealization`: exact native shape/lookup commutation, one-way
  filling preservation, explicit native non-reflection counterexample,
  original-PTS application lemmas and standard realization. Final witnesses
  APPLY the internal maps to previous typed lookup witnesses and convert
  endpoints to canonical quotations by existing beta laws.

Dependency review finds no implemented consumer of full arbitrary-path
functionality or matching-constructor inversion. Keep them as optional open
lemmas, not mandatory soundness gates. Generic consumer preservation and
concrete forward simulations bypass their use only for the stated consumers.
Every related output must preserve the actual eventual invariant. Reusing one
result is legitimate; identifying independently obtained results needs its
own consumer-specific coherence proof. Do not infer label-sensitive safety
from tag-erasing capacity. No impossible-definability result is claimed.
The focused reference search is retained in
`_build/self-consistency-relational-progress/consumer-review.log`; the new
proof modules do not import LookupInversion or InversionRealization.

The negative comparison needs forward realization of accepted standard
general judgments, not reverse checker agreement. The latter is retained
for exact predicate identification. An independent overapproximation is
safe only if all-budget soundness covers EVERY acceptance witness; external
Bottom emptiness cannot supply vacuous realization. Comparing two internal
consistency sentences needs uniform internal acceptance/domain translation,
not just the pointwise standard map. No checker definition is changed here.

Fixed-rank histories already avoid same-rank composition. Structural closure
may replace internal numerical capacity comparison; preserving an independent
invariant may avoid reifying complete typing certificates. Neither option
establishes operation sufficiency automatically. Actual source substitution,
conversion, terminal separation, all-budget soundness, standard admission
and consistency remain open. First proposed concrete operation: independent
annotated replacement/scoped-environment graphs with internal scope
preservation, then the dependent semantic/typing contract. Preserve binary
indices and original binder lifting.

## Fresh verification

```sh
bash docs/direct-r-handoff/verification/self-consistency-relational-2026-10-23/AUDIT.sh
```

- Raw logs: `_build/self-consistency-relational-audit.ILJDGV`.
- Fresh absolute Dune build: `/tmp/pts-rk-relational-fresh.ZbkLf6`.
- Pristine build: `/tmp/pts-rk-relational-pristine.yosufK`.
- Pristine revision: `723cf2ec61c737ae82ba33d2e7db44f650122b0e`.
- Start 23:29:14 UTC. Pristine build/kernel pass at 23:29:18/23:29:24.
- Fresh dependencies pass at 23:33:26, exit 0 (242 seconds).
- Separate endpoint audit passes at 23:33:33: **283/283 closed** (242 prior
  plus 10 transport, 12 homomorphism, 12 occurrence and 7 realization).
- Recursive kernel checking passes, exit 0, 23:33:33 UTC (22 October) to
  00:03:42 UTC (23 October): **1809 seconds**, within the up-front limit.
- Complete dependency inventory exactly equals freshly rebuilt pristine:
  only unchanged `Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep`;
  no type-in-type, unsafe (co)fixpoints or assumed positivity.
- Inventory comparison, original-source comparison, before/after manifests
  and source stability all pass at 00:03:42. **Every audit stage exits 0;
  no timeout**. Total run: 23:29:14–00:03:42 UTC.

Pinned versions: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml
4.14.2, Dune 3.23.1. Exact expanded commands and full versions are in the
raw logs. The focused script allocates 900 seconds to the enlarged fresh
build and 2400 seconds to recursive checking BEFORE its first run (previous
closure took 971 seconds). No proof check is omitted, no repository CI
setting is changed. This focused audit is not full repository CI.

Prior-source hash comparison passes for original/common infrastructure and
all 23 earlier proof modules:

```sh
shasum -a 256 -c <(rg -v 'self_consistency/(Audit.v|dune)$' _build/self-consistency-relational-progress/sources-before.log)
```

Output: `_build/self-consistency-relational-progress/prior-unchanged.log`.

## Incremental compilation and failures

Pinned environment:

```sh
export PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH"
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
```

Root progress logs: `_build/self-consistency-relational-progress`.

- `opam exec -- dune build -j 2 theories/self_consistency/RelationalTransport.vo`:
  `attempt-01.log`, exit 0.
- Same command for `OccurrenceSafety.vo`: `attempt-02.log`, exit 1. Invalid
  Ltac `[contradiction |all: ...]` syntax in the final leaf-case proof.
  Replaced by `destruct t; intro H; try contradiction; ...`; no theorem or
  check was weakened. Earlier theorems in that file already compiled.
- `opam exec -- dune build -j 2 theories/self_consistency/OccurrenceSafety.vo theories/self_consistency/LookupHomomorphisms.vo`:
  `attempt-03.log`, exit 0.
- Independent first-attempt compilation of LookupHomomorphisms and
  SimulationRealization passes, exit 0, in
  `/tmp/pts-rk-lookup-homomorphisms.Oe1hKt`, logs `attempt-01.log` and
  `simulation-attempt-01.log`. Exact command, with the final filename varied:

```sh
opam exec -- rocq compile \
  -Q /Users/akuklev/air/pts-rk/_build/default/theories PTSrk \
  -Q /Users/akuklev/air/pts-rk/_build/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q /Users/akuklev/air/pts-rk/_build/default/theories/self_consistency PTSrk.SelfConsistency \
  -Q /tmp/pts-rk-lookup-homomorphisms.Oe1hKt PTSrk.SelfConsistency \
  /tmp/pts-rk-lookup-homomorphisms.Oe1hKt/SimulationRealization.v
```

The fresh Dune audit subsequently rebuilds all final source versions.
Only existing logical-loadpath remapping warnings occur in successful builds.

## Note/PDF

```sh
bash theories/self_consistency/build-note.sh DIRECT_ROADMAP
mkdir -p _build/self-consistency-relational-progress/pdf
swift docs/direct-r-handoff/verification/self-consistency-direct-roadmap-2026-10-22/inspect.swift \
  theories/self_consistency/DIRECT_ROADMAP.pdf _build/self-consistency-relational-progress/pdf
```

Build 01 passes in `/tmp/pts-rk-consistency-note.6LAiII`; 14 nonempty pages,
four links, required text/math and all-page rendering pass. Two underfull
work-package lines are resolved by shortening the repetitive module list.
Build 02 passes in `/tmp/pts-rk-consistency-note.LYRZcJ`, clean diagnostics,
same full inspector passes; changed pages 10, 11 and 14 visually reviewed.
Build 03 passes in `/tmp/pts-rk-consistency-note.Dh6AOH` after adding the
concrete next-step contract; full inspector passes (15 pages), but the last
page has only two lines. Shortening the repetitive conclusion fixes this:
build 04 in `/tmp/pts-rk-consistency-note.ZzOgUv` passes, 14 pages, all checks
pass and pages 12/14 reviewed. Build 05 adds the one-way adequacy distinction
and passes in `/tmp/pts-rk-consistency-note.mqU7eX`: 14 nonempty pages, four
links, required text/math and all-page rendering pass. Pages 4/14 reviewed;
final diagnostics are clean. All build/inspection logs remain in the progress
directory. No proof source changed during the fresh audit.

## Git and scope

HEAD `6a8dc984fb59a9b3743503cd405ffe59a31d1978`, branch main; preserve all
pre-existing dirty work. No staging, commit, push, cleanup or edits to
kernel/common, arithmetic, set-model, combinatory or self-interpreter proofs.
Only the four new proof modules, audit registration and related exposition/
handoff are changed in this continuation.
The index is empty. Final scoped whitespace, audit shell syntax and
prior-source hash checks pass; source/PDF hashes below are unchanged.

## SHA-256

```text
2735363cb803a50ed3e367c025b42cf74416fa0fd0d41f5b123ce85a2835afc8  RelationalTransport.v
a1513186d799636cfa20a94dd863d631fa88338b3dfbfb3c37cc5f7a452a2f2a  LookupHomomorphisms.v
7ae4e938e278bce620ba555aeb5658562efc4ae2de8810f5cc112dca4355ccb0  OccurrenceSafety.v
9dd34c9a9a73c79ec214ab020cc17b7c7264166b394ffb4d75bcc23d5fc31049  SimulationRealization.v
5a2aa7793e9d48a7c0b7ce3ca25cea8d5265a6c67a3767785533edebcabc286a  Audit.v
78104b9b7d2b5ee4952996f875636796c0421b985aa0a108e5591ced94e1c325  dune
c0fa635fb9d823821cd42e8db478b6cbc7075fdcabbc414462ff0c64520af733  DIRECT_ROADMAP.tex
f1d9a2228ab56a7971e97c2a19e21412b4f850407f7c0349c6f1aa2720f6fa39  DIRECT_ROADMAP.pdf
```
