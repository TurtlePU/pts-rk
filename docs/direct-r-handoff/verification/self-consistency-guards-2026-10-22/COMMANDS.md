# Fixed PTS carrier and guarded finite pilot — 22 October 2026

HEAD remains `6a8dc984fb59a9b3743503cd405ffe59a31d1978`. No staging,
commit, push or cleanup. Existing unrelated changes are preserved.

## Contracts

Three new modules (465 lines) extend `PTSrk.SelfConsistency`:

- `InternalCarrier`: original annotated PTS Church type for the literal
  29-tag/binary-pair serialized alphabet, at rank 2. Constructor generation
  uses exactly rank-1 motives; `Good x : U4`, and the pair-generation
  theorem type has rank 5. Executable quotation and generation construct
  original PTS inhabitants for every raw tree, including malformed and
  rejected inputs. Quotation is syntactically injective. Generation contains
  no decoding, acceptance, normalization or resource condition.
- `GuardedTables`: exact rank-1/rank-2 guards on rank-1 Boolean selectors;
  both guards have rank 3. Literal closed rank-4 PTS laws establish binary
  elimination, closure, and pointwise Leibniz equality on arbitrary guarded
  inputs. The table constructor takes four entries as ordinary data at one
  fixed type. Lookup/closure explicitly handle selector expansion; no eta
  conversion or all-inhabitant parametricity is assumed. All sixteen canonical
  binary tables are typed instances of the same constructor.
- `FiniteRejection`: independently classifies all closed native height-zero
  certificates with recorded labels <= 1. They are exactly SortRule 0 and
  SortRule 1; both pass ordinary acceptance, neither concludes Bottom by
  local syntax checking. A PTS table is generated from the independent raw
  contradiction checker. Canonical computation/fragment coverage and an
  internal rejection term on ALL Can_2 selector inputs are proved. Its exact
  motive rank is 2 and complete quantified type rank is 4. No external
  normalization or Bottom-emptiness theorem supplies the branch evidence.

Reuse only the unchanged shared named assembler, native successful-run
checker/evaluator, kernel wrappers and structural lemmas in Interpretation_of_R.
The endpoints are original `Syntax.Term nat`, `Typing.typ`, `Ranks.RankSorts`,
not checker judgments. Neither arithmetic interpretation nor a set model is
imported. The original kernel and seven preceding consistency proof files
match the previous audit hashes; shared infrastructure has no Git diff.

This is a representation/finite-case milestone, not internal consistency.
Generation is not resource admission. The finite pilot has the explicitly
stated tiny bound; it does not internalize the general decoder/checker.
Variable-size resource graphs, guarded operation/closure/joining laws,
internal compression, standard admission, cost/transport/history bounds
and one all-budget soundness term remain open. Later motives need exact
rank checks; Good_1 is not a cumulative induction principle.

## Fresh audit

```
bash docs/direct-r-handoff/verification/self-consistency-guards-2026-10-22/AUDIT.sh
```

All stages exit 0, 17:09:43–17:11:55 UTC:

- Logs: `_build/self-consistency-guards-audit.fLkaOG`.
- Fresh absolute Dune build: `/tmp/pts-rk-guards-fresh.wn4TgK`.
- Independent pristine: `/tmp/pts-rk-guards-pristine.fhrnxL`, baseline
  `723cf2ec61c737ae82ba33d2e7db44f650122b0e`.
- Pristine build 17:09:43–46; pristine recursive kernel check 17:09:46–53.
- Fresh dependency closure 17:09:53–17:10:42; separately compiled public
  audit 17:10:42–46: **127 endpoints, 127 closed reports** (85 prior, 42 new).
- Recursive kernel check 17:10:46–17:11:55. Full context inventory exactly
  equals pristine: only unchanged upstream `functional_extensionality_dep`,
  no type-in-type, unsafe (co)fixpoints or assumed positivity.
- Original-source comparison, safety scan and before/after source manifests
  pass. The manifest includes shared infrastructure. Prior-source hash
  comparison and shared-directory `git diff --exit-code` also pass.

Versions: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2,
Dune 3.23.1. Raw commands, versions, start/end times, exits, stdout/stderr
and both complete inventories remain in the log directory. No full-repository
CI run is claimed; the existing staged consistency alias includes the new files.

## Incremental attempts

Pinned environment as in AUDIT.sh. Logs in
`_build/self-consistency-guards-progress/attempt-NN.log`:

```
opam exec -- dune build -j 2 theories/self_consistency/InternalCarrier.vo
# 01: exit 1, residual substitution/shift; 02: exit 0
opam exec -- dune build -j 2 theories/self_consistency/GuardedTables.vo
# 03/04: exit 1, missing bool/named binder annotations; 05: exit 0
opam exec -- dune build -j 2 theories/self_consistency/InternalCarrier.vo theories/self_consistency/GuardedTables.vo
# 06: deliberately terminated, driver exit 1; 07: exit 0
opam exec -- dune build -j 2 theories/self_consistency/FiniteRejection.vo
# 08/09/10: exit 1, Equations pattern names/syntax; 11: exit 0
opam exec -- dune build -j 2 @theories/self_consistency/audit
# 12: exit 0
```

Attempt 06's exhaustive 29-by-29 atom-injectivity proof consumed about
2.4 GiB RSS; its exact compiler process was terminated. Replaced it by a
linear atom-index observation and a finite tag round trip. No theorem
statement or checking discipline was weakened. All compiler errors above
were fixed before the fresh audit. Working builds report old logical-loadpath
remapping warnings; the fresh build supplies independent paths.

## Note and final checks

```
bash theories/self_consistency/build-note.sh DIRECT_ROADMAP
swift docs/direct-r-handoff/verification/self-consistency-direct-roadmap-2026-10-22/inspect.swift theories/self_consistency/DIRECT_ROADMAP.pdf _build/self-consistency-guards-progress/pdf
```

Both note builds and both PDF inspections exit 0. First build:
`/tmp/pts-rk-consistency-note.QG60VD`; final build after prose cleanup:
`/tmp/pts-rk-consistency-note.AZ6Pl2`. Ten nonempty pages, four links,
required text/math/primary citation and all-page rendering pass. Changed
pages 5–7 were visually reviewed. No LaTeX, overflow, underflow or missing
glyph diagnostics. Raw build/inspection logs and renderings are retained
in the progress directory. Scoped whitespace and shell syntax pass.

```
6180327b4a2a1373af953dd6049b1aa5f731b5c975b4df94e4bb46cb87ba3d0f  InternalCarrier.v
8612be2ba45d572d3584e28d547845ae8a8de5c2d7c47aea99a64a50acca1d46  GuardedTables.v
9eca7335710399d68255cc1b9659a01295c269a7ea1aca3c8543d7d060a7370f  FiniteRejection.v
a9bdb798b55cfea50b9cecb6714be0f6e70354381d505824f337cc84d51910cb  Audit.v
34e8c6fec214feb2ee336bce7b138b5fad8ebb8b8b77e813f27ca6be8b79b693  dune
35f944209ae26d00e80405cb499bd80efb9006c0fbea0d8bd79bbd5b88611c5c  DIRECT_ROADMAP.tex
39698bbbf80d7cede3277f14667e0476da6281dbc03319f55a8aed6a905dc9d2  DIRECT_ROADMAP.pdf
```
