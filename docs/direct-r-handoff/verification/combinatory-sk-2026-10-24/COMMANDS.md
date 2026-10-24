# SK surface and beta-faithful reference — 24 October 2026

## Scope and source state

User requested the canonical-beta direction with an SK-only surface.
HEAD remained `6a8dc984fb59a9b3743503cd405ffe59a31d1978`; existing staged,
unstaged and untracked work was preserved. No staging, commit or push.
Pre-edit development snapshot: `/tmp/pts-rk-sk-transition.Wx7vD6/baseline`.

Replaced the two obsolete Rocq basis files by SK.v, removed the redundant
Agda basis signature and its import, migrated all six BinderFree modules to
S/K, and removed primitive identity from Combinatory.agda/Examples.agda.
Identity is a derived SK expression. The complete native Hilbert catalogue
is separate and unchanged, including its identity-shaped logical schemes.
Historical proof logs are retained rather than rewritten as SK evidence.

SK.v has 473 lines and 23 public closed assumption reports. It proves native
typing, forward annotated beta compilation, preservation/reflection of
conversion of source expansions, and literal equality of normal source
expansions. It also checks the 10n+4 numeral family, ranks, unapplied native
normal form and successor/addition/multiplication arithmetic.

The six direct Agda modules total 1,021 lines (281/258/108/112/77/185),
versus 1,168 before. Their weak normalizer/checker/quotient proofs remain
checked. Boundary now gives native typing for EVERY intrinsic SK expansion.
The new 121-line SKNativeCanonical module computes originally typed native
normal forms, decides original beta of expansions, proves native-output
idempotence, and defines the actual native-beta quotient with injective
normalization, decidable equality and well-defined application.

## Fresh Rocq audit

```sh
bash docs/direct-r-handoff/verification/combinatory-sk-2026-10-24/AUDIT.sh
```

Exit 0, 2026-10-24 00:36:32–00:39:56 UTC. Raw commands, stage exits, times,
versions and source manifests: `audit.MhPQbr/`.
Archived text logs have trailing whitespace normalized; paired `.raw.gz`
files preserve their exact original bytes, including the inventory reports.

- Build: `/tmp/pts-rk-sk-audit.puvKDx`, fresh absolute Dune directory.
- Pristine: `/tmp/pts-rk-sk-pristine.vT6zKA`, source commit
  `723cf2ec61c737ae82ba33d2e7db44f650122b0e`.
- Rocq 9.2.0, Dune 3.23.1, OCaml 4.14.2, Stdlib 9.1,
  Equations 1.3.2+9.2 in the pinned pts-rk-ci opam switch.
- Fresh compilation: 00:36:43–00:39:24, all 73 active combinatory modules,
  1,215 own closed reports / 1,216 including Ranks. The count decreases
  because 38 reports in the two replaced files are replaced by 23 in SK.v.
- Recursive kernel check: 00:39:24–00:39:56, exit 0, VM enabled.
- Full context inventory equals fresh pristine byte-for-byte: inherited
  functional_extensionality_dep only; no additional or unsafe assumptions.
- All 72 retained prior Rocq bodies, native kernel and literal MM0 source
  are unchanged. Source stability, safety and whitespace gates pass.

This is the full active combinatory-library audit, not full repository CI.
No unchanged MM0 checker rerun is claimed.

## Fresh complete Agda closure

```sh
AGDA_BIN=/tmp/pts-rk-agda-2.8.0.MvVO53/agda \
CUBICAL_DIR=/tmp/pts-rk-agda-2.8.0.MvVO53/cubical \
bash theories/CombinatoryLogic-rk/check-agda.sh
```

Exit 0, **zero warnings**, 00:36:05–00:36:53 UTC. Fresh copied source,
isolated config/data, `--safe --ignore-interfaces`; Cubical mode comes from
the source pragmas. All 58 project modules are checked. Agda
2.8.0-3d04bac; Cubical v0.9 revision
`b150186d2544e7efeddd31e5d14a8b9ecbb100f7`.
Build `/tmp/pts-rk-combinatory-agda.snmnV0`; full logs/manifests in `agda/`.
All 48 unaffected preceding Agda sources equal the pre-edit snapshot;
`agda/prior-source-stability.log` records each comparison.

Worker histories are under `workers/`: qiirt, binderfree, compiler,
native-reference and native-quotient. Their COMMANDS files retain actual
limitations. In particular the Rocq worker's shell returned the status of
`tail`, so its intermediate compiler numeric exits and timestamps were not
captured. Its raw error/success logs are retained without inventing those
statuses. The fresh root audit supplies authoritative compiler exits and
assumption comparison. No intermediate source snapshots are claimed where
workers did not retain them.
A final supplemental safety-scan command initially had an unescaped brace
in its ripgrep regular expression (exit 2); the corrected scan passed with
no matches. This was a diagnostic-command error, not a compiler failure;
the independent audit safety gate also passed.

## Note and PDF

```sh
bash theories/CombinatoryLogic-rk/build-note.sh
swift docs/direct-r-handoff/verification/combinatory-sk-2026-10-24/inspect.swift \
  theories/CombinatoryLogic-rk/CombinatoryPTS-rk.pdf /tmp/pts-rk-sk-pdf.3wB4UI
```

Both exit 0. Final build `/tmp/pts-rk-combinatory-note.cJu4ye`,
00:38:11–00:38:26 UTC; logs under `note/`. Initial successful build
`/tmp/pts-rk-combinatory-note.NQuWKV`, 00:37:15–00:37:31, was followed
by enclosing the new code excerpt in a minipage to avoid splitting a
declaration across pages. No proof source changed during this formatting.

Final PDF: 36 pages, 3-page complete MM0 appendix, 72 Rocq / 34 Agda badges,
150 links. All linked proof files exist; all pages render. Changed pages
2/10/11 were visually reviewed. Pygments output is present; no overfull
boxes, missing glyphs or unresolved references. No superseded basis name
remains in the paper or active implementation sources. Rendered images and
compiler caches are not archived as repository sources.

## Exact remaining boundary

The checked beta-faithful reference still returns native annotated terms.
The Rocq compiler accepts intrinsic simple-type lambda syntax; it is NOT
a parser/reifier from the native normalizer's output. Therefore the full
canonical SK function C(NF(E(c))), its literal code idempotence, a direct
canonical SK apply operation, dependent catalogue coverage and QIIRT path
adequacy remain open. No original conversion rule, typing rule or native
annotation was changed. No stronger PTS size bound, unrestricted dependent
type-checking completeness or strong normalization theorem is inferred.

Next exact action: construct native-normal-to-intrinsic source reification
for the supported simple-type fragment with deterministic hidden indices,
then compose it with the checked SK compiler. Preserve native beta only.
The same audit commands above are the next verification commands.
