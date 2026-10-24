# Quantified finite models and native realization — 23 October 2026

## Verified scope

Eleven new Rocq modules add 140 closed public reports to the previous 358:

- FiniteAlgebraSearch (16) and FiniteOperationAlgebras (14): complete
  enumeration/search of all total constructor interpretations.
- MM0FiniteSignature (18), MM0FiniteAxioms (8), MM0FiniteSearch (9):
  actual sorted signature/all 55 universal axioms, semantic correspondence
  and exact fixed-domain model decision, including universal Void denial.
- MM0ProjectionModel (11): explicit all-valuations two-element model of
  the subtheory omitting sveq and f0; both omitted axioms explicitly fail.
- FiniteModelRealization (20), FiniteModelSoundness (14),
  MM0SyntaxSoundness (10), MM0InternalSoundness (12): actual native PTS
  finite satisfaction certificates and computational deduction translation.
- FiniteNativeModelBoundary (8): no finite single ungraded carrier with full
  native typing/beta soundness, compositional total application, semantic
  conversion/type reduction and empty Void; finite-selector test lower bounds.

The constructor search is complete at specified equal sort cardinalities,
not an unconditional existence theorem. The projection interpretation has
empty form/ax and identity substitution: it is not nearly the full PTS model.
Its successful search is established analytically, not by executing 2^28
tables. The full 55-axiom singleton checker was actually evaluated to false.
The native obstruction does not settle the literal full55 MM0 theory without
the separate native/catalogue adequacy bridge. Finite certificates are an
externally indexed family of internal proofs, not uniform internal reflection
over arbitrary Church-coded proofs or budgets. Original PTS rules are unchanged.

## Fresh integrated audit — PASS

Exact root command:

```sh
bash docs/direct-r-handoff/verification/combinatory-quantified-models-2026-10-23/AUDIT.sh > docs/direct-r-handoff/verification/combinatory-quantified-models-2026-10-23/audit-driver-01.log 2>&1
```

All **22 stages pass**, **07:43:26–07:45:14 UTC**, exit 0. This is an actual
successful one-shot fresh audit, not a cache hit or a collection of unrelated
isolated successes. Expanded commands and exact stage exits/times are retained
in [audit-final/commands.txt](audit-final/commands.txt) and
[audit-final/status.tsv](audit-final/status.tsv).

- Live logs: `_build/combinatory-quantified-models-audit.fUUdPV`.
- Fresh absolute Dune directory: `/tmp/pts-rk-quantified-models.uhpkYv`.
- Fresh pristine tree: `/tmp/pts-rk-quantified-pristine.9rwXrE`.
- Pristine revision: 723cf2ec61c737ae82ba33d2e7db44f650122b0e.
- Working HEAD: 6a8dc984fb59a9b3743503cd405ffe59a31d1978.

The fresh build passes **07:43:35–07:44:52 UTC**, exit 0: all **43 modules**,
**498 own closed reports**, 140 new; one imported Ranks report gives 499
aggregate. Complete recursive `rocq check -silent -o` passes
**07:44:52–07:45:14 UTC**, exit 0, on every root and dependency, with no
admission/skip flags. The ENTIRE context inventory equals fresh pristine:
only inherited `Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep`,
no type-in-type, unsafe fixpoints or assumed positivity. Raw load-path
diagnostics are preserved; inventory comparison starts at the unique
CONTEXT SUMMARY and includes everything thereafter.

Pinned versions: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2, Dune 3.23.1. The script uses the pinned opam executable and
OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam, OPAMSWITCH=pts-rk-ci.
The exact installed package inventory and compiler versions are archived.

All 12 original kernel files match pristine. All 32 previous combinatory
proof sources and the shared DirectREval source match their prior manifest;
only Dune registration changes. All 52 Agda sources match their previous
safe-check manifest. The MM0 source is unchanged. All 43 current proof sources,
Dune registration, shared equality source and MM0 source have identical
before/after hashes. Safety and scoped whitespace checks pass. Existing
load-path/shadow warnings and the upstream Vector.t advisory remain visible;
no warning-free claim is made. No new Agda/MM0 checker/full-repository CI run
is claimed. No staging, commit, push or cleanup occurred in this turn.

## Literal-source correspondence

```sh
python3 docs/direct-r-handoff/verification/combinatory-quantified-models-2026-10-23/crosscheck-mm0.py
```

Exit 0, both separately and as a fresh audit stage: all 55 expanded axiom
trees match, including binder sorts/order, premises and conclusions.
This independently written textual checker is UNTRUSTED test evidence.
The Rocq sorting, substitution, evaluation and source-proof correspondence
theorems concern the explicit trees, not a kernel-verified MM0 parser.

## Isolated development, failures and independent reviews

No failed isolated attempt is relabelled a success. Exact commands, versions,
logs and final hashes are retained in the following worker ledgers:

- [algebra-search/COMMANDS.md](algebra-search/COMMANDS.md).
- [operation-algebras/COMMANDS.md](operation-algebras/COMMANDS.md).
- [mm0-models/COMMANDS.md](mm0-models/COMMANDS.md).
- [internal/COMMANDS.md](internal/COMMANDS.md).
- [NATIVE-SCHEMA-COMMANDS.md](NATIVE-SCHEMA-COMMANDS.md), with raw logs under
  `schema-boundary/`.

In particular, model-search development retains five deliberate terminations
(143): two expensive higher-order inference attempts, direct dependent-key
singleton search normalization, and two projection-model conversion attempts.
These are not passes. InternalSoundness
attempt 01 failed on an underdetermined placeholder. Attempt 02 was explicitly
interrupted (exit 1, User interrupt) when `apply` started expanding the concrete
saturation table. Final attempt 03 uses fully explicit theorem applications:
12 reports, exit 0, with no execution of the large projection saturation or
constructor search. Generic source-compiler unification takes about 21 seconds;
the concrete certificate/rank applications check immediately. The integrated
fresh run above verifies the final combined sources independently of all
temporary object mappings. No object/cache file was copied into the repository.

Independent review confirms complete semantic operation rows, the substantive
projection omissions, the exact scope of the native obstruction and the
negative/continuation nature of the finite certificate. The forward proof
generator does not use canonicity; converse inhabitability uses the external
native Void theorem openly.

## Note and PDF — PASS

```sh
bash theories/CombinatoryLogic-rk/build-note.sh > docs/direct-r-handoff/verification/combinatory-quantified-models-2026-10-23/note-driver-01.log 2>&1
mkdir -p /tmp/pts-rk-combinatory-note.zcT1xM/inspection
swift docs/direct-r-handoff/verification/combinatory-quantified-models-2026-10-23/inspect.swift theories/CombinatoryLogic-rk/CombinatoryPTS-rk.pdf /tmp/pts-rk-combinatory-note.zcT1xM/inspection > docs/direct-r-handoff/verification/combinatory-quantified-models-2026-10-23/note-inspect-01.log 2>&1
```

Fresh note build `/tmp/pts-rk-combinatory-note.zcT1xM`,
**07:41:38–07:41:53 UTC**, compiler/build/validation exit 0. Inspector exit 0:
**28 pages**, complete three-page MM0 appendix, **41 Rocq / 27 Agda badges**,
44 Agda links, 109 total links. All pages render; pages **1, 18, 20, 21, 22**
were visually reviewed. The obstruction theorem, constructor-count exponent,
finite-certificate formula and scope qualifications render correctly, without
clipping or raw TeX. Earlier inspector requirements were retained except
superseded candidate-only limitations; new requirements enforce all new proof
links and the model/certificate boundaries. Final hashes are in
[note-final.sha256](note-final.sha256); build logs/versions/statuses are in
`note-build-01/`, selected renders/text/links in `note-final/`.

## Next mathematical choice

The unrestricted native interface on one fixed finite carrier is impossible,
not merely unfinished. A meaningful continuation must specify a genuinely
size-/proof-depth-guarded fragment and prove that its finite guards cover the
intended bounded original derivations; guard insertion changes the axioms and
must not be silently identified with the full quantified theory. Growing
graded carriers are another distinct target. Alternatively prove the missing
native/MM0 adequacy bridge and transfer the obstruction to that literal theory.
No such target change is made by this checkpoint.

After any proof change, rerun the exact fresh audit above; its build and full
recursive-check allowances are each 900 seconds. Do not remove semantic
valuations, weaken Void denial, or retain model acceptance as a target premise.
