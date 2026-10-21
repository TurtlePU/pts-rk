# Rank bounds for capped PHOAS environments

21 October 2026. Parent: `1d1f2462b1d5dff9f94f8f1f3247f40d34769a90`.
The preceding improvement commit was pushed to `origin/main`; `git ls-remote
origin refs/heads/main` confirmed this hash. The new request concerns fragment
uniformity. No CPS formalization is included.

## Scope and boundary

- `FragmentUniformity`: actual alignment-request formation bound `k+2`,
  executable cap filtering with exact accepted-membership characterization,
  original typed/normal fillings, preservation of declaration bounds through
  arbitrarily many layers, actual base-signature bound `k+3`.
- `CappedInterpreter`: actual lookup and filling agreement, inherited Tarski
  realization, normal originally typed interpreters whose type-sort indices
  are bounded by `max(k+7,r+6)` for every numerical plan and `s<=k+1`.
- `FiniteCoherenceCatalogue`: every finite list of concrete fields misses an
  accepted normal rank-2 equality with literal ceiling zero; size is `2*h+11`.
  Bounding `conservativeRank` instead gives a finite syntax vocabulary.
- Aggregate audit, Dune registration, development README/ledger, research
  note/PDF and scoped continuity entries.

Full-source quotation into the capped family and a single interpreter term
per whole fragment remain open. The bound k is the formation/literal quotation
budget, not an asserted function of the normalization redex bound d; that
source-side bridge is also open. The local profile bound is an explicit input
of the request-bound theorem. No theorem silently supplies the recursive
quotation invariant or promotes a lower sort index by cumulativity. The
finite-catalogue result does not exclude generic laws or encoded environments.
The complete existing quoter and its syntax-injectivity theorems are unchanged.

## Commands and retained attempts

Raw output: `_build/self-interpreter-fragment-uniformity-2026-10-21`.
All incremental commands used:

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
opam exec -- dune build --display=short --no-buffer theories/self_interpreter/FragmentUniformity.vo
opam exec -- dune build --display=short --no-buffer theories/self_interpreter/FiniteCoherenceCatalogue.vo
opam exec -- dune build --display=short --no-buffer theories/self_interpreter/CappedInterpreter.vo
```

`attempt-01` through `attempt-04` exit 1 while developing the local rank
bound and block induction (beta simplification before `lia`, explicit
induction names). `attempt-05` exits 0. Extending it, `attempt-06` exits 1
because original `wf` is Type-valued and an existential in Prop cannot be
eliminated to construct it. The corrected theorem proves `inhabited (wf G)`
in Prop; later rank proofs use it only in Prop. `attempt-07` exits 0.

`catalogue-01` exits 1 for an unconstrained implicit sort signature in a
constructor proof; it was made explicitly `RankSorts`. `catalogue-02` exits
1 for a rewrite after excessive reduction; a precise `change` fixes it.
`catalogue-03` exits 0. `capped-01` exits 1 for a dependent rewrite match;
using the exact existing filling theorem fixes it. `capped-02` exits 0.
No unfinished proof or added axiom is retained.

The completed prior Dune cache `/tmp/pts-rk-self-improvements-audit.vjkEgS`
occupied 626 MiB with only 387 MiB free. Its successful build/kernel exit
records were checked; its trace was saved as `previous-audit-trace.csexp`.
`opam exec -- dune clean --build-dir=/tmp/pts-rk-self-improvements-audit.vjkEgS`
exits 0, recovering about 626 MiB. This removes only regenerable build files;
the prior raw verification logs remain.

## Fresh verification

The accompanying `AUDIT.sh` records commands, timestamps, versions, exit
codes and source manifests. This run uses the fresh absolute Dune directory
`/tmp/pts-rk-fragment-audit.umlOaP`.

```sh
bash docs/direct-r-handoff/verification/self-interpreter-fragment-uniformity-2026-10-21/AUDIT.sh
DIRECT_R_LOG_DIR=/Users/akuklev/air/pts-rk/_build/self-interpreter-fragment-uniformity-2026-10-21/ci bash tools/check-local-ci.sh
bash tools/build-self-interpreter-note.sh
```

Complete local CI/actionlint exits 0: 226/226 stages PASS, result `complete`,
including a pristine upstream build and the full interpreter audit. The shared
CI also contains unrelated unpublished BZC stages; no publication of them or
hosted CI run is claimed. The fresh aggregate build exits 0 with 2348 closed
reports: 2347 self-interpreter reports (matching the source inventory), plus
one unchanged upstream normalization report. Fresh compilation ran
09:17:49--09:26:10 UTC. Core and complete interpreter recursive kernel checks
exit 0; the latter ran 09:26:16--09:36:10 UTC. The loaded inventory contains
only unchanged upstream functional extensionality, no type-in-type, unsafe
fixpoints or assumed positivity. All own endpoint assumptions are closed.
Pristine core inventories are byte-identical; the original core,
normalization and frozen ZFC proof/Dune comparisons pass. All 115 source/Dune
manifest entries remain stable. Incremental compilation also exits 0.
The first note build (`note-01`) exits 0 in
`/tmp/pts-rk-self-note.QHtYpx`: 12 pages, no layout/reference/glyph warnings.
The second note build (`note-02`) exits 0 in
`/tmp/pts-rk-self-note.u6BhBv`: 12 pages, no overfull/underfull boxes, LaTeX
warnings or missing glyphs. PDFKit text extraction and rendering exit 0;
pages 1, 11 and 12 were visually inspected. `pdf-inspect.log` and the generated
page PNGs are retained in the raw output directory.
The final budget-qualification edit builds successfully (`note-03`) in
`/tmp/pts-rk-self-note.k3lPRz`, still 12 pages and warning-free. Final PDFKit
text/render inspection (`pdf-inspect-final`) exits 0; page 12 is checked again.
`FINAL-CHECKS.sh` exits 0, verifying all recorded outcomes, report counts,
stable manifests, source comparisons, full CI and unchanged publication state.

Pinned versions: OCaml 4.14.2, Dune 3.23.1, Rocq 9.2.0, Stdlib 9.1.0,
Equations 1.3.2+9.2. Full installed versions are in `versions.log`.

Final SHA256 values:

```text
28d38ec58211dbc4c94a2362615e95f30b5b6cc5c792f41d1a981dea6bbcb44b  PTS-rk_self_interpreter.tex
7560532d6b1bfb4c2af7caa04a88f5f6a1dfb44f1b798afc345afea674acd87c  PTS-rk_self_interpreter.pdf
542dfa2ea9e6beafc407903ee1dbd98765f4c73bca92f6d3052354f8ab51b32e  FragmentUniformity.v
3b90447743b9ad6651d50acd9dc6c2bdd068197afd9ed3b512a3d0cc912a8a2e  FiniteCoherenceCatalogue.v
7d70660668979839f68ca43ddd29f34ae88453a6b6a5d902b0a6e10f845ae66e  CappedInterpreter.v
```

Existing unrelated worktree edits and untracked material remain untouched.
No commit or push of this new continuation is requested.
