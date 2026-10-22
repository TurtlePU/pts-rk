# Finite IIR Agda checkpoint — 22 October 2026

## Reproduce the final checks

From the repository root:

```sh
AGDA_BIN=/tmp/pts-rk-agda-2.8.0.MvVO53/agda \
CUBICAL_DIR=/tmp/pts-rk-agda-2.8.0.MvVO53/cubical \
bash theories/CombinatoryLogic-rk/check-agda.sh

bash theories/CombinatoryLogic-rk/build-note.sh

swift docs/direct-r-handoff/verification/combinatory-finite-agda-2026-10-22/inspect.swift \
  theories/CombinatoryLogic-rk/CombinatoryPTS-rk.pdf \
  /Users/akuklev/air/pts-rk/_build/combinatory-finite-pdf.6WaFbZ

shasum -a 256 -c docs/direct-r-handoff/verification/combinatory-bckw-2026-10-22/sources.sha256
bash -n theories/CombinatoryLogic-rk/check-agda.sh theories/CombinatoryLogic-rk/build-note.sh
git diff --check -- theories/CombinatoryLogic-rk \
  docs/direct-r-handoff/STATE.md docs/direct-r-handoff/DECISIONS.md \
  docs/direct-r-handoff/BUILD.md \
  docs/direct-r-handoff/verification/combinatory-finite-agda-2026-10-22
```

All final commands exit 0. The Swift output directory must exist; use a new
mktemp directory for a fresh inspection. The Agda and note scripts themselves
always allocate fresh build directories. No audit condition was weakened.

## Final evidence

- Agda: /tmp/pts-rk-combinatory-agda.7UFFIh, 08:12:27–08:13:03 UTC,
  23 project modules plus their full import closure, --safe and
  --ignore-interfaces, isolated configuration/data, copied sources and
  matching pre/post hashes. No warnings. The actual compiler command, full
  log, versions and source manifest are retained beside this file.
- Toolchain: Agda 2.8.0-3d04bac; Cubical v0.9
  b150186d2544e7efeddd31e5d14a8b9ecbb100f7, clean tracked/untracked sources.
- Note: /tmp/pts-rk-combinatory-note.5X2knp, 08:17:32–08:17:45 UTC,
  build and validation exit 0. Previous successful draft .Nltp4k:
  08:14:15–08:14:28 UTC. Exact LaTeX versions are in note-versions.log.
- PDF inspection: 18 pages, 3-page full MM0 appendix, 22 Rocq badges,
  17 Agda links (nine proof badges), 58 total links. Heading order, expected
  source excerpts, reference links and actual source targets checked.
  All pages rendered; final pages 8–13 visually inspected (10/12/13 rechecked
  after moving short listings into nonbreaking blocks).
- The prior fresh 23-module Rocq audit's complete source/Dune manifest
  matches. Native proofs and MM0 were not edited. No new native/full-CI or
  new assumption-audit claim is made here.
- No staging, commit or push. HEAD cb76553b03d536743e36c4e2c7e5a1c7c1669bef.
  Existing broad dirty worktree, including intent-to-add entries, preserved.

## Incremental attempts and repaired diagnostics

Each local Agda command below used the same compiler with:
```sh
/tmp/pts-rk-agda-2.8.0.MvVO53/agda --safe --no-default-libraries \
  -i /tmp/pts-rk-agda-2.8.0.MvVO53/cubical \
  -i theories/CombinatoryLogic-rk/agda \
  theories/CombinatoryLogic-rk/agda/MODULE.agda
```
Substitute the module named in each row. These reused-interface checks are
superseded by the fresh final import-closure check.

- FiniteBounds: see FiniteBounds-check.txt. Early failures (exit 42) involved
  guardedness propagation, arithmetic reflection and unresolved implicit
  endpoints. Local final and fresh standalone checks exited 0. Public alias
  additions are included in the final closure hash.
- FiniteSyntax, FiniteCarriers, NormalForms: see FiniteSyntax-check.txt.
  /tmp/pts-rk-finite-carriers.xNX3Nu/attempt-{01..06}.log exits
  42/42/42/42/0/0; fresh.log exits 0. Imports, qualified names, binder collision
  and redundant indexed parameter were corrected.
- BoundedReduction: /tmp/pts-rk-bounded-reduction.8uJJif/attempt-{01..09}.log
  exits 42/0/0/0/0/0/42/0/0. Attempts 02/03 had indexed matching warnings;
  caseFin/caseFin-rel eliminated them without suppressing any compiler check.
  Attempt 07's closed-scope inference error was fixed. Final log has no warnings.
- ExponentialBounds: /tmp/pts-rk-exponential-bounds.ZgcXN8/attempt-01.log,
  exit 0.
- RawSizeBounds: /tmp/pts-rk-raw-size.bFdr49/attempt-{01,02}.log, exits 42/0;
  explicit exponent endpoints repaired inference. See RawSizeBounds-check.txt.
- BoundedTrace: /tmp/pts-rk-bounded-trace.0Jt9SA/attempt-01.log, exit 0.
- NativeTyping: first check exit 42 (reserved constructor name variable),
  corrected lookup-var check exit 0. These diagnostics were displayed in
  the tool transcript, not retained separately. TypedNormalFibres subsequent
  checks /tmp/pts-rk-native-typing.7y6ECx/{typed-fibre,typed-pack}.log exit 0.
- FiniteApplication: /tmp/pts-rk-finite-application.fsuWC1/attempt-{01..05}.log,
  exits 42/0/0/0/0. First check preceded the shared seed-bound alias.
  Final version proves size unconditionally and tests normality only.
- TypedApplication: /tmp/pts-rk-typed-application.PAkBBz/attempt-{01,02}.log,
  both exit 0 without warnings; final regression inhabits the original typed
  input premises using original constructors.
- FiniteTrace: /tmp/pts-rk-finite-trace.WuXhVl/attempt-{01,02}.log, exits 42/0.
  Explicit a,n,s indices repaired inference through noninjective capacity.
  See FiniteTrace-check.txt.
- First note build /tmp/pts-rk-combinatory-note.bB5vJG compiled but failed
  glyph validation, exit 1: inline code ≤ was missing in Latin Modern Mono;
  ∥ was missing in DejaVu Sans Mono. Mathematical prose and Luaotfload's
  Latin Modern Math fallback repaired the glyphs. Validation remained intact.
  The two subsequent builds and both PDF inspections exited 0. A diagnostic
  fc-list probe reported the host's fontconfig configuration warnings; no
  global font configuration was changed.
- No build timeout or unsafe proof workaround occurred.
- A broader whitespace check of all docs/direct-r-handoff exited 2 on
  pre-existing raw command/kernel logs and two older inspector EOF blanks.
  Those historical files were preserved. The scoped check above passes;
  untracked new Agda/prose/Swift sources were also checked explicitly.
  Generated raw logs retain their original whitespace.

## Exact mathematical boundary

The original six native typing rules, annotated beta equivalence, context
lookup and semantic redex ranks are transcribed in NativeTyping.agda.
No alternative checker is used. The normal syntax is genuinely IIR
(Nf/NonLamNf/erase); its exact/bounded fibres inject into actual Fin types.

The bound requires a fixed label dictionary Fin a → Nat and a≤N. Distinct
U_i:U_0 already refute the unqualified rank/length-only statement.
For TypedNormal, N is exact annotated length and d bounds the type rank.
For TypedInputs, d is the exact sort rank of the function product, and
N=1+|f|+|y|. Dictionary entries and external supplied types are parameters,
not counted inhabitants of the fibre.

Raw size and every-single-beta peak bounds, finite state encodings, actual
finite-indexed beta traces and the successful-result cardinality are proved.
Typing/rank/reduction witnesses are propositionally truncated so that
derivations do not inflate the carrier.

The total typed Agda normalizer is NOT complete. applyTypedWithin returns
Maybe(Result inputs), not TypedResult. The latter's cardinal bound is proved,
but not its inhabitance or the function's preservation theorem. The remaining
native obligations are:

1. Original subject reduction via context/substitution/conversion lemmas.
2. Rank uniqueness/safety/descent and the normal-application rank bound, giving
   Normal(rounds d (app f y)) from the existing legitimate TypedInputs.
3. Combine these to eliminate Maybe and return the exact Y[y] typed fibre.
4. For a strict carrier-only operational interpretation, replace Raw-valued
   internal construction by carrier-valued transitions. A finite-indexed
   representation of the resulting path is already proved, but whole walks,
   arbitrary proof objects and machine allocations are not bounded.

Relevant Rocq starting points are Preservation.subject_reduction,
NormalizationComplexity.Descent.bounded_rounds_normal, and
Combinatory.QuantitativeNormalization.normal_application_rank_bound /
normalized_application. Do not assume those targets as new Agda parameters,
change original rules, erase annotations or weaken safety checks.
