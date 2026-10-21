# Independent final Tarski audit — 20 October 2026

Base HEAD: `e822cd62df393faf4d5e4ed0c4c8fed173ccba6f`.
No Git mutation or proof edit was made during this final audit. The seven new
modules, aggregate Audit and Dune registration were frozen before launch.
Parent owns note/PDF and handoff integration. All results concern this local
worktree, not remote CI or a new publication.

## Results

- Fresh absolute Dune aggregate: **418 closed assumption reports**, exit 0.
  This is the previous 326 plus 63 reports from seven new modules and 29 new
  aggregate endpoints (126 aggregate endpoints total).
- Recursive kernel checks of `PTSrk.Ranks` and `PTSrk.SelfInterpreter.Audit`:
  both exit 0. The core inventory is byte-identical to the retained pristine
  `723cf2ec61c737ae82ba33d2e7db44f650122b0e` inventory. Full CI additionally
  builds a new isolated archive of that actual upstream revision.
- The aggregate loaded-library inventory contains only the pre-existing
  `Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep`.
  Type-in-type, unsafe fixpoint and assumed-positivity inventories are empty.
  All new theorem assumption reports themselves are closed.
- Original kernel, frozen PR #1 ZFC model and NormalizationComplexity sources
  remain byte-identical to revision `ffa7131` by scoped Git comparisons.
- All 36 proof sources plus Dune pass exact before/after SHA-256 comparison.
- Full local CI: **226/226 stages pass**, including actionlint, the fresh
  upstream build and self-interpreter audit. No stage was weakened.
- Scoped whitespace, shell syntax and new-module safety checks pass.
  The safety scan returns no matches (`rg` exit 1), not a compiler failure.

Aggregate ran 11:41:24--11:42:21 UTC; CI ran 11:41:25--11:42:03 UTC.
Both drivers exit 0. There were no final-driver failures or timeouts.
Intermediate module failures are preserved in their individual subreports;
the closed-casts report records every attempt, including the failed ones.
An additional post-audit source-scan wrapper initially exited 1 because a
shell assignment was accidentally concatenated to the preceding command;
the corrected wrapper passes. Its observed error is retained in
`source-helper-attempt-01.txt`; no proof or audit/CI command changed.
Known logical-loadpath remapping warnings remain in the raw logs.

## Contract and prose review

Read all seven final sources and the note's new Tarski section/status against
their literal original-PTS theorem statements. No correction is required.

1. IndexedEquality keeps predicate rank explicit: for `A:Ua`, its transport
   type has sort `max(a+2,b+1)`. Original annotated reflexivity and application
   transport are constructed; no same-level impredicative symmetry is assumed.
2. TarskiProducts quantifies genuine carrier inputs, not source results to
   be proved. Its operation type has exact sort `a+2`, while the decoded
   dependent product has sort `c=max(a+1,b)`. The identity constructor is an
   actual closed normal original term with beta specialization.
3. TarskiUniverses constructs normal closed witnesses for EVERY external
   rank. The law has sort 2; its identity instance is justified by actual
   `id0 Ua -> Ua`, not an equation postulated for arbitrary decoders.
4. TarskiCasts obtains both directions using predicate rank `c+1` and two
   arrow motives. The law has sort `c+2`. Abs/App and universe casts consume
   separately typed object witnesses. Substitution and local neutral-cast
   normality are proved without assuming global quotation correctness.
5. TarskiIdentity supplies the product-law witness itself as reflexivity at
   the common dependent product. Original application/conversion typing is
   established before recovery. Literal `f` and `f u` are recovered, with
   neither eta expansion nor precomputed normal semantic payloads.
6. ClosedTarskiCasts genuinely closes both programs at scope zero over
   `S`, `T`, and evidence. Programs and types are normal; exact type sort is
   `c+3`. Direct run typing, three-step specialization and literal reflexivity
   computation are separate proved contracts.
7. EtaBoundary proves only that pointwise beta agreement does not imply
   original beta conversion, even inside actual dependent type indices in
   an independently constructed valid context. It does not assert that all
   internal extensionality witnesses or dependent PHOAS constructions are
   impossible.

The note accurately retains the open work: finite dependent palette closure,
translation of every original derivation, internal conversion/substitution
coherence, full quotation normality and faithful strong recovery. These
local operations are not mislabeled as a full dependent interpreter.

## Exact reproduction and local raw evidence

Local-only ignored raw directory:
`_build/self-interpreter-tarski-final-review.VnAQed`.
Fresh absolute Dune directory: `/tmp/pts-rk-self-tarski-audit.OveK1T`.
Exact scripts `AUDIT.sh` and `CI.sh`, full logs, package listing, status codes,
stage table and before/after manifests are retained there. They are not
tracked source artifacts and need not exist in another checkout.

Pinned environment and aggregate commands:

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
timeout 1200 opam exec -- dune build \
  --build-dir=/tmp/pts-rk-self-tarski-audit.OveK1T \
  --display=short --no-buffer -j 2 @theories/self_interpreter/audit
timeout 1200 opam exec -- rocq check -silent -o \
  -Q /tmp/pts-rk-self-tarski-audit.OveK1T/default/theories PTSrk PTSrk.Ranks
timeout 1200 opam exec -- rocq check -silent -o \
  -Q /tmp/pts-rk-self-tarski-audit.OveK1T/default/theories PTSrk \
  -Q /tmp/pts-rk-self-tarski-audit.OveK1T/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
  -Q /tmp/pts-rk-self-tarski-audit.OveK1T/default/theories/self_interpreter PTSrk.SelfInterpreter \
  PTSrk.SelfInterpreter.Audit
```

Full CI command:

```sh
DIRECT_R_LOCAL_HOME=/Users/akuklev/.local/share/pts-rk-ci \
DIRECT_R_LOCAL_SWITCH=pts-rk-ci DIRECT_R_JOBS=2 DIRECT_R_STAGE_SECONDS=1200 \
DIRECT_R_LOG_DIR=/Users/akuklev/air/pts-rk/_build/self-interpreter-tarski-final-review.VnAQed/staged \
bash tools/check-local-ci.sh
```

Resolved versions: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2, Dune 3.23.1, opam 2.6.1. The 226-stage worktree contains
unrelated unpublished developments; the earlier scoped publication's
172-stage result is a different source scope, not a reduced version of this
verification. Neither its stage count nor its historical timings are reused.

Frozen new-source hashes (SHA-256):

```text
7c45de73800705a9ea130719785fcecea020b72961de10556d55af9a3bab93df  IndexedEquality.v
27e6de3d9f10b7d07c9c68c3acf89fb6f40e632e423103351adc72a7fe1bd75f  TarskiProducts.v
bdbbe9578102a93d7b82b1a5c3833b38ca2922669edb1bf6bf1f0ea169f7df2e  TarskiUniverses.v
9b60a7f46652ea62e87bc648ed7935833906e270b5643814595073c80b788111  TarskiCasts.v
20687be9c166ad11d0bbd6774b85a1f91228780e579878419dcfa0257e6c2075  TarskiIdentity.v
8f582984be873f3c9d99d019158d3655aedc4b408f587242bf97ba53e2657f62  ClosedTarskiCasts.v
51d22f51e2724052580fc665fdf7f567f3bbac31beb4c0ecda83b7ba320b316b  EtaBoundary.v
d2ecba5ed4832fae5cfff44b5580cd9e0289f213119f6fddb70623f21c8e9bf3  Audit.v
889d75261b370a3184755076cff4aae6620fe2ac37610f2563abc53f6dbd61dd  dune
```

The complete 37-file manifest has SHA-256
`6beafd6b29d5ed6704ee6c9e06ab0808cac61f029b9dd10273372c2f77d7e7f1`.
