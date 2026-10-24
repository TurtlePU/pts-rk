# Internal fixed-fragment Horn soundness — 23 October 2026

Five added modules, 95 public reports: HornProofEncoding 18,
HornProofRealization 13, GuardedFiniteSupport 36, HornInternalSoundness 11,
MM0GuardedInternalReflection 17. The proof type depends only on the finite
positive clauses/query, not a model or truth table. The internal consumer
and rule constructors accept arbitrary encoded native proof inhabitants.
Type ranks are <=3 and <=4. External converse and actual guarded Void
specialization retain native canonicity. Internal budget-polymorphic raw
source decoding/guard provenance and original-PTS catalogue completeness
remain open; this is not an independent internal consistency proof.

## Scope and individual checks

Read root/development READMEs, live STATE/DECISIONS/BUILD, Dune, existing
diffs and prior final verification before edits. Existing 58 combinatory
proofs, original kernel, shared equality, MM0 and 52 Agda sources are
preserved. Five Dune registrations and audit dependencies are additive.
No staging, commit, push, cleanup or unrelated process action is performed.
HEAD remains 6a8dc984fb59a9b3743503cd405ffe59a31d1978.

Exact individual commands/outputs/timestamps/exits are in encoding/,
realization/, internal/, and the separate sibling
../combinatory-internal-reflection-2026-10-23/finite-support/.
These use the preceding fresh dependency objects, not a new whole build.
Encoding attempt01 fails at renaming naturality;02 passes all18 endpoints.
Realization retains all13 attempts; final13 passes all13 endpoints and the
complete recursive kernel. Its first inventory wrapper compares raw output
to whitespace-normalized archival text; the corrected comparison uses the
raw pristine inventory and passes, without a proof change.
Support attempts01/02 fail;03 passes27 and04 passes all36 endpoints.
Root internal attempts01/02/03 pass10/11/11 endpoints. Guarded attempts01/02
fail at an iff application and unresolved query placeholder;03 passes11;
04 fails at tactic goal distribution;05/06 pass all17. No new axiom, unsafe
cast, admitted proof or disabled checking is introduced.

## Fresh frozen-source audit

```sh
bash docs/direct-r-handoff/verification/combinatory-internal-horn-2026-10-23/AUDIT.sh
```

Started 19:53:09 UTC after every owner froze their source. Live logs:
_build/combinatory-internal-horn-audit.JMyhh0; fresh absolute build:
/tmp/pts-rk-internal-horn.6x5cr6; pristine:
/tmp/pts-rk-internal-horn-pristine.LZ2nx4; archive audit.td6KVY.
Pinned Rocq 9.2, OCaml 4.14.2, Dune 3.23.1, Stdlib 9.1.0 and Equations
1.3.2+9.2. Pristine baseline 723cf2ec61c737ae82ba33d2e7db44f650122b0e.

Fresh 63-module compilation PASSES 19:53:19–19:55:55 UTC (156 seconds),
exit0. Exactly 980 own/981 aggregate closed reports, 95 new. Ranks prints
the sole additional report. Complete recursive kernel verification PASSES
19:55:55–19:56:20 UTC (25 seconds), exit0. The entire context inventory is
byte-identical to freshly built pristine: inherited
functional_extensionality_dep only, no type-in-type, unsafe fixpoints or
assumed positivity. All66 before/after hashes agree; all58 previous proofs,
original kernel, shared equality, MM0 and52Agda sources are unchanged.
Exactly five additive Dune registrations are verified. Literal MM0 text
crosscheck, safety and tracked/new-file whitespace all pass. The entire
driver exits0 at19:56:22 UTC; no failed final gate is being omitted.
The driver retains every exact command, version, exit and source hash.
Safety checks and upstream comparison are unchanged. No new Agda/MM0
checker or full repository CI run is claimed.

## Note and PDF

```sh
bash docs/direct-r-handoff/verification/combinatory-internal-horn-2026-10-23/NOTE-CHECK.sh
```

First attempt 19:53:49–19:54:05 UTC fails validation, exit1, on an 80.34396pt
overwide display; the previous PDF is retained. Live logs
_build/combinatory-internal-horn-note.DJhQdi; build
/tmp/pts-rk-combinatory-note.mVxPaS; archive note.4vLwyr. Split the two
definitions into aligned lines; no mathematical or proof-source change.

Final build passes 19:55:35–19:55:50 UTC; inspection passes19:55:50–52.
Live _build/combinatory-internal-horn-note.fi3gJi; rendered pages
/tmp/pts-rk-internal-horn-note.dyMeWT; archive note.nVOBmg.
31 pages, three-page MM0 appendix, 61 Rocq and27 Agda badges,44 Agda links,
129 total links. Every page renders; all proof/source targets exist, excerpt
highlighting and document ordering pass. Pages1,24,25 are visually reviewed:
the abstract, guarded theorem, new encoding/consumer and exactness formulas
fit cleanly. The final manifest covers note/PDF/build-script/inspector.
