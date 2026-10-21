# Finite dependent signature — fresh final review, 20 October 2026

Base commit: `e822cd62df393faf4d5e4ed0c4c8fed173ccba6f`.
All five new modules and Audit/Dune were frozen before this run. No proof,
index or Git reference was changed by the verification. Parent retained
ownership of concurrent note/README/handoff updates.

## Results

- Fresh absolute aggregate compilation: exit 0, **527** closed assumption
  reports: 418 previous, 68 new module reports, 41 added Audit reports.
  Audit has 167 public Check/Print pairs.
- Recursive original and aggregate `rocq check -silent -o`: exit 0.
- Original kernel inventory: byte-identical to the retained pristine
  `723cf2ec61c737ae82ba33d2e7db44f650122b0e` inventory.
- Frozen ZFC, original kernel and NormalizationComplexity source comparisons
  against `ffa7131`: exit 0 with empty differences.
- All 41 self-interpreter proof files plus Dune: hash-stable during the audit.
- Full `bash tools/check-local-ci.sh`: exit 0; actionlint and all **226/226**
  stages pass, including a new isolated pristine-upstream build. No stage was
  removed or weakened.
- New-source safety/whitespace scans: no matches (expected `rg` exit 1).
  Scoped `git diff --check` and runner shell-syntax check: exit 0.

Every new public assumption report is closed. The recursive loaded-library
inventory contains the unchanged upstream declaration
`Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep`;
it reports no type-in-type, unsafe fixpoints or assumed positivity. A loaded
library inventory is not a theorem dependency report; no new extensionality
assumption was added to these theorems.

Aggregate elapsed interval: 12:11:23–12:12:36 UTC. Full CI: 12:11:24–12:12:10
UTC. Neither final runner failed or timed out. Earlier module-development
failures remain documented in the sibling evidence directories.

## Exact environment and commands

Raw local-only ignored evidence:
`_build/self-interpreter-signature-final-review.rFr76B/`.
Fresh Dune build: `/tmp/pts-rk-self-signature-audit.qlUK8l`.
The raw directory contains the executable command records `AUDIT.sh`, `CI.sh`,
`CHECK-SOURCES.sh`, driver logs, full versions/package list, source manifests,
all stage logs/status codes, and the full staged-driver evidence in `staged/`.
These local raw paths are provenance, not committed/reproducible artifacts.

Pinned versions: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2,
Dune 3.23.1 and opam 2.6.1.

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
build_dir=/tmp/pts-rk-self-signature-audit.qlUK8l
timeout 1200 opam exec -- dune build --build-dir="$build_dir" \
  --display=short --no-buffer -j 2 @theories/self_interpreter/audit
timeout 1200 opam exec -- rocq check -silent -o \
  -Q "$build_dir/default/theories" PTSrk PTSrk.Ranks
timeout 1200 opam exec -- rocq check -silent -o \
  -Q "$build_dir/default/theories" PTSrk \
  -Q "$build_dir/default/theories/NormalizationComplexity" PTSrk.NormalizationComplexity \
  -Q "$build_dir/default/theories/self_interpreter" PTSrk.SelfInterpreter \
  PTSrk.SelfInterpreter.Audit

diff -u docs/direct-r-handoff/verification/self-interpreter-2026-10-20/baseline/upstream-kernel.log \
  _build/self-interpreter-signature-final-review.rFr76B/core-kernel.log
git diff --exit-code ffa7131 -- theories/ZFC_model
git diff --exit-code ffa7131 -- \
  theories/AbstractRewriting.v theories/Congruence.v theories/Confluence.v \
  theories/Context.v theories/DefEq.v theories/Inversions.v \
  theories/Preservation.v theories/Ranks.v theories/Reduction.v theories/SN.v \
  theories/Syntax.v theories/Typing.v
git diff --exit-code ffa7131 -- 'theories/NormalizationComplexity/*.v'
bash -n tools/ci-check-direct-r.sh tools/build-self-interpreter-note.sh

export DIRECT_R_LOCAL_HOME=/Users/akuklev/.local/share/pts-rk-ci
export DIRECT_R_LOCAL_SWITCH=pts-rk-ci
export DIRECT_R_LOG_DIR=/Users/akuklev/air/pts-rk/_build/self-interpreter-signature-final-review.rFr76B/staged
export DIRECT_R_JOBS=2
export DIRECT_R_STAGE_SECONDS=1200
bash tools/check-local-ci.sh
```

The original-kernel comparison uses the retained independently checked
pristine inventory; this run also actually rebuilds pristine upstream in
the CI `01-upstream` stage. No cached compilation is used as new Print
Assumptions evidence. Known logical-loadpath remapping and deprecated
notation warnings remain visible in the logs.

## Contract and prose review

Read-only review of `TarskiPalette`, `TarskiLawFamily`, `TarskiOperations`
and `IndexedCoherence` found no contract defect. In particular:

- The four base blocks and two product blocks are literal original contexts;
  field identity inhabitants are constructed independently of `TypedSub`.
- Product pairs are bounded by `a,b <= k`, with carrier availability through
  `k+1`; there is no infinitely extensible all-available-ranks closure claim.
- The family witness is polymorphic in independently typed code inputs.
  Applied operations use the actual finite law field, not an extra assumed
  equality witness at each call.
- Recovery after actual replacement returns literal substituted inputs,
  preserving their redexes. Normality of casted operations retains the
  explicit decoded-annotation normality premise.
- Equality composition and ordinary nondependent congruence preserve the
  predicate level. Reflexivity laws are strong beta equations; arbitrary
  proof identity laws are applied-only, with no eta/funext assumption.

The updated note abstract, finite-signature/coherence subsections, six-layer
count/sort table, status/remaining-program text and development README match
these boundaries. No prose correction was requested. Generic telescope
closure does not construct a recursively quoted source body. Full original
dependent derivation coverage, generated binder/substitution/conversion
coherence, annotation normality and strong faithful dependent quotation
remain separate obligations, not conclusions of this milestone.

## Frozen source identity

SHA-256 of the complete 42-entry source manifest:
`15d35d203b5e59487c3ba7193ab399954d2bcd39c1747254be70441ba74f3181`.
The beginning/end manifests compare byte-for-byte.

```text
137c4fd12afe57ebea28692c5c456e510d5fd25254df6959f4acca6107f6973b  IndexedCoherence.v
9c302e23c9315eb14f12c14dda6fbf2267b88094f751a54820717d682d3fc423  TarskiLawFamily.v
cdbb248b125cc2be46e16f6ab25b93c8d12a0c354ceaed2d4eebe61decb87e81  TarskiPalette.v
034281219e3e1011f7c690cbfc9184990d6b4f4c1d53a3e76ce7c5f176d92acc  TarskiSignature.v
dd6b69c39e36712ce29df26626f80a0c3d179687193d11c7cee87bf9491311c9  TarskiOperations.v
0a444672e0232947a19a3c0266cb2e83840f1206640a53dcee502bb9c1593ae3  Audit.v
90d2360b7fafbc0d44c7818675d792d24d841093b185ae7b106de8f32512820c  dune
```

All listed files are under `theories/self_interpreter/`. No commit or push
was performed in this continuation.
