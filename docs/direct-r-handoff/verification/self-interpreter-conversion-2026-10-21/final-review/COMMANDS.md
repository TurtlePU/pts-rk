# Scoped operations and full-source conversion — final review

Verified on 21 October 2026 at base commit
`e822cd62df393faf4d5e4ed0c4c8fed173ccba6f`, with all six new proof
modules, Dune and Audit frozen. No Git/index mutation or proof edit was
performed during this audit. Parent owns the note/PDF and handoff updates.

## Results

- Fresh absolute Dune aggregate: exit 0, **800** closed assumption reports.
  Audit itself contains 253 Check/Print pairs. The increase is 107 new
  module reports plus 47 new aggregate reports over the previous 646.
- Recursive `rocq check -silent -o` of original `PTSrk.Ranks` and the
  complete self-interpreter Audit: both exit 0.
- Original core inventory is byte-identical to the retained pristine
  upstream inventory. The loaded aggregate lists only the pre-existing
  `Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep`;
  no type-in-type, unsafe fixpoints or assumed positivity.
- Complete `bash tools/check-local-ci.sh`: exit 0, actionlint successful,
  **226/226** staged checks PASS. The driver freshly builds pristine
  upstream `723cf2ec61c737ae82ba33d2e7db44f650122b0e`.
- Original kernel, NormalizationComplexity sources and frozen PR #1 ZFC
  sources match the checked reference `ffa7131`; all comparisons exit 0.
- All 52 source/Dune manifest entries remained byte-identical across the
  fresh aggregate/kernel run. The six-module safety and whitespace scans
  found no matches; scoped Git whitespace and shell-syntax checks pass.
- No failed final-audit stage or timeout. Development failures remain in
  each module's own evidence; no stage or theorem was weakened to obtain green.

Aggregate timing: 01:58:10–02:00:37 UTC. Complete local CI timing:
01:58:11–01:59:15 UTC. Known logical-loadpath remapping and deprecated
arithmetic-notation warnings are retained in the raw logs.

## Exact runners and environment

Ignored local-only raw artifacts:
`_build/self-interpreter-conversion-final-review.1Axp2t/`.
The complete scripts are `AUDIT.sh`, `CI.sh`, `CHECK-SOURCES.sh`; outputs
include `audit-driver.log`, `fresh-build.log`, `core-kernel.log`, `kernel.log`,
`status.tsv`, `ci-driver.log`, `staged/stages.tsv`, both source manifests,
versions and all comparison logs. Historical/local raw paths are not
promised to exist in a clean checkout.

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
timeout 1200 opam exec -- dune build \
  --build-dir=/tmp/pts-rk-self-conversion-audit.SRZ7pU \
  --display=short --no-buffer -j 2 @theories/self_interpreter/audit
timeout 1200 opam exec -- rocq check -silent -o \
  -Q /tmp/pts-rk-self-conversion-audit.SRZ7pU/default/theories PTSrk \
  PTSrk.Ranks
timeout 1200 opam exec -- rocq check -silent -o \
  -Q /tmp/pts-rk-self-conversion-audit.SRZ7pU/default/theories PTSrk \
  -Q /tmp/pts-rk-self-conversion-audit.SRZ7pU/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
  -Q /tmp/pts-rk-self-conversion-audit.SRZ7pU/default/theories/self_interpreter PTSrk.SelfInterpreter \
  PTSrk.SelfInterpreter.Audit

export DIRECT_R_LOCAL_HOME=/Users/akuklev/.local/share/pts-rk-ci
export DIRECT_R_LOCAL_SWITCH=pts-rk-ci
export DIRECT_R_LOG_DIR=/Users/akuklev/air/pts-rk/_build/self-interpreter-conversion-final-review.1Axp2t/staged
export DIRECT_R_JOBS=2
export DIRECT_R_STAGE_SECONDS=1200
bash tools/check-local-ci.sh
```

Versions: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2,
Dune 3.23.1, opam 2.6.1. Full package inventory and switch export are retained.
The pristine comparison used
`docs/direct-r-handoff/verification/self-interpreter-2026-10-20/baseline/upstream-kernel.log`.

## Independent contract review

All six modules passed read-only mathematical review. ScopedTarski, written
by this reviewer, separately passed the paper-analysis agent's independent
review; that result is recorded in `../scoped/COMMANDS.md`.

- FullSource mirrors every original rule, with unrestricted conversion
  intermediates. Completeness is Prop-valued inhabitation, not computational
  extraction from opaque Prop. Its finite source ceiling is not asserted
  sufficient for a future target quoter.
- FullConversion constructs actual forward traces and structural comparison
  on raw syntax. Success is sound on raw terms; completeness, normality and
  every-stage original typing require independently typed endpoints in an
  original well-formed context. No arbitrary untyped zigzag is translated.
- CanonicalSource preserves literal source terms/types/contexts/annotations.
  Executable comparison supplies the join; validity is used only to rule
  out failure. Output certification is proved, not inserted into the input
  datatype. Certified coverage explicitly requires well-formed contexts.
- ScopedTarski supports arbitrary fresh-scope inputs and computed concrete
  child spines. Its recovery is through the actual recursively lifted fill;
  annotation contraction is a genuine additional beta step. Exact renaming
  is not confused with false smart-substitution equality. Fidelity is local.
- TarskiBeta has the exact finite-polymorphic formation rank
  `max(c+1,max(b+2,d+1))`. The independently typed closed normal identity
  witness specializes to literal reflexivity. The separate beta field is
  not assumed derivable from arbitrary existing product-law evidence.
- TarskiBetaSignature adds exactly `(k+1)^3` bounded beta fields, proves
  original context formation, actual TypedSub and literal field recovery.
  Its inherited environment supports ScopedTarski typing/normality; it is
  not automatically the concrete spine required by scoped recovery.

The updated note and development README were also reviewed. The note's
abstract now explicitly restricts typed source certificates to well-formed
contexts, and trace typing refers to each starting term's original type.
Neither prose source claims a full dependent quoter, internal source
conversion interpretation, function extensionality or global coherence.
PDF compilation/visual verification is recorded by the parent separately.

## Frozen hashes

SHA-256 of the complete 52-entry source manifest:
`4dc10800b7e93f241f45009d95ae44b8d87ba646307d67ba03a040e2f060f151`.

```text
a742200604c651f8344cb6811c28f1bc91f0ecb57e47b18ac30dbd211854f46d  FullSource.v
ca5561a92c99882955cb6608a2b23a3a5b3591bf4579a6afa59a53501b829bd5  FullConversion.v
0ab23ea3ba216deccdd18afa9045df93cc7eed5233e765fd253a9c7e264523f2  CanonicalSource.v
244dcd3bbb11963ff2c2c0b52ac31e3ef683b69fda42ec98c15b7660ab14fe90  ScopedTarski.v
bffb338428c1940001892754cb57af1591c965805b909e3a8fbfd4e6b5b66ba0  TarskiBeta.v
4a6046d73a383f2b80e92cfe6f13993b2f560658788e5bccac23449c9849e99b  TarskiBetaSignature.v
062e14647c79faf02be5ef8bd45ba4747b12ee6cf416f91a09e5d3c1e1ad0aba  Audit.v
d940aae222294cfb51a40ad93734f1b88fd5e9a14627dbe5452f03329634d010  dune
```
