# Original PTS model soundness — 2026-10-14

Parent eb835a29c2e3f311ec13b1fc2bdaa26b3a33ef96. Original semantic
soundness/conversion are now proved. Internal BZC + GCH + hierarchy
derivability remains open. See AUDIT.v and the complete printed types;
explicit hierarchy/classical/cardinal/Choice parameters are retained.

## Environment and successful baseline

All commands run at the repository root with:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/hereditary-baseline" bash tools/check-local-ci.sh > /tmp/pts-rk-hereditary-baseline.log 2>&1
```

Baseline exit 0, all 168 stages passed, including pristine upstream.
Compiler versions are retained in versions.log from the final driver.

## Incremental compiler history

All raw failed and successful attempts are retained. No timeout is counted
as success. N in a command denotes the historical attempt number, not a
command rerunning old source revisions.

RankedSubstitution helper attempts 1,2 exited 1,0 (dependent Fin index).
Root-body extraction attempt 1 exited 0. Integrated hereditary attempt 1
exited 0, as did the later arbitrary certified-application extension.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/RankedSubstitution.vo > /tmp/pts-rk-hereditary-helpers-N.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/RankedRootBeta.vo > /tmp/pts-rk-hereditary-root-body-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/RankedHereditary.vo ZFC_model/RealizationInduction.vo > /tmp/pts-rk-hereditary-integrated-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/RankedHereditary.vo > /tmp/pts-rk-hereditary-application-1.log 2>&1
```

Standalone hereditary attempts 1–7 exited 0,1,1,0,1,1,0 as the file grew.
Attempts 2,3 fixed binder helper inference and conjunctions. Attempts 5,6
fixed congruence typeclass resolution in the main all-rank induction.
Attempt 6 retained a Show diagnostic; final source has none.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 rocq c -Q _build/default/vendor/zfc ZFC -Q _build/default/theories PTSrk -Q _build/default/ZFC_model PTSrkModel -Q /tmp/pts-rk-hereditary.S3MBci PTSrkModel -o /tmp/pts-rk-hereditary.S3MBci/RankedHereditary.vo ZFC_model/RankedHereditary.v > /tmp/pts-rk-hereditary-N.log 2>&1
```

Standalone normalization attempts 1–8 exited 1,1,0,1,0,1,1,0. Attempt 1
used the previous scratch mapping, which duplicated the integrated
RankedHereditary library. Attempts 2–8 used a fresh output directory.
Other failures fixed explicit sort parameters, a context argument, valuation
reconstruction and conversion inference. No theorem premise was weakened.

```sh
# Attempt 1 used -Q /tmp/pts-rk-hereditary.S3MBci PTSrkModel and its output directory.
opam exec --switch=pts-rk-ci -- timeout 180 rocq c -Q _build/default/vendor/zfc ZFC -Q _build/default/theories PTSrk -Q _build/default/ZFC_model PTSrkModel -Q /tmp/pts-rk-normalization.RhcGEd PTSrkModel -o /tmp/pts-rk-normalization.RhcGEd/RankedNormalization.vo ZFC_model/RankedNormalization.v > /tmp/pts-rk-ranked-normalization-N.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/RankedNormalization.vo > /tmp/pts-rk-ranked-normalization-integrated-1.log 2>&1
```

Normalization integration exited 0. ModelSoundness attempts 1–5 exited
1,0,1,1,0. Attempt 1 corrected the generalized arguments of an existing
coherence theorem; attempts 3,4 corrected the empty valuation used in the
external Bottom corollary. Attempt 5 includes all final semantic endpoints.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/ModelSoundness.vo > /tmp/pts-rk-model-soundness-N.log 2>&1
```

## Final independent verification commands

The fresh build directory was allocated by
mktemp -d /tmp/pts-rk-soundness-fresh.XXXXXX. ALL final commands below and
the five source comparisons exited 0. The selected fresh dependency build
printed 420 closed reports; all 14 explicit audit reports are closed.
The recursive summary lists only upstream functional_extensionality_dep
and no unsafe settings. The original PTS sources/rules are unchanged.
Adjacent raw logs and the CI result retain the actual evidence.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-soundness-fresh.q3YE9C --display=short --no-buffer ZFC_model/ModelSoundness.vo > /tmp/pts-rk-soundness-fresh.log 2>&1
for soundness_module in RankedSubstitution RankedRootBeta RankedHereditary RankedNormalization ModelSoundness; do
  cmp "ZFC_model/$soundness_module.v" "/tmp/pts-rk-soundness-fresh.q3YE9C/default/ZFC_model/$soundness_module.v"
done
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-soundness-fresh.q3YE9C/default/vendor/zfc ZFC -Q /tmp/pts-rk-soundness-fresh.q3YE9C/default/theories PTSrk -Q /tmp/pts-rk-soundness-fresh.q3YE9C/default/ZFC_model PTSrkModel PTSrkModel.ModelSoundness PTSrkModel.RankedNormalization PTSrkModel.RankedHereditary PTSrkModel.RankedSubstitution PTSrkModel.RankedRootBeta > /tmp/pts-rk-soundness-kernel.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 rocq c -Q /tmp/pts-rk-soundness-fresh.q3YE9C/default/vendor/zfc ZFC -Q /tmp/pts-rk-soundness-fresh.q3YE9C/default/theories PTSrk -Q /tmp/pts-rk-soundness-fresh.q3YE9C/default/ZFC_model PTSrkModel -o /tmp/pts-rk-soundness-fresh.q3YE9C/AUDIT.vo docs/direct-r-handoff/verification/model-soundness-2026-10-14/AUDIT.v > /tmp/pts-rk-soundness-assumptions.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/model-soundness-final" bash tools/check-local-ci.sh > /tmp/pts-rk-soundness-ci.log 2>&1
```

The final local driver includes 171 stages. It also runs actionlint and
builds pristine upstream. Local driver results do not assert hosted CI
success. No PTS rule or original denotation/validity definition changed.
No admitted proof, new axiom, unsafe checking flag or annotation erasure
was introduced. All temporary compiler artifacts stayed outside sources.

## Remaining foundation-strength work

There is no remaining semantic conversion/fundamental-theorem obligation
in the supplied hierarchy model. The material BZC + GCH + existence of
V_(omega+omega) target still requires internal derivations of the same
construction, explicit GCH/hierarchy formulas, and bounded definability of
the denotation predicates used by relational selection. Ens satisfaction of
BZC and closed Rocq assumption reports alone do not establish those claims.
