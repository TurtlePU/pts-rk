# Ranked certificates and material BZC — 2026-10-14

Verified partial proof checkpoint, parent 3454c9f. Full PTS model soundness
and internal BZC foundation justification remain OPEN. The interruption
occurred while writing this command record, after verification succeeded.
No proof source changed between verification and the commit.

## Reproducible final verification

All commands ran from the repository root. The fresh directory was allocated
with mktemp -d /tmp/pts-rk-ranked-fresh.XXXXXX. Each command below exited 0.

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-ranked-fresh.kI0Mjw --display=short --no-buffer ZFC_model/RankedRootBeta.vo ZFC_model/MaterialZermelo.vo ZFC_model/CanonicalValuationTransport.vo ZFC_model/BoundedModelData.vo ZFC_model/TypedEqualityRenaming.vo ZFC_model/CanonicalHereditary.vo ZFC_model/CanonicalApplication.vo ZFC_model/RealizationInduction.vo ZFC_model/RootBeta.vo > /tmp/pts-rk-ranked-fresh.log 2>&1
for ranked_module in NeutralCutRank RankedDenotation RankedTransport RankedSubstitution RankedRootBeta CanonicalValuationTransport MaterialZermelo; do
  cmp "ZFC_model/$ranked_module.v" "/tmp/pts-rk-ranked-fresh.kI0Mjw/default/ZFC_model/$ranked_module.v"
done
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-ranked-fresh.kI0Mjw/default/vendor/zfc ZFC -Q /tmp/pts-rk-ranked-fresh.kI0Mjw/default/theories PTSrk -Q /tmp/pts-rk-ranked-fresh.kI0Mjw/default/ZFC_model PTSrkModel PTSrkModel.NeutralCutRank PTSrkModel.RankedDenotation PTSrkModel.RankedTransport PTSrkModel.RankedSubstitution PTSrkModel.RankedRootBeta PTSrkModel.MaterialZermelo PTSrkModel.CanonicalValuationTransport PTSrkModel.BoundedModelData PTSrkModel.TypedEqualityRenaming PTSrkModel.CanonicalHereditary PTSrkModel.CanonicalApplication PTSrkModel.RealizationInduction PTSrkModel.RootBeta > /tmp/pts-rk-ranked-kernel.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 rocq c -Q /tmp/pts-rk-ranked-fresh.kI0Mjw/default/vendor/zfc ZFC -Q /tmp/pts-rk-ranked-fresh.kI0Mjw/default/theories PTSrk -Q /tmp/pts-rk-ranked-fresh.kI0Mjw/default/ZFC_model PTSrkModel -o /tmp/pts-rk-ranked-fresh.kI0Mjw/AUDIT.vo docs/direct-r-handoff/verification/ranked-certificates-2026-10-14/AUDIT.v > /tmp/pts-rk-ranked-assumptions.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/ranked-certificates-final" bash tools/check-local-ci.sh > /tmp/pts-rk-ranked-ci.log 2>&1
```

The selected fresh build printed 523 closed reports; the seven new modules
print 53. All twelve explicit assumption reports are closed. The recursive
kernel audit lists only upstream functional_extensionality_dep, with no
unsafe checking settings. Original_realization_from_conversion still has
its explicit, unproved semantic-conversion premise in the printed type.

All 168 local CI stages passed, including pristine upstream. The wrapper
also ran actionlint. This is local workflow-driver evidence, not a hosted
GitHub Actions result. Versions, stages, result and raw logs are retained
alongside AUDIT.v; compiled audit artifacts stayed outside the source tree.

## Retained incremental attempts

Each numbered raw log records the corresponding historical source revision.
Failures were retained, not reclassified as successes. No timeout occurred.

| Log stem | Attempts' exit codes | Main corrections |
| --- | --- | --- |
| pts-rk-neutral-cut-rank | 0,0,1,1,0,1,1,0 | Dependency, pattern, dependent rewriting; later versions extend the theorem |
| pts-rk-ranked-denotation | 1,1,1,0,1,0 | Notation, induction names, inference and import |
| pts-rk-canonical-valuation-transport | 1,1,1,1,1,0 | Inference and binder extensionality |
| pts-rk-material-zermelo | 1,1,0,0 | Pair conversion and von Neumann unfolding; final Choice extension |
| pts-rk-ranked-transport | 1 | Inconsistent scratch dependency artifacts |
| pts-rk-ranked-integrated | 1,1,0 | Consistent rebuild, explicit ranks and import |
| pts-rk-ranked-substitution | 1,0,0 | Explicit fresh-variable rank; final normalized-binder/rank-zero extension |
| pts-rk-ranked-root-beta | 0 | Compiled first attempt |

The isolated certificate, valuation and material-theory kernel checks also
exited 0. The final combined fresh audit supersedes scratch artifacts.
Integrated commands used the environment above and:

```sh
# NeutralCutRank attempts 6–8; replace N by the historical attempt number.
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/NeutralCutRank.vo > /tmp/pts-rk-neutral-cut-rank-N.log 2>&1
# RankedTransport integrated attempts 2–3.
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/RankedTransport.vo > /tmp/pts-rk-ranked-integrated-N.log 2>&1
# RankedSubstitution attempts 1–2.
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/RankedSubstitution.vo > /tmp/pts-rk-ranked-substitution-N.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/RankedRootBeta.vo > /tmp/pts-rk-ranked-root-beta-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/RankedSubstitution.vo ZFC_model/RankedRootBeta.vo > /tmp/pts-rk-ranked-substitution-3.log 2>&1
```

The preliminary incremental baseline exited 0 with empty output retained
in pts-rk-ranked-continuation-baseline.log; its exact target list was not
retained. Use the recorded fresh command above for reproducible evidence.
Earlier checkpoint directories retain the prior accumulated proof work's
commands, successful audits and failures.

## First remaining goal

Generalize certificate_rank_zero_substitution to arbitrary cut rank, with
reductions of both substituted term and assigned type to normal outputs,
preserving both semantic indices. Active-head strict descent and binder
helpers are proved. General hereditary substitution, certificate totality,
agreement with arbitrary original denotations, and internal weak-foundation
justification remain open. STATE.md gives the next exact build command.
