# STLC reduction verification — 2026-10-14

Parent b61eef647cc7e3572e57f3f83a73d4ca221b46cb; uncommitted source update.
Environment for all direct opam commands:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

Rocq 9.2.0, OCaml 4.14.2, Dune 3.23.1, Equations 1.3.2+9.2.
Commands run from repository root. Logs retained verbatim.

1. Baseline: `DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/tower-hardness-baseline" bash tools/check-local-ci.sh > /tmp/pts-rk-tower-hardness-baseline.log 2>&1` — exit 0.
2. Iterations 1–5: `opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer theories/NormalizationComplexity/STLCEmbedding.vo > /tmp/pts-rk-stlc-N.log 2>&1` (replace N by iteration). Compiler exits: 1, 1, 1, 1, 0. Iteration 3's enclosing shell returned 0 after tail, but its compiler failed; the failure is retained. Errors respectively concerned lifted substitution, explicit weak-renaming instantiation, a generated reduction hypothesis name, and a second generated hypothesis name. No proof statement was weakened to fix these errors.
3. Fresh directory allocated with `mktemp -d /tmp/pts-rk-stlc-fresh.XXXXXX`, yielding `/tmp/pts-rk-stlc-fresh.ybfesA`.
4. `opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-stlc-fresh.ybfesA --display=short --no-buffer theories/NormalizationComplexity/Audit.vo > /tmp/pts-rk-stlc-fresh.log 2>&1` — exit 0. 96 closed reports: 95 audit checks plus one upstream report. Exact public theorem type at end of log.
5. Same build after comments/formatting cleanup, output `/tmp/pts-rk-stlc-final-audit.log` — exit 0; 95 closed audit reports.
6. `opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-stlc-fresh.ybfesA/default/theories PTSrk PTSrk.NormalizationComplexity.Audit > /tmp/pts-rk-stlc-kernel.log 2>&1` — exit 0. Recursive checking, no admitted dependency flags. Global Stdlib extensionality entry matches the prior upstream baseline; all new theorem-specific reports are closed.
7. `DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/tower-hardness-final" bash tools/check-local-ci.sh > /tmp/pts-rk-stlc-ci.log 2>&1` — exit 0, 81 stages pass. The normalization audit imports the new embedding. Full per-stage logs remain under that diagnostic directory; result and stage summaries are copied here.
8. Repeat command 6 after the final source cleanup, output `/tmp/pts-rk-stlc-final-kernel.log` — exit 0.

This verifies the reduction, not an external STLC hardness theorem or a machine-level complexity classification. No axiom was added for the cited lower bound.
