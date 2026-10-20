# Build, logs, and recovery

Finished-development documentation: `bash tools/build-development-docs.sh`
rebuilds the five README.tex/PDF pairs indexed by docs/developments/README.md.
The final build gives 38 pages and passes log, PDF text and visual checks.
A fresh audit of every finished library passes with 1,127 closed reports
and recursive kernel checking. Full local CI in the shared checkout at that
documentation checkpoint stopped at a concurrent self-interpreter error;
that observation does not describe this isolated publication checkout.
Exact commands, failures, local logs and cleanup recovery details are in
[the documentation checkpoint](verification/development-docs-2026-10-20/COMMANDS.md).

## Inspect and preserve

From the repository root inspect git status, branch, recent commits, actual
module files, and Dune configuration. Preserve existing user changes. Record
the checkout, available toolchain, and relevant logs in STATE.md. Never reset
to a historical base or expose credential-bearing URLs or environment values.

## Current layout

All project Rocq sources are under theories:

- theories/*.v: original PTSrk kernel.
- theories/Interpretation_of_R/: shared arithmetic infrastructure.
- theories/Interpretation_of_R/relational/: completed Theorem 4.
- theories/Interpretation_of_R/functional/: completed Theorem 7 and effective
  Theorem5Target witnesses.
- theories/ZFC_model/: original set-model typing soundness and open material
  BZC foundation reduction.
- theories/NormalizationComplexity/: costed normalization bounds and STLC
  conversion reduction.

See [theories/README.md](../../theories/README.md). Rocq library names are
unchanged by the physical moves. Both arithmetic libraries depend on shared
infrastructure and the original kernel, not on each other.

## Toolchain and complete check

The pinned configuration is OCaml 4.14.2, Dune 3.23.1, rocq-prover meta.1,
rocq-core 9.2.0, rocq-stdlib 9.1.0, and rocq-equations 1.3.2+9.2.
Stdlib is independently versioned. Rocq 9.1.1 cannot parse pristine upstream's
Create Rewrite HintDb command.

```sh
bash tools/check-local-ci.sh
# Or, inside an already activated Rocq/Equations switch:
opam exec -- bash tools/ci-check-direct-r.sh
```

The local wrapper selects the dedicated pts-rk-ci switch and runs actionlint
plus the staged build. The CI driver archives pristine upstream commit
723cf2ec61c737ae82ba33d2e7db44f650122b0e into a separate temporary directory
and compiles it before the current developments. It stops at the first actual
failure and retains exit codes, versions, stage logs, and Dune output.
GNU timeout must be available. See [DirectR-CI.md](../DirectR-CI.md) for setup,
platform details, environment overrides, and the Actions workflow.

A timeout is a diagnostic resource limit, not a compiler rejection. A local
successful run does not by itself assert remote CI success.

## Targeted checks and fresh assumptions

From the repository root in the configured environment:

```sh
dune build theories/Ranks.vo
dune build theories/Interpretation_of_R/DirectREval.vo theories/Interpretation_of_R/DirectRCheck.vo
dune build @theories/Interpretation_of_R/relational/audit
dune build @theories/Interpretation_of_R/functional/audit
dune build @theories/ZFC_model/audit
dune build @theories/NormalizationComplexity/audit
```

Use a NEW absolute --build-dir for fresh compilation and assumption output.
A cached successful audit does not rerun Print Assumptions. Record exact
public theorem types and transitive reports, distinguishing upstream logical
assumptions from any newly introduced hypothesis.

tools/check-direct-r.sh is a smaller functional smoke check. Its first target
theories/Ranks.vo is in the working tree, not an isolated pristine baseline.
It does not replace the complete staged driver or the public theorem audits.

A green build proves only statements actually present, with their actual
premises. Original set-model soundness has explicit hierarchy, classical,
cardinal, and choice parameters; it does not establish internal BZC
derivability. The checked STLC reduction does not formalize the cited external
hardness theorem or machine-level complexity classes.

## Historical recovery packages

The modular development is already installed. Do not reapply the packages
in inputs over current sources. HANDOFF.md, LATEST_DECISIONS.md, and original
packages retain their original paths and historical limitations.

If recovery is ever necessary, extract packages to a separate temporary
directory, inspect their base and patches, and adapt without overwriting user
work. Do not apply both an aggregate patch and its constituent patches.
Do not run archived publish.sh or require gh.

## Browser CI and durable evidence

Use ordinary Git and the existing Actions workflow; no GitHub CLI is needed.
Actions uploads direct-r-logs-<run-id>-<attempt> on success or failure when
possible. Inspect the matching commit, versions.log, stages.tsv, result.txt,
per-stage logs, and raw Dune logs. An early failure leaves later stages
unchecked. No push or workflow dispatch is authorized merely by reading this
guide.

Update STATE.md and DECISIONS.md with actual milestones and exact next
commands. Keep dated raw verification logs unchanged, including their
historical source paths; add new evidence for the current layout instead.
