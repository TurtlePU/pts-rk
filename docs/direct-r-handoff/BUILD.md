# Build, logs, and recovery

Latest self-interpreter milestone: full-PTS open-context normalization,
hereditary typed substitution and canonical contexts/type indices. Original
kernel, normalization sources and frozen ZFC remain unchanged. Fresh prior
audit: 326 closed reports; recursive/pristine checks and all 226 current-root
CI stages pass. The object-language dependent PHOAS step remains open.
See [canonical proof checkpoint](verification/self-interpreter-canonical-2026-10-20/COMMANDS.md)
and [scoped publication](verification/self-interpreter-canonical-publish-2026-10-20/COMMANDS.md).

Publication verification: merge 64864e36b4d748cf117f830cdc4438d4d4054a2f,
confirmed on origin/main, passes the complete clean 172-stage local CI plus
actionlint. A separate fresh absolute self-interpreter build prints 264 closed
assumption reports; recursive kernel checks, byte-identical pristine-core
inventory comparison, frozen-library comparisons and source-hash checks pass.
No failed or timed-out stage, no weakened check and no remote CI claim.
Commands, versions, timestamps and current-versus-historical PDF hashes:
[publication checkpoint](verification/self-interpreter-publish-2026-10-20/COMMANDS.md).
Raw logs remain local in /tmp/pts-rk-self-publication.KX9EQK; the fresh build is
/tmp/pts-rk-self-publication-build.GMOcrx. The source merge was published by the
parent; this later evidence/handoff update awaits its separate evidence commit.

Latest self-interpreter checkpoint: finite closed indexed PHOAS for independent
Church-STLC, with normal syntax-injective quotes and an actual closed strong
decoder indexed by budget AND full simple type. No semantic payload is
precomputed. Genuinely dependent local handlers and a limited shared-map
conversion obstruction are also checked; full dependent indexed PHOAS remains
open, not ruled out. The original development worktree's fresh aggregate audit
has 264 closed reports; recursive kernel, pristine core comparison and frozen
ZFC/original-core checks pass. Its actionlint and 226-stage CI passed, including
unrelated unpublished stages. The isolated publication instead contains the
171 committed baseline stages plus the self-interpreter audit; its successful
separate 172-stage verification is recorded in the publication checkpoint above.
Updated note/PDF: 18 pages. Exact commands, failures, versions, hashes and limits:
[finite PHOAS checkpoint](verification/self-interpreter-phoas-2026-10-20/COMMANDS.md).
Historical raw-log paths refer to locally retained evidence, not additional
committed source files. Concise reports and selected provenance are published.

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
- theories/self_interpreter/: faithful raw HOAS, full-PTS weak interpretation,
  finite closed indexed STLC PHOAS with strong unquotation, genuinely dependent
  local handlers and precise obstructions; full dependent interpretation open.

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
dune build @theories/self_interpreter/audit
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
