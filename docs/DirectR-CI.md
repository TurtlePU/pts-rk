# DirectR continuous integration

`.github/workflows/direct-r.yml` installs Rocq on a GitHub-hosted Ubuntu runner
and invokes `tools/ci-check-direct-r.sh`. No local Rocq or GitHub CLI is required
to submit a branch. The workflow uses `push` and `pull_request`, not
`pull_request_target`, with read-only repository permissions and no custom secrets.

## Toolchain

The pinned configuration is OCaml 4.14.2, Dune 3.23.1,
`rocq-prover=meta.1`, `rocq-core=9.2.0`, `rocq-stdlib=9.1.0`, and
`rocq-equations=1.3.2+9.2`. Published package constraints admit this combination.
Rocq 9.2 is required because the pristine upstream `Syntax.v` uses
`Create Rewrite HintDb`, introduced in
[Rocq 9.2](https://rocq-prover.org/doc/V9.2.0/refman/changes.html).
Run `38328517931`, attempt 1, installed the previous Rocq 9.1.1 toolchain
successfully but failed parsing that command during `01-upstream`; no DirectR
modules were checked. The updated toolchain still needs a full compilation run.
The pristine upstream build distinguishes base/toolchain failures from failures
in the new modules. `rocq-prover` is a metapackage: pin `rocq-core` and the
separately versioned Stdlib instead.

The actions use maintained major-version tags. Transitive opam dependencies are
resolved from the configured repositories and recorded in `opam-switch.export`.
This is not a fully locked dependency graph.

## Build and diagnostics

The driver first archives commit
`723cf2ec61c737ae82ba33d2e7db44f650122b0e` into a separate directory and builds
`theories/Ranks.vo` there, using that commit's original Dune file. It then compiles
the new modules one at a time. The final `DirectRTests.vo` compilation contains
the source's `Print Assumptions` commands.

A stage failure stops the sequence and remains a failing job. A stage timing out
is a resource-limit result, not a typing rejection. The runner attempts to upload
`direct-r-logs-<run-id>-<attempt>` after failure as well as success. Ordinary logs
and version data are uploaded, not the whole opam switch or credentials.

Inspect Actions > DirectR / Rocq > the commit's run. The artifact contains:

- installation output and `versions.log`;
- `opam-switch.export` with resolved packages;
- `stages.tsv` and `result.txt` when the driver ran;
- one log for each attempted compilation stage;
- Dune's raw build logs when present.

For a workflow only on a feature branch, push triggers work without a main-branch
merge. The manual "Run workflow" button needs the workflow on the default branch;
use a new push or the run's "Re-run jobs" menu instead. Fork PR workflow execution
in the upstream may need maintainer approval; the fork's own push run is separate.

## Interpretation of results

A green run validates the existing scripts and examples, not missing statements.
`GeneratorTotal`, `GeneratorSound`, and first-order deduction preservation are
still open in the development. Do not report Theorem 5 as complete just because
these files compile. Do not hide compilation errors with `continue-on-error`,
axioms or admissions. No set model or answer-type nontriviality proof is added.
