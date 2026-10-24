# PTS-rk continuous integration

## Direct consistency certificates (23 October 2026)

The current finite-fragment continuation has a separate fresh focused
[audit](direct-r-handoff/verification/self-consistency-finite-fragments-2026-10-23/AUDIT.sh):
95 new public endpoints, full recursive checking of the complete new closure,
and pristine inventory equality pass, 08:23:08–08:24:10 UTC. The full audit
imports this new coverage; `@theories/self_consistency/finite-fragment-audit`
is the focused build alias. It proves a rank-four internal rejection schema
for every external complete-certificate size bound, not one internal
all-budget theorem. The library now imports the improved combinatory and
normalization libraries directly. Exact commands and limitations are in the
[verification record](direct-r-handoff/verification/self-consistency-finite-fragments-2026-10-23/COMMANDS.md).
The following 495-report figures describe the earlier replacement checkpoint,
whose proof sources are unchanged; the whole staged CI has not been rerun.

Stage `01-self-consistency` builds `@theories/self_consistency/audit`.
The library `PTSrk.SelfConsistency` uses the original kernel, Stdlib,
Equations and the shared assembler/native checker, not either arithmetic
interpretation. Its [focused audit](direct-r-handoff/verification/self-consistency-replacement-2026-10-23/AUDIT.sh)
rebuilds 495 public reports. The current staged fresh build passes in 3205 seconds,
and 495/495 reports are closed, with identical before/build source hashes.
Complete new dependency-closure checking passes in 2550 seconds over
explicitly source-mapped coherent isolated objects, with the supported VM
flag, exact pristine inventory equality and stable before/after source hashes.
All final snapshot/original-source checks pass. The redundant fresh-object
check was deliberately stopped afterward (exit 143), not reported as passed.
The previous
426-report checkpoint passed complete recursive checking with supported
`-bytecode-compiler yes` in 875 seconds, with exact pristine inventory equality
(inherited functional_extensionality_dep only, no unsafe entries).
The previous seven-module closure
also passes with that backend and exact pristine inventory equality; its earlier
VM-disabled 2400-second timeout remains recorded, not relabelled a pass.
Every requested proof body is checked; no module admission/skip flags are used.
The 27 unchanged older proof
sources retain their [full previous audit](direct-r-handoff/verification/self-consistency-relational-2026-10-23/COMMANDS.md):
283 closed reports, recursive checking in 1809 seconds and exact pristine
inventory equality (unchanged functional_extensionality_dep only, no unsafe
entries). The continuation audit does not repeat that entire older closure
and is not full repository CI. The linked one-shot script is syntax-checked;
the [verification record](direct-r-handoff/verification/self-consistency-replacement-2026-10-23/COMMANDS.md)
documents the actual separately executed stages and earlier interruptions.
Coverage includes external certificate adequacy, faithful
serialization, scope checking, source-rank compression, and actual original-PTS
carrier/generation/guarded finite-table witnesses. The complete closed-leaf
fragment with labels at most 1 has an internal guarded rejection pilot.
Fixed-rank resource lookup/prefix/extension now have actual PTS closure,
joining and generation witnesses, with executable standard-lookup realization.
Stratified path composition, exact beta correspondence with path concatenation,
executable higher-rank witnesses and internal root/leaf separation are
kernel-checked. The new modules add stratified constructor-case elimination,
fixed-rank histories with executable standard coverage, structural capacity
and finite-family budgets. The numerical bounds remain external, and the
full-functionality target has only been formed, not inhabited. Consumer
preservation, concrete occurrence safety, shape/fill forward simulations and
their standard original-PTS realizations now have witnesses. Global lookup
functionality/matching inversion are optional open lemmas, not mandatory
gates. Native annotated substitution now has exact Syntax agreement and scope
preservation. Independent internal binary/scope relations have all-standard
witnesses; fixed-environment renaming has an actual rank-17 output-scope term.
Standard shift now has exact original-PTS realization, including raw decoder
endpoints and application of the internal scope theorem. An independent
single-substitution environment has a proved local bound and standard witnesses.
Binder-lifted term lookup and full annotated internal replacement now have
fixed-rank output-scope folds and exact standard substitution realization.
Dependent invariants, conversion transport, operation sufficiency, admission
and all-budget soundness remain open. The precise same-index motive obstruction
does not rule out the rank-feasible whole-history/closure-machine alternatives.
All 38 prior proof modules and common infrastructure are unchanged.
The complete staged CI driver has not been rerun at this checkpoint.

## Combinatory Hilbert development (22 October 2026)

Stage `01-combinatory` builds `@theories/CombinatoryLogic-rk/audit`, retaining
the Rocq namespace `PTSrk.Combinatory` after the physical directory rename.
It covers the indexed core, finite-basis obstruction, the P/I/K/S catalogues,
independent Hilbert calculus and the equivalent 66/65-shape instances. No existing
stage is removed. A separate [fresh focused audit](direct-r-handoff/verification/combinatory-gat-2026-10-22/AUDIT.sh)
regenerates assumption reports and compares recursive kernel inventories
against freshly built pristine upstream. See the development's
[evidence](../theories/CombinatoryLogic-rk/EVIDENCE.md) for actual runs;
successful soundness/extraction checks do not prove full completeness.

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
Historically, run `38328517931`, attempt 1, installed the Rocq 9.1.1 toolchain
successfully but failed parsing that command during `01-upstream`; no DirectR
modules were checked. Rocq 9.2.0 has since passed the complete local staged build.
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
the new modules one at a time, including normalization, both arithmetic
interpretations, and the set model. Public audit modules and theorem sources
contain `Print Assumptions` commands. Filesystem targets now live under
`theories/`; the Rocq import namespaces are unchanged.

A stage failure stops the sequence and remains a failing job. A stage timing out
is a resource-limit result, not a typing rejection. The runner attempts to upload
`direct-r-logs-<run-id>-<attempt>` after failure as well as success. Ordinary logs
and version data are uploaded, not the whole opam switch or credentials.

Inspect Actions > DirectR / Rocq > the commit's run. The legacy workflow/job
names are retained for compatibility; coverage includes all developments.
The artifact contains:

- installation output and `versions.log`;
- `opam-switch.export` with resolved packages;
- `stages.tsv` and `result.txt` when the driver ran;
- one log for each attempted compilation stage;
- Dune's raw build logs when present.

For a workflow only on a feature branch, push triggers work without a main-branch
merge. The manual "Run workflow" button needs the workflow on the default branch;
use a new push or the run's "Re-run jobs" menu instead. Fork PR workflow execution
in the upstream may need maintainer approval; the fork's own push run is separate.

## Local checks

`bash tools/check-local-ci.sh` validates the workflow with actionlint and runs
the same staged compilation driver used by Actions, including the isolated
upstream build and the final assumption report. This checks the workflow
expressions and build stages on the host OS; it does not emulate Ubuntu or the
checkout, OCaml setup, and artifact-upload actions.

The dedicated local environment lives in
`${XDG_DATA_HOME:-$HOME/.local/share}/pts-rk-ci`. It contains `bin/opam`,
`bin/actionlint`, and an opam root with a `pts-rk-ci` switch. It does not require
shell profile changes. GNU `timeout` must also be on PATH (on macOS, install
Homebrew `coreutils`). Logs are written to the ignored `_build/local-ci-logs`
directory. Set `DIRECT_R_LOCAL_HOME`, `DIRECT_R_LOCAL_SWITCH`, or
`DIRECT_R_LOG_DIR` to override these defaults.

To recreate the switch after installing opam, actionlint, and GMP:

```sh
export PATH="${XDG_DATA_HOME:-$HOME/.local/share}/pts-rk-ci/bin:$PATH"
export OPAMROOT="${XDG_DATA_HOME:-$HOME/.local/share}/pts-rk-ci/opam"
opam init --bare --no-setup --yes default https://opam.ocaml.org
opam switch create pts-rk-ci ocaml-base-compiler.4.14.2 --yes --jobs=2
opam repository add --switch=pts-rk-ci rocq-released https://rocq-prover.org/opam/released --yes
opam install --switch=pts-rk-ci --yes --jobs=2 \
  dune.3.23.1 rocq-prover.meta.1 rocq-core.9.2.0 \
  rocq-stdlib.9.1.0 rocq-equations.1.3.2+9.2
bash tools/check-local-ci.sh
```

On Apple Silicon, GMP must match the OCaml compiler's architecture. An Intel
Homebrew GMP installation cannot be linked into a native ARM compiler switch.
For a separately installed native GMP, set `PKG_CONFIG_PATH` to its
`lib/pkgconfig` directory while installing the opam packages.

Earlier 2026-10-13 partial builds and timeouts remain recorded in the handoff.
They are historical evidence, not the current theorem status. The
2026-10-14 pre-reorganization baseline and post-move local CI both passed
actionlint and all 171 stages. A separate fresh full build, public-interface
audit, and recursive kernel checks also passed. See
[STATE.md](direct-r-handoff/STATE.md) for exact dated commands/logs.
Cached success does not rerun assumption output;
use a new absolute Dune `--build-dir` for a fresh audit.

## Interpretation of results

A green run validates the statements actually supplied, with their explicit
premises. Theorem 4, Theorem 7, independent first-order deduction preservation,
and effective `Kernel.Theorem5Target` witnesses are proved and audited. Legacy
optional bounded-generator contracts are separate, not prerequisites.

Original set-model soundness is proved under explicit supplied hierarchy,
classical, cardinal, and choice parameters; its material BZC reduction remains
open. Normalization bounds have an explicit encoding/operation-cost model.
The STLC reduction is checked, but its cited external hardness theorem and
machine-level TOWER-completeness are not formalized. See the relevant
[source-folder READMEs](../theories/README.md). Never hide compiler failures
with `continue-on-error`, axioms, admissions, or reduced CI coverage.
