# Build, logs, and recovery packages

## Inspect first; do not destroy current work

From the real repository root inspect `git status --short`, `git branch --show-current`,
`git log -5 --oneline`, the actual module files and build configuration. Record
commit and local changes in STATE.md. Preserve any user changes. The historical
base is a reference, not authorization to reset the checkout.

Record available versions with `command -v rocq coqc dune opam ocamlc`, and
appropriate version commands; the new local environment may differ from the
ChatGPT container that had no compiler. Inspect actual CI logs when available.
Never put remote URLs containing credentials or secret environment values in logs.

## Latest development already installed

Check for `theories/DirectRObligations.v` and the other split modules. Do NOT
reapply the archive on top of them. Use the checked-out files as active code;
archives are frozen provenance/recovery copies.

In a working Rocq/Equations environment, useful targeted commands are:

```sh
dune build theories/DirectRKernel.vo
dune build theories/DirectREval.vo
dune build theories/DirectRCheck.vo
dune build theories/DirectR.vo
dune build theories/DirectRArithmetic.vo theories/DirectRTests.vo
```

`bash tools/check-direct-r.sh` is a smaller staged runner. Its first target
`theories/Ranks.vo` is in the patched working tree, NOT an isolated baseline.
Prefer the pristine baseline in the CI driver when diagnosing toolchain issues.
The small runner uses `rocq --version`; if the installed Rocq does not support
that spelling, correct the diagnostic to its supported spelling (`rocq -v` in
the supplied CI driver), rather than misreporting it as a proof failure.

The CI add-on's Linux/opam driver is invoked as:

```sh
opam exec -- bash tools/ci-check-direct-r.sh
```

It requires GNU `timeout` and is designed for the Linux GitHub runner. Do not
assume it runs unchanged on macOS. It archives the pristine upstream commit
into a separate temporary directory and builds that before the contribution.
It then builds each module separately, stopping with the actual failing status.
Inspect the script before invoking it; select the local runner or targeted
commands if the tool dependencies are absent.

The current CI/local toolchain is OCaml 4.14.2, Dune 3.23.1,
rocq-prover meta.1, rocq-core 9.2.0, rocq-stdlib 9.1.0, and
rocq-equations 1.3.2+9.2. Stdlib has an independent version. The earlier
9.1.1 candidate cannot parse the upstream `Create Rewrite HintDb` command.
The current toolchain has built pristine upstream and the infrastructure,
structural, and foundations modules locally. The latest CI-repair continuation
also obtained a fresh full development build and a successful complete local
CI driver run, after keeping generated test witnesses compact in Ltac. See
STATE.md and verification/ci-repaired-full-2026-10-13.log. This does not mean the
unfinished functional Theorem 7 has been proved or that remote CI has passed.
`bash tools/check-local-ci.sh` selects the installed native ARM switch and
runs actionlint plus the same staged driver using the available GNU timeout.
See STATE.md for exact commands, logs, and the remaining proof bottleneck.

## Development not installed

`inputs/DirectR_restructured_PR_package.zip` contains the latest modular draft.
`inputs/DirectR_GitHub_CI.zip` adds ONLY workflow, driver, and CI instructions.
Do not use older monolithic packages. Do not run `publish.sh`: it requires gh.

Extract these to a temporary directory outside the checkout. Inspect the patch,
source base, and local changes. If the base differs, review/adapt the patch; do
not reset the branch. On the documented unmodified base, the patch sequence is:

```sh
git apply --check /path/to/pts-rk-direct-r-restructured/direct-r.patch
git apply /path/to/pts-rk-direct-r-restructured/direct-r.patch
git apply --check /path/to/pts-rk-direct-r-ci/ci.patch
git apply /path/to/pts-rk-direct-r-ci/ci.patch
```

Do not apply both the aggregate patch and its three constituent patches.
Do not use the package's clean-checkout helper after adding local handoff files
without inspecting its checks: those docs make the worktree nonempty. Raw
`git apply --check` checks the patch paths without erasing unrelated files.
Installation of THIS handoff does not apply any development/CI patch.

## CI without gh

The user can commit and push with ordinary Git and open the fork's Actions tab.
Download the `direct-r-logs-<run-id>-<attempt>` artifact in the browser and extract
it to `docs/direct-r-handoff/logs/<run-id>/` locally. That logs directory is
ignored by the handoff's .gitignore. Preserve the commit SHA in STATE.md and
check the logs correspond to the code being repaired.

Important logs: toolchain-install.log, versions.log, 01-upstream.log,
02-kernel.log onward, stages.tsv, result.txt, and the final assumptions log
when its stage was reached. A failed earlier stage means later modules were
NOT checked. The workflow's timeout caps are not proofs of untypability.

No push, workflow dispatch, or PR publication is authorized merely by reading
this file. Ask when remote actions are needed unless separately authorized.
Do not disable approvals/sandboxing or grant write workflow tokens to get a build.

## Completion and assumption checks

Rebuild the changed files (cached output is not a fresh assumption report).
Audit the actual PUBLIC all-index theorem and FOL-soundness result with
Print Assumptions. Record the exact type, names, commit and output. An upstream
logical assumption, if any, must be distinguished from a NEW assumption that
postulates the interpretation. Do not call the development axiom-free without
checking the transitive report.

A green build currently proves only the theorems actually present. Definitions
of unproved contracts can compile. The final CI must require an unconditional
Theorem5Target (or equivalent), all ground-faithfulness statements, and
first-order deduction preservation before calling Theorem 5 completed.
