# Add DirectR and GitHub Actions without GitHub CLI

This is a CI add-on to `DirectR_restructured_PR_package.zip`, not a replacement
proof development. It adds `.github/workflows/direct-r.yml`,
`tools/ci-check-direct-r.sh`, and `docs/DirectR-CI.md`. It does not change any `.v`
file or prove Theorem 5. Neither a real Rocq compilation nor a GitHub Actions run
was available when this add-on was prepared.

Local requirements: ordinary Git and the ability to extract ZIP archives. No
GitHub CLI, Python, Rocq, OCaml, opam, or Dune installation is required locally.
GitHub installs the compiler and dependencies on its runner. You need normal
Git authentication for pushing your branch; this workflow needs no custom secrets.

## 1. Fork, clone, and enable Actions

Using GitHub's web interface, fork `TurtlePU/pts-rk` to `akuklev/pts-rk`.
Clone your fork with your ordinary Git client, or:

```sh
git clone https://github.com/akuklev/pts-rk.git
cd pts-rk
```

In your fork, visit Settings > Actions > General. Enable GitHub Actions and allow
`actions/checkout@v6`, `actions/upload-artifact@v7`, and `ocaml/setup-ocaml@v3`
(or retain an existing policy that permits them). Keep the default token
read-only. Leave any "allow GitHub Actions to create/approve pull requests"
option disabled; it is not needed. If the Actions tab displays an enable-workflows
banner, enable workflows before pushing.

## 2. Extract BOTH packages outside the repository

Extract `DirectR_restructured_PR_package.zip` and `DirectR_GitHub_CI.zip`, e.g. in
Downloads. They produce:

- `pts-rk-direct-r-restructured/`
- `pts-rk-direct-r-ci/`

Do not use the older monolithic DirectR packages, and do not run `publish.sh`.
The commands below use `git apply` directly, without its GitHub CLI integration.

## 3. Create a branch at the package's inspected base

From your fork's checkout, set the two absolute package paths:

```sh
PKG="$HOME/Downloads/pts-rk-direct-r-restructured"
CI="$HOME/Downloads/pts-rk-direct-r-ci"

git status --short
git remote -v
```

The status must be empty before proceeding. `origin` must point to your fork.
Keep the archives outside the checkout so they are not accidentally committed.
Do not discard any existing changes to make the checkout clean; use another
checkout when necessary.

```sh
git fetch https://github.com/TurtlePU/pts-rk.git main
git switch -c direct-r-ci 723cf2ec61c737ae82ba33d2e7db44f650122b0e
```

This deliberately uses the base against which the development was prepared,
not an unreviewed newer main. Do not reset or force-push either main branch.
Choose another unused branch name when `direct-r-ci` already exists.

## 4. Apply the development and the CI add-on

Stop if any command fails; do not continue to the commit after an error.

```sh
git apply --check "$PKG/direct-r.patch"
git apply --index "$PKG/direct-r.patch"
git apply --check "$CI/ci.patch"
git apply --index "$CI/ci.patch"

git diff --cached --stat
git diff --cached --check
```

These patches stage the intended files, including the updated explicit module
list in `theories/dune`. No manual Dune edit is needed. When the restructured
development is already applied on your branch, skip its two patch commands and
apply only `ci.patch`; do not create a new base branch over your existing work.

## 5. Commit and push

```sh
git commit -m "Add draft direct R interpretation with Rocq CI"
git push -u origin direct-r-ci
```

Use your existing Git author identity and authentication. GitHub account passwords
cannot authenticate HTTPS Git pushes. Use an existing credential manager, SSH,
or a suitably scoped token. For HTTPS workflow updates, a classic token requires
`workflow` scope as well as repository access; a fine-grained token needs access
to this repository and Contents/Workflows write permissions. Never put the token
in the workflow, remote URL, committed files, or chat.

## 6. Inspect the CI run in the browser

In `akuklev/pts-rk`, open Actions > DirectR / Rocq, then the run for your pushed
commit and the job "Compile PTS-rk and DirectR". A push runs this workflow without
opening a PR and without putting the workflow on main.

The job:

1. Installs the pinned candidate toolchain (below).
2. Builds the unmodified inspected upstream commit in a separate temporary tree.
3. Builds each DirectR module separately, stopping at the first failure.
4. Attempts to upload diagnostics even if dependency installation or compilation
   fails. No `continue-on-error` hides a failing compilation.

In the run's Summary, download the artifact named
`direct-r-logs-<run-id>-<attempt>`. It includes package-installation output,
toolchain versions, a switch export, per-stage logs, and (after builds) a result
and stage table. The concrete-tests stage includes `Print Assumptions` output.
If setup fails before a compiler is installed, compiler-stage files will naturally
be absent; inspect the setup step's web log and any uploaded installation log.
A cancelled job or a workflow-YAML error might not produce an artifact.

Typical diagnosis:

- `toolchain-install.log`: dependency resolution/download/build problem.
- `01-upstream.log`: original repository/toolchain compatibility problem.
- `02-kernel.log` onwards: the first new module that failed compilation.
- `13-examples-and-assumptions.log`: concrete checks and assumptions, only when
  all preceding modules compiled.
- exit 124: the stage resource limit was reached, not proof of untypability.

No run after the push? Enable Actions first, then trigger another push:

```sh
git commit --allow-empty -m "Trigger DirectR CI after enabling Actions"
git push
```

A workflow only on the feature branch may not show a "Run workflow" button:
`workflow_dispatch` requires the workflow file on the default branch. Use the
push trigger or the existing run's Re-run jobs menu instead. Do not merge the
unfinished development solely to obtain a manual-run button.

After editing a failed proof, commit the actual changed files and `git push`
again. Each push triggers another run. Leave failures visible and do not weaken
the proof goal or insert admissions merely to make CI green.

## 7. Create the draft PR on the website

Open `TurtlePU/pts-rk` > Pull requests > New pull request > compare across forks.
Select base `TurtlePU/pts-rk:main`, head fork `akuklev/pts-rk`, compare `direct-r-ci`.
Use the title/body in the original package and add a link to the Actions run.
Choose **Create draft pull request**, not a ready-for-review or merge action.
Update the body's compiler status to describe the observed run accurately.
An upstream maintainer may have to approve execution of the fork's PR workflows;
the push workflow in your own fork is independently available.

## Candidate CI toolchain

- Ubuntu 24.04 runner
- OCaml 4.14.2
- Dune 3.23.1 (upstream declares Dune language 3.23 and Rocq language 0.13)
- `rocq-prover=meta.1` with **`rocq-core=9.1.1`**
- `rocq-stdlib=9.0.0` (Stdlib is versioned separately)
- `rocq-equations=1.3.1+9.1`

These package constraints were checked against published package metadata,
not confirmed by a successful build of DirectR. The first CI run is the real
integration test. This is a version-pinned initial toolchain, not a fully locked
transitive dependency graph; `opam-switch.export` records the resolved versions.
The three actions use their maintained major-version tags.

The baseline/ref, jobs and per-stage timeout are explicit environment variables
in the workflow. The default stage timeout is 1200 seconds and the job limit is
120 minutes. These are safety caps, not expected build times.

## What a green run means

A green run means that all requested files and examples compiled in that run.
It does NOT prove the currently missing uniform `GeneratorTotal`,
`GeneratorSound`, or arbitrary-first-order derivation preservation theorems.
The source still states those as open obligations. This CI adds no nontriviality
or set-model development. See `docs/DirectR-obligations.md`.

## References used to prepare this add-on

- Upstream: https://github.com/TurtlePU/pts-rk/blob/main/dune-project
- Rocq installation: https://rocq-prover.org/docs/using-opam
- Rocq 9.1.1: https://rocq-prover.org/releases/9.1.1
- Dune: https://opam.ocaml.org/packages/dune/dune.3.23.1/
- Stdlib: https://opam.ocaml.org/packages/rocq-stdlib/rocq-stdlib.9.0.0/
- Equations: https://github.com/rocq-prover/opam/blob/master/released/packages/rocq-equations/rocq-equations.1.3.1%2B9.1/opam
- OCaml action: https://github.com/ocaml/setup-ocaml
- Artifact action: https://github.com/actions/upload-artifact
- Repository Actions settings: https://docs.github.com/en/repositories/managing-your-repositorys-settings-and-features/enabling-features-for-your-repository/managing-github-actions-settings-for-a-repository
- Manual runs/default branch: https://docs.github.com/en/actions/how-tos/manage-workflow-runs/manually-run-a-workflow
- Fork PRs: https://docs.github.com/en/pull-requests/how-tos/create-pull-requests/creating-a-pull-request-from-a-fork
