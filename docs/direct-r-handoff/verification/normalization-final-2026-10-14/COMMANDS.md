# Normalization proof verification — 2026-10-14

Starting/final HEAD: 95450d34bffd4c4d54ddd73d79f0d0d830837276.
Proof changes are uncommitted. Existing changes and user logs/ were preserved.
Rocq 9.2, OCaml 4.14.2, Dune 3.23.1, dedicated pts-rk-ci switch.

All commands ran from the repository root. Environment for direct commands:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

## Incremental compiler evidence

The command template was:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build \
  --display=short --no-buffer theories/NormalizationComplexity/TARGET.vo \
  > /tmp/pts-rk-nc-finalize-N.log 2>&1
```

Each numbered log is copied here unmodified, including failed compilations.
No timeout occurred. Exit codes are compiler command exit codes, not those of
a later log-reading command.

| N | TARGET | Exit | Outcome |
|---|---|---|---|
| 1 | Morphisms | 1 | Missing explicit sort-label parameter |
| 2 | Morphisms | 1 | Rewrite targeted wrong occurrence |
| 3 | Morphisms | 1 | Implicit transpose label parameter |
| 4 | Morphisms | 0 | Typed substitution/renaming compiled |
| 5 | Safety | 1 | Proof variable name collision |
| 6 | Safety | 1 | Induction variable name collision |
| 7 | Safety | 1 | Unspecified well-formed extension rank |
| 8 | Safety | 0 | Structural bound equivalence/renaming compiled |
| 9 | Safety | 1 | Ambiguous context in rank uniqueness |
| 10 | Safety | 0 | Residual substitution bound compiled |
| 11 | Safety | 0 | Context transport compiled |
| 12 | Descent | 1 | Non-lambda case splitting tactic |
| 13 | Descent | 0 | Strict descent and d-pass normality compiled |
| 14 | EstimatorChecks | 1 | Incomplete sort axiom subgoal |
| 15 | EstimatorChecks | 0 | Typed counterexample to old bridge compiled |
| 16 | Audit | 0 | Fixed-rank success/cost theorem audited |
| 17 | SortBounds | 1 | Redundant bullets after arithmetic solved goals |
| 18 | SortBounds | 1 | Redundant induction case |
| 19 | SortBounds | 1 | List/lambda notation conflict |
| 20 | SortBounds | 1 | List/context constructor conflict |
| 21 | SortBounds | 0 | Application-spine value bound compiled |
| 22 | SortBounds | 1 | Context lookup induction instantiation |
| 23 | SortBounds | 1 | Redundant constructor after automation |
| 24 | SortBounds | 0 | Uniform sort-rank/size bound compiled |
| 25 | AutomaticBound | 1 | Existential application argument inference |
| 26 | AutomaticBound | 0 | Semantic automatic bound and linear cost compiled |
| 27 | Audit | 1 | Over-simplification in cost arithmetic |
| 28 | Audit | 1 | Empty-context proof inference |
| 29 | Audit | 1 | Remaining empty-context proof inference |
| 30 | Audit | 0 | All three public results and 87 assumption checks |

## Fresh builds

First fresh build, exit 0:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build \
  --build-dir /tmp/pts-rk-nc-final-fresh.Bm7eZT \
  --display=short --no-buffer theories/NormalizationComplexity/Audit.vo \
  > /tmp/pts-rk-nc-final-fresh.log 2>&1
```

After comment/import cleanup, final fresh build, exit 0:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build \
  --build-dir /tmp/pts-rk-nc-verified.xg8gFn \
  --display=short --no-buffer theories/NormalizationComplexity/Audit.vo \
  > /tmp/pts-rk-nc-verified.log 2>&1
```

Both build directories were newly allocated by `mktemp -d`. Both logs contain
87 closed local Print Assumptions reports and one closed upstream report,
and exact types of the public theorems. No rank/descent/success contract is
an assumption of the automatic normalization theorem.

## CI-equivalent checks

Baseline, exit 0, including separately archived pristine upstream:

```sh
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/normalization-finalize-baseline" \
  bash tools/check-local-ci.sh > /tmp/pts-rk-nc-finalize-baseline.log 2>&1
```

First final CI, exit 0, all 81 stages PASS:

```sh
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/normalization-finalize-final" \
  bash tools/check-local-ci.sh > /tmp/pts-rk-nc-finalize-final-ci.log 2>&1
```

After cleanup, the final rerun exited 0 with all 81 stages PASS:

```sh
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/normalization-verified-final" \
  bash tools/check-local-ci.sh > /tmp/pts-rk-nc-verified-ci.log 2>&1
```

See final-stages.tsv and its archived output for the final result.

## Independent recursive kernel checks

Exit 0, no dependency-admission flags:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o \
  -Q /tmp/pts-rk-nc-final-fresh.Bm7eZT/default/theories PTSrk \
  PTSrk.NormalizationComplexity.Normalization \
  PTSrk.NormalizationComplexity.BoundedNormalization \
  PTSrk.NormalizationComplexity.EstimatorChecks \
  > /tmp/pts-rk-nc-final-kernel-check.log 2>&1
```

Baseline library comparison, exit 0:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o \
  -Q /tmp/pts-rk-nc-final-fresh.Bm7eZT/default/theories PTSrk PTSrk.Ranks \
  > /tmp/pts-rk-nc-upstream-kernel-check.log 2>&1
```

The two context summaries compare byte-for-byte equal (`cmp` exit 0). Both
list the loaded Stdlib declaration functional_extensionality_dep, not used by
any of the 87 closed audited theorems. Neither reports unsafe fixpoints,
type-in-type, rewrite rules or assumed positivity. This distinction is why
the per-theorem transitive Print Assumptions audit is also retained.

The final cleaned build's whole Audit library was additionally checked, exit 0:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o \
  -Q /tmp/pts-rk-nc-verified.xg8gFn/default/theories PTSrk \
  PTSrk.NormalizationComplexity.Audit \
  > /tmp/pts-rk-nc-verified-kernel-check.log 2>&1
```

Its context summary also compares byte-for-byte equal to the upstream check.

Compiler logs are retained verbatim, including their trailing whitespace.
Source/documentation whitespace checks pass; a whole-worktree diff check
also reports that pre-existing/new raw compiler-log whitespace.
