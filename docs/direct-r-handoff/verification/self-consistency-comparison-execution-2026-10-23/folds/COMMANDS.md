# Fixed comparison-expression folds — isolated verification

Only repository source written: theories/self_consistency/InternalComparisonFolds.v.
SHA256: 920350accac8ad9d9d7a65fdf9ac04ac300025cdb3ab7f033765340e5ac5f07d.

Environment for all commands:

```sh
export PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH"
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
```

## Compiler iterations

Attempts 01–03 compiled the independent fixed evaluator core, before adding
the CheckerComparisons-based generic quotation:

```sh
opam exec -- rocq compile -Q /tmp/pts-rk-dictionaries-fresh.KOCLBv/default/theories PTSrk -Q /tmp/pts-rk-dictionaries-fresh.KOCLBv/default/theories/Interpretation_of_R Interpretation_of_R -Q /tmp/pts-rk-dictionaries-fresh.KOCLBv/default/theories/self_consistency PTSrk.SelfConsistency -Q /tmp/pts-rk-comparison-folds.e00aQK PTSrk.SelfConsistency -o /tmp/pts-rk-comparison-folds.e00aQK/InternalComparisonFolds.vo theories/self_consistency/InternalComparisonFolds.v
```

- Attempt 01 exits 1: that focused prior build had no GuardedTables object.
- Dependency compilation below exits 0.
- Attempt 02 exits 1: a redundant lift_closed_zero rewrite after the existing
  structural substitution tactic had already consumed that redex.
- Attempt 03 exits 0: all fixed-core typing and open beta schemata compile.

Dependency command, captured in dependencies.log:

```sh
opam exec -- dune build --build-dir /tmp/pts-rk-dictionaries-fresh.KOCLBv --display=short --no-buffer -j 2 theories/self_consistency/GuardedTables.vo
```

After adding generic quotation over CheckerComparisons.Expr, attempts 04–05
used the same coherent earlier closure as that new dependency:

```sh
opam exec -- rocq compile -Q /tmp/pts-rk-replacement-fresh.87Hwa9/default/theories PTSrk -Q /tmp/pts-rk-replacement-fresh.87Hwa9/default/theories/Interpretation_of_R Interpretation_of_R -Q /tmp/pts-rk-replacement-fresh.87Hwa9/default/theories/self_consistency PTSrk.SelfConsistency -Q /tmp/pts-rk-checker-comparisons.bAGHxQ PTSrk.SelfConsistency -Q /tmp/pts-rk-comparison-folds.e00aQK PTSrk.SelfConsistency -o /tmp/pts-rk-comparison-folds.e00aQK/InternalComparisonFolds.vo theories/self_consistency/InternalComparisonFolds.v
```

- Attempt 04 exits 1: ordinary destruct generalized away the fixed initial
  endpoint of a reduction; inversion preserves that endpoint.
- Attempt 05 exits 0: complete final module, measured approximately 0.25s.

Every attempt redirects output to its matching attempt-NN.log; the shell
captures the result, prints the final 65 lines, and exits with that result.
All failures remain preserved. No timeout or proof-checking bypass was used.

## Reports and complete kernel check

```sh
opam exec -- rocq compile -Q /tmp/pts-rk-replacement-fresh.87Hwa9/default/theories PTSrk -Q /tmp/pts-rk-replacement-fresh.87Hwa9/default/theories/Interpretation_of_R Interpretation_of_R -Q /tmp/pts-rk-replacement-fresh.87Hwa9/default/theories/self_consistency PTSrk.SelfConsistency -Q /tmp/pts-rk-checker-comparisons.bAGHxQ PTSrk.SelfConsistency -Q /tmp/pts-rk-comparison-folds.e00aQK PTSrk.SelfConsistency /tmp/pts-rk-comparison-folds.e00aQK/Report.v
opam exec -- rocq check -silent -o -bytecode-compiler yes -Q /tmp/pts-rk-replacement-fresh.87Hwa9/default/theories PTSrk -Q /tmp/pts-rk-replacement-fresh.87Hwa9/default/theories/Interpretation_of_R Interpretation_of_R -Q /tmp/pts-rk-replacement-fresh.87Hwa9/default/theories/self_consistency PTSrk.SelfConsistency -Q /tmp/pts-rk-checker-comparisons.bAGHxQ PTSrk.SelfConsistency -Q /tmp/pts-rk-comparison-folds.e00aQK PTSrk.SelfConsistency PTSrk.SelfConsistency.InternalComparisonFolds
```

Both exits explicitly captured as 0. report.log contains exactly 24 closed
reports. kernel.log checks the entire recursive closure with no module-admission
or recursive-skip flags. Its complete inventory equals the previous fresh
pristine inventory: only inherited functional_extensionality_dep, no unsafe
entries. Exact comparison:

```sh
diff -u docs/direct-r-handoff/verification/self-consistency-finite-dictionaries-2026-10-23/audit-final/pristine-inventory.txt <(sed -n '/^CONTEXT SUMMARY/,$p' /tmp/pts-rk-comparison-folds.e00aQK/kernel.log)
```

The comparison and tracked/untracked source whitespace checks pass. No full
fresh integrated audit, full repository CI, commit, staging, push or cleanup
is claimed here. Archive this ledger, report source and logs, not .vo caches.
