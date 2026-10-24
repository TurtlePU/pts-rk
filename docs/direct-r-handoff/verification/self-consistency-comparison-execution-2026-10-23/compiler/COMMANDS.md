# Native checker comparison compiler: isolated checks, 2026-10-23

The only owned repository edit is the new
`theories/self_consistency/CheckerComparisons.v`. All 18 public endpoints
are proved without acceptance, normalization, typing, or rejection premises.
The six native typing-rule checks, equality/context checks and both raw
checkers compile to actual conjunctions with complete comparison operands.
Parsing, context lookup, endpoint extraction and substitution remain external.

Environment:

```sh
export PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH"
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
```

The prior coherent replacement build supplies unchanged imported objects.
This focused isolated check is not a fresh integrated or full repository CI
run. Compiler: pinned Rocq 9.2 with OCaml 4.14.2.

## Compilation history

Before each attempt the source was copied with:

```sh
cp theories/self_consistency/CheckerComparisons.v /tmp/pts-rk-checker-comparisons.bAGHxQ/CheckerComparisons.v
```

Attempt 01 exited 1 in 0.068327 seconds: the finite-fragment focused build
did not include InternalCarrier.vo. Its exact command was:

```sh
opam exec -- rocq c \
  -Q /tmp/pts-rk-fragments-fresh.d7RHpo/default/theories PTSrk \
  -Q /tmp/pts-rk-fragments-fresh.d7RHpo/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q /tmp/pts-rk-fragments-fresh.d7RHpo/default/theories/self_consistency PTSrk.SelfConsistency \
  -Q /tmp/pts-rk-checker-comparisons.bAGHxQ PTSrk.SelfConsistency \
  /tmp/pts-rk-checker-comparisons.bAGHxQ/CheckerComparisons.v \
  > /tmp/pts-rk-checker-comparisons.bAGHxQ/attempt-01.log 2>&1
```

Attempts 02–04 used this command, with the corresponding numbered log:

```sh
opam exec -- rocq c \
  -Q /tmp/pts-rk-replacement-fresh.87Hwa9/default/theories PTSrk \
  -Q /tmp/pts-rk-replacement-fresh.87Hwa9/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q /tmp/pts-rk-replacement-fresh.87Hwa9/default/theories/self_consistency PTSrk.SelfConsistency \
  -Q /tmp/pts-rk-checker-comparisons.bAGHxQ PTSrk.SelfConsistency \
  /tmp/pts-rk-checker-comparisons.bAGHxQ/CheckerComparisons.v \
  > /tmp/pts-rk-checker-comparisons.bAGHxQ/attempt-04.log 2>&1
```

- Attempt 02: exit 1, 0.145513667 seconds. An encoded sort in the context
  clause needed its explicit scope. The clause now binds the original
  ExtendContext scope and passes it to that sort constructor.
- Attempt 03: exit 0, 0.14296825 seconds. All 18 endpoints compile.
- Attempt 04: exit 0. Final comment-only clarification that comparison/node
  counts are not runtime or operand-size bounds. Combined final compilation
  and fresh report command took 0.516751083 seconds.

## Fresh assumption reports and recursive kernel check

`Report.v` explicitly prints assumptions of all 18 endpoints. Command:

```sh
opam exec -- rocq c \
  -Q /tmp/pts-rk-replacement-fresh.87Hwa9/default/theories PTSrk \
  -Q /tmp/pts-rk-replacement-fresh.87Hwa9/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q /tmp/pts-rk-replacement-fresh.87Hwa9/default/theories/self_consistency PTSrk.SelfConsistency \
  -Q /tmp/pts-rk-checker-comparisons.bAGHxQ PTSrk.SelfConsistency \
  /tmp/pts-rk-checker-comparisons.bAGHxQ/Report.v \
  > /tmp/pts-rk-checker-comparisons.bAGHxQ/report.log 2>&1
```

Exit 0: exactly 18 reports closed under the global context.

```sh
opam exec -- rocq check -silent -o -bytecode-compiler yes \
  -Q /tmp/pts-rk-replacement-fresh.87Hwa9/default/theories PTSrk \
  -Q /tmp/pts-rk-replacement-fresh.87Hwa9/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q /tmp/pts-rk-replacement-fresh.87Hwa9/default/theories/self_consistency PTSrk.SelfConsistency \
  -Q /tmp/pts-rk-checker-comparisons.bAGHxQ PTSrk.SelfConsistency \
  PTSrk.SelfConsistency.CheckerComparisons \
  > /tmp/pts-rk-checker-comparisons.bAGHxQ/kernel.log 2>&1
```

Exit 0, 19.239523917 seconds. Complete recursive dependency checking, no
admission/skip flags. Inventory: only inherited functional_extensionality_dep;
no type-in-type, unsafe fixes or assumed positivity. Inventory comparison
against a fresh pristine build is left to the root's integrated audit.

Final log last-write times (not inferred start/completion times):
attempt-04 09:32:28 UTC; report 09:32:29 UTC; kernel 09:33:04 UTC.

Source checks, all exit 0:

```sh
cmp theories/self_consistency/CheckerComparisons.v /tmp/pts-rk-checker-comparisons.bAGHxQ/CheckerComparisons.v
git diff --check -- theories/self_consistency/CheckerComparisons.v
shasum -a 256 theories/self_consistency/CheckerComparisons.v /tmp/pts-rk-checker-comparisons.bAGHxQ/CheckerComparisons.v
```

Both final source hashes:
`b4c5d3e265c58d96a60c52c32d2c4ce29ce96ba6e0a3207d700bac8858330acf`.

Archive this ledger, logs and source/report files, not generated objects.
No changes to existing proofs, Dune, docs, original rules, index, or commits.
