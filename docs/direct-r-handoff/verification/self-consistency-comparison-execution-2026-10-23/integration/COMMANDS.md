# Root integration: incremental evidence

Working directory: `/Users/akuklev/air/pts-rk`.
No repository `.vo` or cache artifacts were written. Final verification is
the separate fresh integrated audit, not these reused-object checks.

Pinned environment:

```sh
export PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH"
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
```

Exact successful final command (attempt-06, exit 0):

```sh
opam exec -- timeout 300 rocq compile \
  -Q /tmp/pts-rk-dictionaries-fresh.KOCLBv/default/theories PTSrk \
  -Q /tmp/pts-rk-dictionaries-fresh.KOCLBv/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q /tmp/pts-rk-dictionaries-fresh.KOCLBv/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
  -Q /tmp/pts-rk-dictionaries-fresh.KOCLBv/default/theories/CombinatoryLogic-rk PTSrk.Combinatory \
  -Q /tmp/pts-rk-dictionaries-fresh.KOCLBv/default/theories/self_consistency PTSrk.SelfConsistency \
  -Q theories/self_consistency PTSrk.SelfConsistency \
  -Q /tmp/pts-rk-comparison-integration.mga5V1 PTSrk.SelfConsistency \
  -o /tmp/pts-rk-comparison-integration.mga5V1/CodeComparisonRealization.vo \
  theories/self_consistency/CodeComparisonRealization.v \
  > /tmp/pts-rk-comparison-integration.mga5V1/attempt-06.log 2>&1
```

`execution-01.log` records the same command with input/output basename
`CheckerExecution` and that log basename; exit 0. Attempts 03–05 used the
same final loadpaths and respective attempt log, with evolving proof source.
Their first errors, all exit 1:

- 03: unresolved subject placeholder in `quote_zip_typed`;
- 04: unresolved scope parameter in a Boolean-injectivity `change`;
- 05: that proposed Boolean syntax is not convertible. The final proof
  instead reuses `InternalComparisonFolds.point_equiv_injective`.

Earlier setup errors, both exit 1, are preserved in full:

- 01: mapping the whole code-comparison worker directory collided on
  `GuardedTables.vo` with the dependency directory;
- 02: after isolating only the new worker objects, `InternalCarrier.vo`
  was missing. Its coherent worker object was added to the temporary directory.

The exact initial setup wrappers were not retained in a separate command
ledger; their logs are diagnostic evidence, not a reproducible fresh audit.
No incremental timeout occurred. The fresh audit script records every command,
exit status, UTC start/end, source manifest and complete kernel inventory.
