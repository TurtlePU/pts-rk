# Quotient-free computed-type canonical algebra

Final verification uses Agda 2.8.0-3d04bac and Cubical v0.9 commit
b150186d2544e7efeddd31e5d14a8b9ecbb100f7. Sources were copied into this
directory; configuration and Agda data are isolated. The final command
rechecks every imported interface. No source safety flags were weakened.

```sh
AGDA_DIR=/tmp/pts-rk-canonical-algebra.pAIEvR/config \
XDG_DATA_HOME=/tmp/pts-rk-canonical-algebra.pAIEvR/data \
/tmp/pts-rk-agda-2.8.0.MvVO53/agda \
  --safe --ignore-interfaces --no-default-libraries \
  -i /tmp/pts-rk-canonical-algebra.pAIEvR/source \
  -i /tmp/pts-rk-agda-2.8.0.MvVO53/cubical \
  /tmp/pts-rk-canonical-algebra.pAIEvR/source/CanonicalAlgebra.agda
```

PASS: exit 0, zero warnings. Exact timestamps are final2-started.txt and
final2-finished.txt; full log final2.log; exit final2-exit.txt. Source-copy
comparison passes, with final-source-stability-exit.txt and
final-source.sha256 recording the checked source. The source has 82 lines
and SHA256 34e723adbf6eace6955ba30dc6dfff2bb6efb163d145cea17fa010486a0d69d7.

Retained development evidence:

- attempt1-CanonicalAlgebra.agda, check.log, exit-code.txt: exit 42, parse
  error from the reserved word syntax; renamed the declaration code.
- attempt2-CanonicalAlgebra.agda, attempt2.log and associated times/exit:
  exit 42, unresolved family metavariables for substRefl; supplied the
  explicit family C.Canonical.
- attempt3-CanonicalAlgebra.agda, attempt3.log and associated times/exit:
  exit 0, zero warnings, 01:28:16–01:28:18 UTC.
- final.log and associated times/exit: exit 42 because --no-libraries
  prevented the Cubical library's flags from loading. Replaced that flag
  by --no-default-libraries in the final successful command above; no
  source changes were made for this tool-configuration correction.

The new algebra uses ordinary Sigma types, not a claimed dependent IIRT.
It supplies computed type fibres, their proved isomorphism with existing
canonical SK codes, normalized application and its typing/agreement law,
decidable fibre equality, actual SK normal-form recovery and native PTS
typing. Normalization reuses SKCanonical and its intrinsic typed lambda
intermediate; direct binder-free evaluation, dependent PTS coverage,
simultaneous hereditary-substitution termination, and complexity bounds
are not claimed. No existing source, index, or commit was modified.
