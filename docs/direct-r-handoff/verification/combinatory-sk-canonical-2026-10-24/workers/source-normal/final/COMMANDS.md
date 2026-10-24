# Fresh final intrinsic-source normalization check

Agda 2.8.0-3d04bac; Cubical v0.9 commit
b150186d2544e7efeddd31e5d14a8b9ecbb100f7. Copied sources and isolated config,
data, and interfaces. No source pragmas or safety flags weakened.

```sh
XDG_DATA_HOME=/tmp/pts-rk-sk-source-final.yWoN0X/data \
AGDA_DIR=/tmp/pts-rk-sk-source-final.yWoN0X/config \
/tmp/pts-rk-agda-2.8.0.MvVO53/agda \
  --safe --no-default-libraries --ignore-interfaces \
  -i /tmp/pts-rk-agda-2.8.0.MvVO53/cubical \
  -i /tmp/pts-rk-sk-source-final.yWoN0X/source \
  /tmp/pts-rk-sk-source-final.yWoN0X/source/SKSourceNormal.agda
```

PASS, exit 0, zero warnings, 2026-10-24 00:57:30–00:58:01 UTC.
Full log check.log; source manifest sources.sha256; exit and timestamps in
exit-code.txt, started.txt, finished.txt. Final live-to-copy comparisons for
SKSourceEquality.agda and SKSourceNormal.agda pass; scoped diff-check passes.

SKSourceEquality.agda: 146 lines, SHA256
43d6cdf536f3f65156c1993f80e45b2af19992f129ccad5c4eca49dcdb00ddac.
SKSourceNormal.agda: 54 lines, SHA256
7f4f228e3151a1f910311293b6a5ac66e06ff3146100a7f62e902e39ea9597bd.

Development attempts, including the two compiler failures and the successful
incremental attempt, are retained at
/tmp/pts-rk-sk-source-normal.OEpsnr/COMMANDS.md with source snapshots,
hashes, exact commands, logs, exits, and times. No other source file, git
index, or commit was modified by this task.

The source normalization algorithm follows intrinsic rounds commuting with
the original native greedy passes. It needs no partial parser, guessed rank,
new typing relation, eta equation, or assumed termination witness. The
independent Check fibres are used only to prove erasure injectivity, not as
a substitute for original PTS typing. Original typing is supplied by the
separately proved SKSource.erase-typed bridge.
