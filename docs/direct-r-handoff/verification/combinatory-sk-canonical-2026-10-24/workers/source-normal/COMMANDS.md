# Source erasure injection and intrinsic normalization

Pinned Agda 2.8.0-3d04bac, Cubical v0.9 revision
b150186d2544e7efeddd31e5d14a8b9ecbb100f7. All sources use
`--cubical --safe --guardedness`. No proof premise or safety option weakened.

For attempt 1:

```sh
XDG_DATA_HOME=/tmp/pts-rk-sk-source-normal.OEpsnr/data \
AGDA_DIR=/tmp/pts-rk-sk-source-normal.OEpsnr/config \
/tmp/pts-rk-agda-2.8.0.MvVO53/agda \
  --safe --no-default-libraries --ignore-interfaces \
  -i /tmp/pts-rk-agda-2.8.0.MvVO53/cubical \
  -i /tmp/pts-rk-sk-source-normal.OEpsnr/source \
  /tmp/pts-rk-sk-source-normal.OEpsnr/source/SKSourceNormal.agda
```

Attempts 2 and 3 used the same command without `--ignore-interfaces` after
copying the revised SKSourceEquality.agda into the isolated source directory.
SKSourceNormal.agda and its other copied imports were unchanged.

1. Exit 42: `variable` is an Agda reserved word, so it cannot name a View
   constructor. Renamed that constructor and all its uses to `slot`.
   Initial log/times/exit are check.log, started.txt, finished.txt,
   exit-code.txt. Snapshot attempt1-SKSourceEquality.agda was reconstructed
   after its copy was overwritten; its SHA256 exactly matches sources.sha256.
2. Exit 42: two `substRefl` calls omitted their explicit value argument.
   Snapshot attempt2-SKSourceEquality.agda and attempt2-* logs/hashes/times.
3. Exit 0, zero warnings: both new modules checked. Snapshot
   attempt3-SKSourceEquality.agda and attempt3-* logs/hashes/times retained.

The independently recursive Check relation is auxiliary proof infrastructure
for injectivity of erasure, not a replacement native typing rule. Native
normalization lifts through the proved erase-rounds equation and uses no
parser or termination premise. Source indices stay intrinsic throughout.

Final clean import-closure check runs separately in
/tmp/pts-rk-sk-source-final.yWoN0X. Its exit and timestamps are recorded there.
No staging or commit was performed.
