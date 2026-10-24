# SK native-canonical reference check

Source: SKNativeCanonical.agda plus copied current project imports, with
pinned Agda 2.8.0-3d04bac and Cubical v0.9 revision
b150186d2544e7efeddd31e5d14a8b9ecbb100f7. No source pragmas were weakened.

```sh
XDG_DATA_HOME=/tmp/pts-rk-sk-reference.woGuNO/data \
AGDA_DIR=/tmp/pts-rk-sk-reference.woGuNO/config \
/tmp/pts-rk-agda-2.8.0.MvVO53/agda \
  --safe --no-default-libraries --ignore-interfaces \
  -i /tmp/pts-rk-agda-2.8.0.MvVO53/cubical \
  -i /tmp/pts-rk-sk-reference.woGuNO/source \
  /tmp/pts-rk-sk-reference.woGuNO/source/SKNativeCanonical.agda
```

First check: exit 0, no warnings. Full output check.log; copied-source
manifest sources.sha256; timestamps started.txt/finished.txt; exit-code.txt.
The final live-to-copy source comparison passed. No preceding source file
was changed by this task. Full aggregate verification is performed by root.

The output is native annotated syntax, not a binder-free recompiled SK
representative. Source-beta? decides native beta conversion of expansions,
not weak combinatory conversion. Idempotence is native renormalization.
