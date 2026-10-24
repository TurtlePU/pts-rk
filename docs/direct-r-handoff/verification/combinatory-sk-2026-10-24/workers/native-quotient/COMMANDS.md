# SK native-canonical reference and quotient check

Source: SKNativeCanonical.agda plus copied current project imports. Compiler
Agda 2.8.0-3d04bac; Cubical v0.9 revision
b150186d2544e7efeddd31e5d14a8b9ecbb100f7. No flags or pragmas weakened.

```sh
XDG_DATA_HOME=/tmp/pts-rk-sk-native-quotient.tZUhv0/data \
AGDA_DIR=/tmp/pts-rk-sk-native-quotient.tZUhv0/config \
/tmp/pts-rk-agda-2.8.0.MvVO53/agda \
  --safe --no-default-libraries --ignore-interfaces \
  -i /tmp/pts-rk-agda-2.8.0.MvVO53/cubical \
  -i /tmp/pts-rk-sk-native-quotient.tZUhv0/source \
  /tmp/pts-rk-sk-native-quotient.tZUhv0/source/SKNativeCanonical.agda
```

Result: exit 0, zero warnings. Complete output: check.log; copied-source
hashes: sources.sha256; times: started.txt/finished.txt; exit: exit-code.txt.
Final live-to-copy source comparison and scoped git diff --check pass.
No prior source file, index, or commit was modified by this subtask.

The preceding 84-line reference-only check also passed, without failures:
/tmp/pts-rk-sk-reference.woGuNO/COMMANDS.md. This final module adds an actual
set quotient by native beta conversion of annotated expansions. Its
normalization map is injective and supplies decidable quotient equality;
quotient application respects the original native beta congruence.

Outputs still contain native binders/annotations. Neither a canonical SK
reifier nor completeness for arbitrary dependent PTS terms is claimed.
