# Intrinsic SK source worker verification

Owned only the NEW SKSource.agda. No prior source, build registration,
paper, Git index or commit was changed. Final source is copied under
source/ and hashed in final-source.sha256.

Toolchain: /tmp/pts-rk-agda-2.8.0.MvVO53/agda (Agda 2.8.0-3d04bac),
Cubical v0.9 revision b150186d2544e7efeddd31e5d14a8b9ecbb100f7 under
/tmp/pts-rk-agda-2.8.0.MvVO53/cubical. Every check uses isolated
AGDA_DIR=/tmp/pts-rk-sk-source.caRvqq/config and
XDG_DATA_HOME=/tmp/pts-rk-sk-source.caRvqq/data, and includes source/ plus
the pinned Cubical directory. Commands preserve compiler numeric exits
and UTC timestamps separately, not the status of the tail command.

- check01.log: --safe --no-default-libraries SKSource.agda, exit 0 with
  eight UnsupportedIndexedMatch warnings. They arise in fixed-successor
  context elimination and fixed-arrow type elimination. Those definitions
  were replaced by generic caseVar/FunctionAt eliminators, not suppressed.
- check02.log: same flags, exit 42. The generic relational eliminator had
  underconstrained implicit Ty indices. Making those relation parameters
  explicit resolves the reported metas, without changing theorem targets.
- check03.log: same flags, exit 0, zero warnings.
- final-check.log: --safe --no-default-libraries --ignore-interfaces,
  exit 0, zero warnings. Includes the added executable regressions for
  capture-avoiding substitution under lambda and newly created redexes.

Exact final command:

```sh
AGDA_DIR=/tmp/pts-rk-sk-source.caRvqq/config XDG_DATA_HOME=/tmp/pts-rk-sk-source.caRvqq/data /tmp/pts-rk-agda-2.8.0.MvVO53/agda --safe --no-default-libraries --ignore-interfaces -i /tmp/pts-rk-sk-source.caRvqq/source -i /tmp/pts-rk-agda-2.8.0.MvVO53/cubical /tmp/pts-rk-sk-source.caRvqq/source/SKSource.agda
```

Final source stability and whitespace checks pass. Unsafe-pragma/postulate
scan has no matches. The final module has 261 lines. Source typings remain
intrinsic simple typings; erase-typed targets NativeTyping.Typ, the original
six-rule annotated system. Context wellformedness is proved. Exact erasure
commutation covers renaming, substitution, the native bottom-up pass and
every number of passes. Passes are total structural computations, not a
postulated normalizer; the automatic native rank budget is supplied by the
separate source-normalization wrapper.
