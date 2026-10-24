# SK contextual QIIRT migration check

The source copy was taken after the two changes to Combinatory.agda and
Examples.agda and before any support-module edits (none were needed).

Compiler: Agda 2.8.0-3d04bac. Cubical: pinned v0.9 checkout at
b150186d2544e7efeddd31e5d14a8b9ecbb100f7. Pragmas are `--cubical --safe
--guardedness`; Cubical mode is not supplied globally.

Initial command (exit 0, no warnings):

```sh
XDG_DATA_HOME=/tmp/pts-rk-sk-qiirt.yXkl5I/data \
AGDA_DIR=/tmp/pts-rk-sk-qiirt.yXkl5I/config \
/tmp/pts-rk-agda-2.8.0.MvVO53/agda \
  --safe --no-default-libraries --ignore-interfaces \
  -i /tmp/pts-rk-agda-2.8.0.MvVO53/cubical \
  -i /tmp/pts-rk-sk-qiirt.yXkl5I/source \
  /tmp/pts-rk-sk-qiirt.yXkl5I/source/Examples.agda
```

Output: check.log. Source hashes: sources.sha256. Exit: exit-code.txt.
Start timestamp: started.txt. The initial shell did not record an end time;
the later checks record their own timestamps below.

The new `skk-computes` is a derived equation for explicitly certified S/K
instantiation spines, not a closed-polymorphic identity construction.
There are no new term/path constructors, assumptions, or unsafe flags.

Additional copied-source support checks, each exit 0/no warnings; these use
the fresh initial run's interfaces and do not request `--ignore-interfaces`:

```sh
for qiirt_module in SGuardIrrelevance TargetView Exact; do
  XDG_DATA_HOME=/tmp/pts-rk-sk-qiirt.yXkl5I/data \
  AGDA_DIR=/tmp/pts-rk-sk-qiirt.yXkl5I/config \
  /tmp/pts-rk-agda-2.8.0.MvVO53/agda \
    --safe --no-default-libraries \
    -i /tmp/pts-rk-agda-2.8.0.MvVO53/cubical \
    -i /tmp/pts-rk-sk-qiirt.yXkl5I/source \
    /tmp/pts-rk-sk-qiirt.yXkl5I/source/$qiirt_module.agda
done
```

Per-module logs, exits, started/finished timestamps are retained alongside
this file. Final live-to-copy byte comparisons and scoped `git diff --check`
both passed. No support files changed. No staging or commit was performed.
