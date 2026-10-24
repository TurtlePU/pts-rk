# Safe Agda SK bracket compiler worker

Only the new project module `SKBracket.agda` was edited by this worker.
`SKSource.agda` was concurrently developed by the source-syntax worker.
No Rocq source, existing Agda module, aggregate import, documentation source,
Git index, commit or remote was changed here.

Final source: 264 lines; SHA256
`f8c30552fca14936c0750e4958a93e5c7186b76f4fe5eb6fcca73757bc655c89`.

## Commands and preserved evidence

The working directory was `/Users/akuklev/air/pts-rk`. Scratch allocation:

```sh
mktemp -d /tmp/pts-rk-skbracket.XXXXXX
```

It returned `/tmp/pts-rk-skbracket.Cjke1Y`. Both checked drivers, `check.sh`
and `fresh.sh`, were written using `apply_patch` and are retained here.
The exact commands issued were:

```sh
bash /tmp/pts-rk-skbracket.Cjke1Y/check.sh 01
bash /tmp/pts-rk-skbracket.Cjke1Y/check.sh 02
bash /tmp/pts-rk-skbracket.Cjke1Y/check.sh 03
bash /tmp/pts-rk-skbracket.Cjke1Y/check.sh 04
bash /tmp/pts-rk-skbracket.Cjke1Y/check.sh 05
bash /tmp/pts-rk-skbracket.Cjke1Y/check.sh 06
bash /tmp/pts-rk-skbracket.Cjke1Y/check.sh 07
bash /tmp/pts-rk-skbracket.Cjke1Y/fresh.sh
```

Each invocation saves the exact expanded compiler command, raw log, start
and end UTC timestamps, and numeric compiler exit status. The driver saves
the status BEFORE displaying a log tail and exits with that saved status.
For each numbered attempt, `snapshots/NN` preserves the actual SKBracket
source and, if it existed, SKSource as copied for that attempt. Other
unchanged project dependencies were copied into the isolated source area;
they were not separately versioned per attempt. The final fresh check
retains its complete copied source directory and source hash stability check.

## Toolchain and isolation

Compiler: `/tmp/pts-rk-agda-2.8.0.MvVO53/agda`, version
`Agda version 2.8.0-3d04bac`.
Cubical library: `/tmp/pts-rk-agda-2.8.0.MvVO53/cubical`, pinned revision
`b150186d2544e7efeddd31e5d14a8b9ecbb100f7`.
Source pragmas are `--cubical --safe --guardedness`.
No checks or warnings are disabled.

The numbered checks use copied project sources and isolated AGDA_DIR and
XDG_DATA_HOME. They reuse interfaces between attempts. They invoke:

```sh
/tmp/pts-rk-agda-2.8.0.MvVO53/agda --safe --no-default-libraries -i /tmp/pts-rk-agda-2.8.0.MvVO53/cubical -i /tmp/pts-rk-skbracket.Cjke1Y/source /tmp/pts-rk-skbracket.Cjke1Y/source/SKBracket.agda
```

The final check creates a distinct source/config/data area and adds
`--ignore-interfaces`:

```sh
/tmp/pts-rk-agda-2.8.0.MvVO53/agda --safe --no-default-libraries --ignore-interfaces -i /tmp/pts-rk-agda-2.8.0.MvVO53/cubical -i /tmp/pts-rk-skbracket.Cjke1Y/fresh/source /tmp/pts-rk-skbracket.Cjke1Y/fresh/source/SKBracket.agda
```

The actual environment and full command are also retained in the driver and
`fresh/command.txt`; compiler and Cubical versions are recorded under fresh.

## Attempt outcomes

| Attempt | Start UTC | End UTC | Exit | Observation |
| --- | --- | --- | ---: | --- |
| 01 | 2026-10-24T00:48:56Z | 2026-10-24T00:49:01Z | 0 | Native S/K head and application reductions compile; no source compiler yet. |
| 02 | 2026-10-24T00:50:59Z | 2026-10-24T00:50:59Z | 42 | Parse failure: `variable` is reserved, renamed constructor to `cv`. |
| 03 | 2026-10-24T00:51:06Z | 2026-10-24T00:51:06Z | 42 | Parse failure: `abstract` is reserved, renamed function to `bracket`. |
| 04 | 2026-10-24T00:51:15Z | 2026-10-24T00:51:17Z | 42 | Four UnsupportedIndexedMatch warnings and mismatch between extension environments. Replaced fixed-context variable matching by SKSource.caseVar/caseVar-rel; native environments became scoped finite substitutions. |
| 05 | 2026-10-24T00:52:45Z | 2026-10-24T00:52:47Z | 42 | Unsolved type-index metas: native expansion cannot infer hidden simple types. Fixed with explicit S/K instances and unindexed native environment helpers. No warning suppression. |
| 06 | 2026-10-24T00:53:28Z | 2026-10-24T00:53:29Z | 0 | Open bracket applied and unapplied recovery proved; zero warnings. |
| 07 | 2026-10-24T00:54:05Z | 2026-10-24T00:54:06Z | 0 | Final closed compiler and expansion bridge complete; zero warnings. |

Final fresh check: exit 0, zero warnings; exact start/end timestamps are in
`fresh/start.txt` and `fresh/end.txt`. It checks the import closure of
SKBracket, NOT the whole project aggregate. Root performs the final full
aggregate check separately. No run timed out or was interrupted.

## Proved API and scope

`compile-open` deterministically removes every intrinsic source lambda using
only typed open S/K application. `compile-open-correct` is forward ORIGINAL
annotated native beta reduction under arbitrary scoped substitution.
`compile : Source ε A → BinderFreeCore.Tm A` returns literal existing
binder-free codes, with no new primitive atom for a source term.
`compile-steps` recovers the source's literal native erasure by forward beta;
`compile-typed` uses the original Typ judgment at precisely `decode A`.
`expand-source` and `erase-expand` provide an intrinsic source for every
existing closed SK code and literal agreement with its native expansion.

No eta equation, normalization premise, reification premise, postulate,
unsafe pragma, or termination/positivity exemption is used. This module is
the compiler component, not by itself a native normalizer, canonical-image
theorem, weak-normal output proof, or full dependent PTS compiler. Those
separate integration steps belong to the root and the other workers.
