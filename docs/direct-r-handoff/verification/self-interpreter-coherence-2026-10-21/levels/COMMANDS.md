# Predicative equality levels and joins — 2026-10-21

Source `theories/self_interpreter/IndexedEqualityLevels.v`, SHA256
`726d67825f42a05a97ad200ba99af1f44030d26923ae8d27593add4e8da2bac0`.
Working directory `/Users/akuklev/air/pts-rk`. No existing proof source or
original calculus was changed. Independent paper-agent and audit-agent
mathematical reviews both PASS.

## Contract

For A:U_a define h=max(a+2,d+1), exactly the formation rank of Eq_d(A,u,v).
`lower` and `reverse` eliminate supplied Eq_h evidence using the actual
motives x↦Eq_d(A,u,x) and x↦Eq_d(A,x,u), with independently typed reflexivity
seeds. They construct Eq_d(A,u,v) / Eq_d(A,v,u). `join` combines two
high-level forward witnesses through a common middle using the existing
same-level composition, lowering the first and reversing the second.

Direct original typings, literal substitution equations, and strong literal
reflexivity computation are proved. Normality requires normal inputs and
non-lambda-headed evidence; it is not asserted after arbitrary specialization.
For type laws at U_c the carrier has sort ZERO, so input predicate c+2 gives
reversed evidence at predicate c+1. No cumulativity, same-level symmetry or
source-to-internal-witness compiler is assumed. Raw reflexivity equations
allow arbitrary input h as reduction statements only, not hidden typings.

## Builds

Fresh build `/tmp/pts-rk-equality-levels.S2TruK`; raw artifacts
`_build/equality-levels.DYMmNA`. Each command was
`bash _build/equality-levels.DYMmNA/RUN.sh NN`, whose retained contents are:

```sh
#!/usr/bin/env bash
attempt="$1"
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-equality-levels.S2TruK --display=short --no-buffer theories/self_interpreter/IndexedEqualityLevels.vo > "_build/equality-levels.DYMmNA/attempt-$attempt.log" 2>&1
build_status=$?
printf '%s\n' "$build_status" > "_build/equality-levels.DYMmNA/attempt-$attempt.exit"
tail -n 45 "_build/equality-levels.DYMmNA/attempt-$attempt.log"
exit "$build_status"
```

01 exits 1: all direct typing/substitution proofs passed; a congruence proof
used the wrong name `reduces_to_rename`, corrected to original `rename_rtc`.
02 exits 0 with 10 closed reports. After adding normality and the type-law
specialization, 03 exits 1: `cbn` unfolded Eq before the planned normality
lemma application. Replaced this proof step with explicit syntax unfolding
and the existing normality-under-renaming lemma. 04 exits 0 with all 15
closed reports. No timeout, weakened statement or disabled check.

Recursive kernel command, exit 0 (`kernel.log`, `kernel.exit`):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-equality-levels.S2TruK/default/theories PTSrk -Q /tmp/pts-rk-equality-levels.S2TruK/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-equality-levels.S2TruK/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.IndexedEqualityLevels > _build/equality-levels.DYMmNA/kernel.log 2>&1
status=$?
printf '%s\n' "$status" > _build/equality-levels.DYMmNA/kernel.exit
tail -n 22 _build/equality-levels.DYMmNA/kernel.log
exit "$status"
```

Loaded inventory: only pre-existing upstream functional extensionality;
unsafe fixpoints, type-in-type and assumed positivity empty. This is distinct
from the 15 closed theorem-level reports. Known loadpath warning retained.

Version command, exit 0 (`versions.log`, `versions.exit`):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam list --switch=pts-rk-ci --installed --columns=name,version --short rocq-core rocq-stdlib rocq-equations ocaml dune
```

Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2, Dune 3.23.1.
Final fresh aggregate, pristine comparison and full CI are recorded separately
in `../final-review/COMMANDS.md`.
