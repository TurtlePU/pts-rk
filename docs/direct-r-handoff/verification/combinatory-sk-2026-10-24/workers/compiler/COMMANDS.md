# SK compiler worker: commands and verification limitations

This record was written after the worker runs, on 2026-10-24. It records
commands actually sent through the execution tool and observations from the
retained logs; it is not a reconstructed timestamped audit. The root agent's
separate fresh full-closure/pristine audit supersedes these iterative checks.

## Scope and final source

The worker changed only the new
`theories/CombinatoryLogic-rk/SK.v`. Root managed Dune registration and removal
of the preceding basis modules. Final source: 473 lines; SHA256
`0577cef46bab3cc7c13baa2c2f33a32c50e5ebf77cda9713b030d14375d12f93`.
The final source was frozen before the root audit. The worker did not stage,
commit, push, modify other proof sources, or run the root audit itself.

Intermediate source snapshots were NOT retained. Therefore a failed run's
exact source cannot be reconstructed from this directory alone. Temporary
unfinished proof scripts, including an `Abort` during initial development,
were replaced by completed proofs before the final build. Final source
searches found no `Admitted`, `admit`, `Axiom`, `Parameter`, or `Abort`.

## Working directory and toolchain

All build commands ran with repository working directory
`/Users/akuklev/air/pts-rk`, using the following explicit environment and
executable prefix:

```sh
OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam \
OPAMSWITCH=pts-rk-ci \
/Users/akuklev/.local/share/pts-rk-ci/bin/opam exec --
```

Versions re-observed after the runs, at approximately
2026-10-24T00:38:03Z: Rocq core 9.2.0 (CLI reports 9.2), OCaml 4.14.2,
Dune 3.23.1, rocq-stdlib 9.1.0, rocq-equations 1.3.2+9.2. Exact queries:

```sh
OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci /Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- rocq --version
OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci /Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- dune --version
OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci /Users/akuklev/.local/share/pts-rk-ci/bin/opam list --installed --columns=name,version rocq-core rocq-equations rocq-stdlib coq-equations coq-stdlib dune ocaml-base-compiler
```

## Actual build commands

The scratch directory was allocated using:

```sh
mktemp -d /tmp/pts-rk-sk-worker.XXXXXX
```

The result was `/tmp/pts-rk-sk-worker.IuJaUA`.

First exploratory check used existing repository dependency objects:

```sh
OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci /Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- rocq c -Q _build/default/theories PTSrk -o /tmp/pts-rk-sk-worker.IuJaUA/SK.vo theories/CombinatoryLogic-rk/SK.v > /tmp/pts-rk-sk-worker.IuJaUA/compile01.log 2>&1; tail -30 /tmp/pts-rk-sk-worker.IuJaUA/compile01.log
```

For each two-digit `NN` from `02` through `20`, the following literal command
template was issued with `NN` and `TAIL` substituted according to the table.
This notation specifies the commands; no loop was used in those invocations.

```sh
OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci /Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- dune build --build-dir /tmp/pts-rk-sk-worker.IuJaUA/build theories/CombinatoryLogic-rk/SK.vo > /tmp/pts-rk-sk-worker.IuJaUA/compileNN.log 2>&1; tail -TAIL /tmp/pts-rk-sk-worker.IuJaUA/compileNN.log
```

The absolute Dune build directory was fresh at run 02, then reused for the
worker's incremental proof development. It was not a fresh directory per
attempt. Root is running a separate final fresh audit.

| Run | TAIL | Observed result in retained log |
| --- | ---: | --- |
| 01 | 30 | Failure: congruence relation inference (`RTC` versus indexed `R`); direct invocation also emitted absolute-name masking warning. |
| 02 | 30 | Failure: congruence inference (`Term nat ?n` versus `nat`). Dependencies built in the fresh Dune directory. |
| 03 | 25 | Failure: destruct-generated name `v` unavailable. |
| 04 | 25 | Failure: lambda congruence relation inference (`RTC` versus indexed `R`). |
| 05 | 18 | Failure: proposed intermediate native term not definitionally convertible. |
| 06 | 40 | Same conversion failure, with `Show` diagnostic goal retained. |
| 07 | 18 | Same conversion failure after initial simplification change. |
| 08 | 25 | Failure: induction hypothesis not generalized/applied correctly in `replace_variables`. |
| 09 | 18 | Failure: remaining application case in `replace_variables`. |
| 10 | 20 | Failure: replacement rewrite did not match the incompletely simplified environment. |
| 11 | 20 | Same replacement-rewrite failure. |
| 12 | 40 | Same failure with `Show` diagnostic identifying the residual `eq_rect`. |
| 13 | 20 | Intermediate success: bracket abstraction proof completed; no compiler or arithmetic endpoints yet. |
| 14 | 30 | Failure: native source expansion match did not transport the indexed variable family. |
| 15 | 25 | Intermediate success: dependent return clause fixed source expansion; compiler/conversion results completed. |
| 16 | 25 | Intermediate success: 16 closed endpoint assumption reports, including initial arithmetic. |
| 17 | 25 | Intermediate success: 18 closed reports, adding numeral native expansion and normality. |
| 18 | 30 | Failure: implicit variable family `V` could not be inferred in `extend_env_typed`. |
| 19 | 30 | Failure: implicit binder type `A` could not be inferred in `extend_env_typed`. |
| 20 | 30 | Final targeted success: 23 closed endpoint assumption reports, final source typing and arithmetic computation theorems. |

Runs 13, 15, 16 and 17 succeeded on intermediate sources; it would be
incorrect to label every run before 20 a failure. Dune runs retain the
existing `Interpretation_of_R` logical-loadpath remapping warning. No warning
was disabled. Final run 20 has 23 `Closed under the global context` lines
and no error diagnostic.

### Exit-code and timestamp limitation

Each command above ends with `; tail ...`. Consequently the execution
tool's observed outer-shell exit code 0 is the exit code of `tail`, NOT an
independently captured compiler/Dune exit code. The worker did not save
the underlying numeric exit statuses. Failures are identified by their
explicit compiler diagnostics; successful incremental builds by completed
objects and absence of errors, with final assumption reports. Do not report
these as independently recorded Dune `exit 0` observations.

Exact per-run start/end UTC timestamps were not captured. Log modification
times exist but are not substituted for execution timestamps here. No
worker command timed out or was terminated. Asynchronous tool sessions
were polled until completion for runs 02, 16, 17 and 20.

## Arithmetic size query

`Counts.v` was created with `apply_patch` and contains two `Eval vm_compute`
queries of the final definitions' atom counts, over the empty variable
family. First command failed because the nonphysical library-directory
mapping was omitted:

```sh
OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci /Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- rocq c -Q /tmp/pts-rk-sk-worker.IuJaUA/build/default/theories PTSrk /tmp/pts-rk-sk-worker.IuJaUA/Counts.v > /tmp/pts-rk-sk-worker.IuJaUA/counts.log 2>&1; tail -15 /tmp/pts-rk-sk-worker.IuJaUA/counts.log
```

The corrected command produced `414 : nat` and `81 : nat` in `counts02.log`:

```sh
OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci /Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- rocq c -Q /tmp/pts-rk-sk-worker.IuJaUA/build/default/theories PTSrk -Q /tmp/pts-rk-sk-worker.IuJaUA/build/default/theories/CombinatoryLogic-rk PTSrk.Combinatory /tmp/pts-rk-sk-worker.IuJaUA/Counts.v > /tmp/pts-rk-sk-worker.IuJaUA/counts02.log 2>&1; tail -15 /tmp/pts-rk-sk-worker.IuJaUA/counts02.log
```

The same outer-shell exit-status limitation applies. The final source
proves these counts for arbitrary variable families with `reflexivity`;
the query output alone is not used as evidence of that general theorem.

## Final scope and remaining obligations

The final source proves actual deterministic SK bracket compilation of
intrinsically simply typed source syntax, its literal annotated original-PTS
typing and forward beta correctness, conversion preservation/reflection,
and equality of native normal source expansions. Numeral atom counts,
rank claims, full native Church-normal expansion, normality, and applied
successor/addition/multiplication computation are proved.

It does NOT supply a full dependent PTS compiler, a parser/reifier of
arbitrary native normal terms back to the intrinsic source, a total
canonical-SK-output operation, or structural equality of hidden-indexed SK
codes from native beta equality. No such target theorem is assumed.

The worker did NOT run pristine comparison, recursive kernel checking, full
repository CI, Agda checking, or note compilation. Those belong to root's
separate verification. Root reported a fresh full audit underway at
`/tmp/pts-rk-sk-audit.puvKDx`; this record makes no claim about its outcome.
