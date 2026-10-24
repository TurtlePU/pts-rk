# Finite dictionary realization — isolated checks, 2026-10-23

Only the new repository source `theories/self_consistency/FiniteDictionaryRealization.v`
was edited. This directory contains isolated copies, proof objects, and logs;
archive the source/report/logs, not generated proof objects.

Environment used for every compilation/check:

```sh
export PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH"
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
```

Checked versions: Rocq 9.2, compiled with OCaml 4.14.2; Dune 3.23.1.
Dependency objects are from the already audited finite-fragment closure
and the concurrently built new dictionary module, not copied into repository
sources. This isolated check is not the later fresh integrated audit.

## Compilation

Before attempts 01–11 the current source was copied using:

```sh
cp theories/self_consistency/FiniteDictionaryRealization.v /tmp/pts-rk-dictionary-realization.KorrfC/FiniteDictionaryRealization.v
```

Attempts 01–11 each ran this command with the matching numbered log:

```sh
opam exec -- rocq c \
  -Q /tmp/pts-rk-fragments-fresh.d7RHpo/default/theories PTSrk \
  -Q /tmp/pts-rk-fragments-fresh.d7RHpo/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q /tmp/pts-rk-finite-dictionaries.KMlC6m PTSrk.SelfConsistency \
  /tmp/pts-rk-dictionary-realization.KorrfC/FiniteDictionaryRealization.v \
  > /tmp/pts-rk-dictionary-realization.KorrfC/attempt-NN.log 2>&1
```

Those attempts omitted the new source directory's logical mapping. Thus
successful attempts 09 and 11 established their respective source proofs,
but produced a root-namespaced object; they are not the final importable
library build. No proof or checking option was weakened to fix this.

| Attempt | Result | First error or correction |
| --- | --- | --- |
| 01 | nonzero | Substitution tactic did not unfold native variable helpers before rewriting. |
| 02 | nonzero | Original Syntax list-notation conflict; imported Syntax without its notations. |
| 03–05 | nonzero | Rewriting `nth` failed because its explicit type argument was `closed_term` in the goal and expanded `Term nat 0` in the lemma instance. |
| 06 | nonzero | Diagnostic `change` was not convertible; propositional equality was still required. |
| 07–08 | nonzero | Continued `nth` diagnostic, including fully printed terms. |
| 09 | 0 | Initial list/Fill/All/membership realization compiled after explicitly matching the `closed_term` argument. |
| 10 | nonzero | New telescope beta proof lacked imported transitivity instances. |
| 11 | 0 | All 24 endpoints compiled after importing AbstractRewriting, approximately 2.9 seconds. |
| 12 | 0 | Exact final source, correct library namespace, approximately 2.9 seconds. |

Final compile (attempt 12):

```sh
opam exec -- rocq c \
  -Q /tmp/pts-rk-fragments-fresh.d7RHpo/default/theories PTSrk \
  -Q /tmp/pts-rk-fragments-fresh.d7RHpo/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q /tmp/pts-rk-finite-dictionaries.KMlC6m PTSrk.SelfConsistency \
  -Q /tmp/pts-rk-dictionary-realization.KorrfC PTSrk.SelfConsistency \
  /tmp/pts-rk-dictionary-realization.KorrfC/FiniteDictionaryRealization.v \
  > /tmp/pts-rk-dictionary-realization.KorrfC/attempt-12.log 2>&1
```

## Fresh reports and complete kernel check

`Report.v` explicitly prints assumptions for all 24 declarations, including
the application lemmas and both open beta schemata. Exact command:

```sh
opam exec -- rocq c \
  -Q /tmp/pts-rk-fragments-fresh.d7RHpo/default/theories PTSrk \
  -Q /tmp/pts-rk-fragments-fresh.d7RHpo/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q /tmp/pts-rk-finite-dictionaries.KMlC6m PTSrk.SelfConsistency \
  -Q /tmp/pts-rk-dictionary-realization.KorrfC PTSrk.SelfConsistency \
  /tmp/pts-rk-dictionary-realization.KorrfC/Report.v \
  > /tmp/pts-rk-dictionary-realization.KorrfC/report.log 2>&1
```

Exit 0, approximately 0.6 seconds; exactly 24 closed reports.

Complete recursive check, with no admission/skip flags:

```sh
opam exec -- rocq check -silent -o -bytecode-compiler yes \
  -Q /tmp/pts-rk-fragments-fresh.d7RHpo/default/theories PTSrk \
  -Q /tmp/pts-rk-fragments-fresh.d7RHpo/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q /tmp/pts-rk-finite-dictionaries.KMlC6m PTSrk.SelfConsistency \
  -Q /tmp/pts-rk-dictionary-realization.KorrfC PTSrk.SelfConsistency \
  PTSrk.SelfConsistency.FiniteDictionaryRealization \
  > /tmp/pts-rk-dictionary-realization.KorrfC/kernel-02.log 2>&1
```

Exit 0, measured 11.910105291 seconds. Complete context inventory contains
only inherited `functional_extensionality_dep`, with no unsafe entries.
The earlier identical check wrote `kernel.log`, but its asynchronous tool
session ID was not retained, so its exit was not independently captured;
the explicit successful second run is the verification evidence.

Log last-write times (not inferred start/completion times): attempt-12
08:57:01 UTC; report 08:57:25 UTC; kernel-02 08:58:25 UTC.

Source equality and whitespace checks both exit 0:

```sh
cmp theories/self_consistency/FiniteDictionaryRealization.v /tmp/pts-rk-dictionary-realization.KorrfC/FiniteDictionaryRealization.v
git diff --check -- theories/self_consistency/FiniteDictionaryRealization.v
shasum -a 256 theories/self_consistency/FiniteDictionaryRealization.v /tmp/pts-rk-dictionary-realization.KorrfC/FiniteDictionaryRealization.v
```

Both source hashes:
`767899547b16ae5aa857b8ac825aadd482647d2728baac0f3321c3513ca7ecc8`.

No edit to earlier proofs, Dune, documentation, or original typing rules;
no staging, commit, push, cleanup, or full repository CI run.
