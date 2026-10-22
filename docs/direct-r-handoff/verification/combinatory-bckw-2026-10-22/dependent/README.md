# BCKW type-scheme tests

Run with Agda 2.8.0-3d04bac:

```sh
AGDA_BIN=/tmp/pts-rk-agda-2.8.0.MvVO53/agda \
  bash docs/direct-r-handoff/verification/combinatory-bckw-2026-10-22/dependent/CHECK.sh
```

The script copies the four modules to a fresh temporary directory, isolates
configuration/data, checks with `--safe --ignore-interfaces`, and records exact
commands, hashes and exit codes. Only Agda builtins are imported. It expects
the positive module to exit 0 and the three negative modules to exit 42 with
the specific dependent-metavariable scope error, not an arbitrary failure.

Fresh archived-fixture run: exit 0, logs
`/tmp/pts-rk-bckw-dependent-check.3s6E48`; recorded exits are respectively
0, 42, 42 and 42, all as expected. Source hashes are stable.
The earlier successful run `.0hNLWP` predates timestamp logging; both have
the same source hashes and outcomes.

`BCKWPositive` proves both literal formulas `B (B W) (B B C)` and
`B (B (B W) C) (B B)` at all simple types and checks their saturated beta
equations definitionally. Natural dependent-result schemes for B, C and W
also check, as does dependent evaluation through C.

`BCKWNegative` tests the first literal formula against the genuinely dependent
substitution type. The other two negatives test both formulas with the
dependent-result schemes. Both reject an attempted domain `D x` because `x`
is not in scope where that domain is chosen.

These are bounded type-scheme experiments, **not** a nondefinability theorem
or an original-PTS/QIIRT adequacy proof. They do not exclude an explicit
polymorphic translation computing family arguments, or a contextual/resource
presentation with its own compiler theorem. Structural substitution
composition/weakening/diagonal do not by themselves provide that compiler.

Initial scratch experiments are retained in
`/tmp/pts-rk-bckw-dependent.OWBz5l/RESULTS.md`. A first positive run used an
absent configuration directory (then reran in the created isolated directory);
initial negative runs had module-name collisions (fixed by selective imports).
Only subsequent `*-typing.log`/`*-final.log` errors were mathematical tests.
An additional codomain-only negative experiment remains in that scratch
directory. No repository production source was changed by these tests.
