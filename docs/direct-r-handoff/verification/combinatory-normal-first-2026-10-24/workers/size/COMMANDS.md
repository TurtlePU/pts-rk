# SK compiler output-size evidence

Worker: `/root/sk_canonical`. Worktree: `/Users/akuklev/air/pts-rk`.
Scope: new `theories/CombinatoryLogic-rk/agda/SKBracketSize.agda` only.
No existing source, native rule, Rocq module, index entry, or commit changed.

## Toolchain and exact commands

Pinned Agda `/tmp/pts-rk-agda-2.8.0.MvVO53/agda`, reported version
`2.8.0-3d04bac`; Cubical include
`/tmp/pts-rk-agda-2.8.0.MvVO53/cubical`, revision
`b150186d2544e7efeddd31e5d14a8b9ecbb100f7`.

Iterative invocation for each NN was:

```sh
bash /tmp/pts-rk-sksize.flfBIE/check.sh NN
```

The retained `check.sh` copies development sources, snapshots the owned file
in `snapshots/NN/`, sets `XDG_DATA_HOME=/tmp/pts-rk-sksize.flfBIE/data` and
`AGDA_DIR=/tmp/pts-rk-sksize.flfBIE/config`, and executes exactly:

```sh
/tmp/pts-rk-agda-2.8.0.MvVO53/agda --safe --no-default-libraries -i /tmp/pts-rk-agda-2.8.0.MvVO53/cubical -i /tmp/pts-rk-sksize.flfBIE/source /tmp/pts-rk-sksize.flfBIE/source/SKBracketSize.agda
```

The source OPTIONS specify `--cubical --safe --guardedness`. Each expanded
command, raw log, numeric underlying compiler exit, and actual UTC timestamp
is saved as `command-NN.txt`, `check-NN.log`, `exit-NN.txt`, `start-NN.txt`,
and `end-NN.txt`. Compiler exits were captured before printing log tails and
returned unchanged by the driver.

## Iterative checks

All times are UTC, 2026-10-24.

| Attempt | Start | End | Exit | Result |
| --- | --- | --- | --- | --- |
| 01 | 01:37:19 | 01:37:34 | 42 | Incorrect named argument to arithmetic solver macro |
| 02 | 01:37:46 | 01:37:48 | 42 | Unresolved intermediate exponent indices |
| 03 | 01:38:03 | 01:38:05 | 42 | Unresolved upper endpoint before arithmetic reflection |
| 04 | 01:38:14 | 01:38:16 | 42 | Solver cannot directly reflect opaque exponent subexpression |
| 05 | 01:38:29 | 01:38:32 | 42 | Unresolved factor index in multiplication monotonicity |
| 06 | 01:38:42 | 01:38:44 | 0 | Full module passes, zero warnings |

The fixes expose explicitly typed arithmetic helper equalities, factor the
polynomial inequality away from exponentiation, and specify the factor 4.
No mathematical premise or claim was weakened to obtain a passing check.
No compiler timeout or resource termination occurred in this task.

## Fresh check

Invocation:

```sh
bash /tmp/pts-rk-sksize.flfBIE/fresh.sh
```

The retained `fresh.sh` copies all development sources to `fresh/source`,
sets `XDG_DATA_HOME=/tmp/pts-rk-sksize.flfBIE/fresh/data` and
`AGDA_DIR=/tmp/pts-rk-sksize.flfBIE/fresh/config`, records version/revision
and the source hash, and invokes:

```sh
/tmp/pts-rk-agda-2.8.0.MvVO53/agda --safe --no-default-libraries --ignore-interfaces -i /tmp/pts-rk-agda-2.8.0.MvVO53/cubical -i /tmp/pts-rk-sksize.flfBIE/fresh/source /tmp/pts-rk-sksize.flfBIE/fresh/source/SKBracketSize.agda
```

Fresh evidence is retained in `fresh/command.txt`, `fresh/check.log`,
`fresh/start.txt`, `fresh/end.txt`, `fresh/exit-code.txt`, `fresh/version.txt`,
`fresh/cubical-commit.txt`, `fresh/sources.sha256`, and `fresh/stability.txt`.

Fresh check passed with exit 0 and zero warnings, from
`2026-10-24T01:39:08Z` to `2026-10-24T01:39:43Z`. The owned source hash
remained unchanged before and after this check.

## Proved scope

134-line module, SHA256:

```text
a826dc967e19409f30703b578353098c98feb524b43184c7812b1cb809e518ca SKBracketSize.agda
```

- `bracket-bound`: `suc (open-atoms (bracket p)) ≤ 4 · open-atoms p`.
- `compile-bound`: `atoms (compile s) ≤ 4 ^ source-nodes s`.
- `source-native-nodes`: intrinsic source constructor count is at most
  the node count of its original annotated erasure.
- `normalized-source-bound`: source normalization has constructor count
  at most `tower (SN.budget s) (nodes (erase s))`, composing exact
  source-round erasure with the existing raw normalization size theorem.
- `canonical-output-bound`: canonical SK output has at most
  `4 ^ tower (SN.budget (expand-source t)) (nodes (native-expand t))` atoms.

The output count assigns one to each S, K or ground-label occurrence and
adds across application. Open variables similarly count as one for the
bracket lemma. Type-index payloads, label bit lengths, proof objects,
compiler intermediates and runtime are explicitly excluded. This is a
simply typed SK output bound, not a dependent compiler or a machine memory
bound. All numerical proofs use the existing natural-number representation;
none creates additional original PTS inhabitants.

Root owns aggregate registration, documentation and durable handoff. The
paper excerpt marker is `BEGINSKCANONICALSIZE` / `ENDSKCANONICALSIZE`.
