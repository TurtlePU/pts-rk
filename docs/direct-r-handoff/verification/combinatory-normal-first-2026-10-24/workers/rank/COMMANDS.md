# SK source rank budget and canonical computation evidence

Worker: `/root/sk_canonical`. Worktree: `/Users/akuklev/air/pts-rk`.
All times below are recorded UTC on 2026-10-24. No commits were made.

## Toolchain and isolation

- Agda executable: `/tmp/pts-rk-agda-2.8.0.MvVO53/agda`.
- Reported version: `Agda version 2.8.0-3d04bac`.
- Cubical include: `/tmp/pts-rk-agda-2.8.0.MvVO53/cubical`.
- Cubical revision: `b150186d2544e7efeddd31e5d14a8b9ecbb100f7`.
- Each checker command uses `--safe --no-default-libraries`; the source
  OPTIONS set `--cubical --safe --guardedness`.
- Iterative checks set `XDG_DATA_HOME=/tmp/pts-rk-skfast.TSEzs7/data`
  and `AGDA_DIR=/tmp/pts-rk-skfast.TSEzs7/config`, and copy the development's
  Agda sources to `/tmp/pts-rk-skfast.TSEzs7/source`.
- Fresh checks use separate `data`, `config`, and `source` directories
  underneath `fresh` and `consolidated`, respectively. Both pass
  `--ignore-interfaces` and retain their complete copied sources.
- The actual version and revision outputs are saved in each fresh directory.

The executable shell drivers `check.sh`, `fresh.sh`, and
`fresh-consolidated.sh` record exact expanded checker commands, timestamps,
and numeric checker exits before returning that same status. The iterative
driver was expanded before check04 to snapshot the three consolidated files
in addition to the two draft adapters. Earlier raw command files and raw logs
were not rewritten.

## Recorded checks

| Invocation | Target | Start | End | Exit |
| --- | --- | --- | --- | --- |
| `bash /tmp/pts-rk-skfast.TSEzs7/check.sh 01 SKSourceFast` | Draft source adapter | 01:24:50 | 01:25:03 | 0 |
| `bash /tmp/pts-rk-skfast.TSEzs7/check.sh 02 SKFastCanonical` | Draft canonical adapter | 01:25:52 | 01:25:57 | 0 |
| `bash /tmp/pts-rk-skfast.TSEzs7/check.sh 03 SKFastCanonical` | Expanded draft regressions | 01:26:45 | 01:26:48 | 0 |
| `bash /tmp/pts-rk-skfast.TSEzs7/fresh.sh` | Fresh draft canonical adapter | 01:27:10 | 01:27:45 | 0 |
| `bash /tmp/pts-rk-skfast.TSEzs7/check.sh 04 SKCanonicalExamples` | Consolidated public API | 01:32:22 | 01:32:24 | 0 |
| `bash /tmp/pts-rk-skfast.TSEzs7/fresh-consolidated.sh` | Fresh consolidated public API | 01:32:54 | 01:33:32 | 0 |

All six checker runs completed without warnings. There were no failed or
timed-out compiler invocations in this worker's current task. A subsequent
diagnostic `rg` for warning/error text returned 1 because it found no matches;
that is not a compiler failure. Other workers' attempted checks are not
reported here.

Iterative raw commands, logs, timestamps, and exits are `command-NN.txt`,
`check-NN.log`, `start-NN.txt`, `end-NN.txt`, and `exit-NN.txt`; exact source
snapshots of owned files are in `snapshots/NN/`. Each fresh directory has
`command.txt`, `check.log`, `start.txt`, `end.txt`, `exit-code.txt`,
`sources.sha256`, and `stability.txt`.

The final exact checker invocation was:

```sh
export XDG_DATA_HOME=/tmp/pts-rk-skfast.TSEzs7/consolidated/data
export AGDA_DIR=/tmp/pts-rk-skfast.TSEzs7/consolidated/config
/tmp/pts-rk-agda-2.8.0.MvVO53/agda --safe --no-default-libraries --ignore-interfaces -i /tmp/pts-rk-agda-2.8.0.MvVO53/cubical -i /tmp/pts-rk-skfast.TSEzs7/consolidated/source /tmp/pts-rk-skfast.TSEzs7/consolidated/source/SKCanonicalExamples.agda
```

## Snapshots and consolidation

Before changing the existing source normalizer or deleting either draft
adapter, copied all three to `consolidation-baseline/`, recording hashes in
its `SHA256SUMS.txt` and timestamp `2026-10-24T01:31:51Z` in
`snapshot-time.txt`. These copies preserve the original proof-derived
normalizer and the separately checked adapters. No claim is made that this
later snapshot time was the original creation time of those files.

Pre-consolidation SHA256:

```text
7f4f228e3151a1f910311293b6a5ac66e06ff3146100a7f62e902e39ea9597bd SKSourceNormal.agda
48f04f35906737deb9810a053496b8435e00635fe7c9e3e3b0d9e29dc80fcb59 SKSourceFast.agda
391790901a189ca140e4901878817647333235f80b9fda07b93dfaa0e559e02a SKFastCanonical.agda
```

Final SHA256, checked unchanged after the fresh consolidated build:

```text
95fa9533bb4861ed4e880ac30ff4ea0ae632a9873804953675ed4007548fc8c3 SKSourceRank.agda
8fdc0a6a57e3eb724fa0699db712f5c8e07b20ec308a1d456312826a6374a5a7 SKSourceNormal.agda
331592836d6742f5a0bfe8ca94b0fdb9c2cdbc738a1d4e304961fa54c08ba034 SKCanonicalExamples.agda
```

Only the worker's newly created draft adapter files were deleted from the
active worktree, using apply_patch after check04 succeeded and after checking
that no other active Agda module imported them. They remain recoverable in
the baseline snapshots and fresh draft evidence.

The unintegrated design comprised 54 lines of original SKSourceNormal plus
144 lines of SKSourceFast and 84 lines of SKFastCanonical: 282 lines. The
consolidated design is 89 lines of SKSourceRank, 61 lines of SKSourceNormal,
and 58 lines of SKCanonicalExamples: 208 lines. This is a 74-line reduction
against that adapter design, not an economy claim for full PTS-rk.

## Checked mathematical scope

`SKSourceRank.budget` computes only from intrinsic simple syntax and the
orders of types annotating actual lambda redex heads. `rank-safe` and
`redex-bound` prove it sufficient for original native typing and reduction;
the proof uses original native rank uniqueness rather than assuming the
bound. Normal source syntax has budget zero. Applying two normal source
terms has budget equal to the function's syntactic head order.

The existing `SKSourceNormal` API now uses this budget with the original
`NativeNormalization.normalize`; its old soundness/coherence/reflection
and idempotence proofs still check. `sufficient-budget-agrees` proves exact
source-tree equality with the rounds computed using any independently
proved native redex bound. No replacement typing relation or new assumption
was introduced.

`SKCanonicalExamples` imports the existing public `SKCanonical`, not a new
adapter. Identity, identity application, alternative identity, and canonical
apply-and-normalize examples prove their outputs by `refl`. Additional source
examples exercise reduction under a lambda and a created redex. The eta
counterexample remains distinct by native beta reflection.

This remains the simply typed annotated source fragment. The canonicalizer
still traverses intrinsic lambda syntax internally. These results do not
claim an all-types direct binder-free evaluator, a full dependent compiler,
a machine-level runtime bound, or a compiled-code size bound.

Root owns aggregate registration, documentation, durable handoff, and the
fresh full-development audit. This worker made no Rocq or native-rule edits.
