# Fixed-head rank obstruction and indexed shallow retraction

Working directory: /Users/akuklev/air/pts-rk

Environment for every command:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
```

Fresh absolute build directory created by `mktemp -d /tmp/pts-rk-self-rank.XXXXXX`:
`/tmp/pts-rk-self-rank.PLMFay/build`.

## Rank obstruction

```sh
opam exec --switch=pts-rk-ci -- dune build \
  --build-dir=/tmp/pts-rk-self-rank.PLMFay/build \
  --display=short --no-buffer theories/self_interpreter/RankObstruction.vo
```

- attempt-01.log: exit 1. An `eapply` in application_spine_rank left its
  argument metavariable unconstrained; the focused subproof remained open.
- attempt-02.log: exit 0 after explicit function/argument instantiation.
  Six public theorem reports: closed under the global context.

```sh
opam exec --switch=pts-rk-ci -- rocq check -silent -o \
  -Q /tmp/pts-rk-self-rank.PLMFay/build/default/theories PTSrk \
  -Q /tmp/pts-rk-self-rank.PLMFay/build/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
  -Q /tmp/pts-rk-self-rank.PLMFay/build/default/theories/self_interpreter PTSrk.SelfInterpreter \
  PTSrk.SelfInterpreter.RankObstruction
```

kernel.log: exit 0. Global loaded-library inventory contains only upstream
functional_extensionality_dep; no unsafe checks. This is distinct from the six
new theorem reports, all closed.

## Indexed shallow retraction

```sh
opam exec --switch=pts-rk-ci -- dune build \
  --build-dir=/tmp/pts-rk-self-rank.PLMFay/build \
  --display=short --no-buffer theories/self_interpreter/RankedDecoder.vo
```

- decoder-01.log: exit 1; wrong direction of Nat.max_assoc rewrite.
- decoder-02.log: exit 1; unrestricted max rewrite also rewrote the inner max.
- decoder-03.log: exit 1; replacing A in decode_typing changed its term occurrence.
- decoder-04.log: exit 0 after restricting replacement to the result type.
  Eleven public theorem reports: closed under the global context.
- decoder-05.log: exit 0 after adding decoder_type_not_in_result_universe.
  Twelve public theorem reports: closed under the global context.

```sh
opam exec --switch=pts-rk-ci -- rocq check -silent -o \
  -Q /tmp/pts-rk-self-rank.PLMFay/build/default/theories PTSrk \
  -Q /tmp/pts-rk-self-rank.PLMFay/build/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
  -Q /tmp/pts-rk-self-rank.PLMFay/build/default/theories/self_interpreter PTSrk.SelfInterpreter \
  PTSrk.SelfInterpreter.RankedDecoder
```

decoder-kernel.log: exit 0. The loaded-library inventory again contains only
upstream functional_extensionality_dep and no unsafe checks. No timeouts,
disabled checks, new axioms, admitted proofs, or original-kernel changes were
introduced. versions.log records the pinned package versions.

The final source theorem names and precise boundaries are in the two modules.
The fixed-head theorem permits arbitrary finite typed application spines but
not arbitrary externally added abstraction wrappers. The indexed packet is
only a shallow retraction, not beta-normal quotation. Full dependent quotation
is not claimed by either module.

## Actual telescope decoders and closed source coverage

The same build command above, with target
`theories/self_interpreter/TelescopeDecoder.vo`, produced:

- telescope-01.log: exit 1; an unused parameter s had no inferable type.
- telescope-02.log: exit 0 after removing that parameter. Seven theorem
  assumption reports, all closed. The preceding dependency compilation also
  printed nine closed RankedQuotation assumption reports.

The same build command, with target
`theories/self_interpreter/ClosedDecoder.vo`, produced:

- closed-01.log: exit 1; an equality placeholder in change was uninferable.
- closed-02.log: exit 1; a replacement needed explicit Fin scope indices.
- closed-03.log: exit 1; lambda congruence needed an explicit RTC relation.
- closed-04.log: exit 0 after finishing unpack/shifted-beta congruence.
  Four theorem assumption reports, all closed.
- closed-05.log: exit 0 after adding closed_every_source_interpreted.
  Five theorem assumption reports, all closed.

The new closed decoder has explicit original PTS type-family and code
parameters. Its source and target programs and its decoder are all closed.
For a fixed application-rank budget and result rank, the SAME decoder
recovers every source in that fragment. Every independently typed closed
Church-STLC source has some budget. This remains a Church-STLC precursor,
not a self-interpreter for all dependent PTS terms.

These two additional modules rely on RankedQuotation's finite normal
quotation theorem. No new assumptions or original-kernel changes were added.
Final isolated full-library/kernel checking is performed by the coordinating
agent after source freeze, separately from these development builds.
