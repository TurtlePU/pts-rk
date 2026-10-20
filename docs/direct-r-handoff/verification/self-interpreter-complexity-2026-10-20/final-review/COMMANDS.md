# Independent final review and full CI — 2026-10-20

## Source-contract review

Read-only review of the three frozen new modules found no proof-contract or
rank-arithmetic defect. No proof source or manuscript was edited by this
review. Original annotated `Syntax.Term nat`, `Typing.typ`, `Ranks.RankSorts`
and beta conversion remain the object-language judgments.

- `RankedNormalization.normalized_source_correct` requires original typing,
  well-formedness and the independent semantic redex bound. The automatic
  closed endpoint derives its bound from syntax. Normalized HOAS codes identify
  exactly original beta conversion, including annotation reduction; they do
  not preserve unreduced source syntax. Cost fields explicitly charge the
  normalization stage only, not quotation construction or serialization.
- `LiteralObstruction.normal_sort_counterexample` uses closed normal original
  sources `U_k : U_0`, all with redex bound zero and type rank zero. The
  obstruction applies to a fixed head and fixed-rank current raw-HOAS code
  whose labels are numeral data. An external source-literal ceiling or a
  source-dependent literal bank lies outside its conclusion. No sufficiency
  theorem for such a repair is claimed.
- `WeakFullInterpretation.full_closed_weak_interpretation` has only the
  independent premise `typ empty t A`. Its exact sort witness `s` is derived
  using original typing validity, not postulated or replaced by a cumulative
  upper bound. Both the payload and its type annotation are externally
  normalized. The package type has sort `max(s+2,r+5)` and the decoder type
  has sort `max(s+3,r+6)`. The actual closed decoder application has original
  type `A`; five explicit beta steps recover `nf(t)`, hence beta conversion
  to `t`. Exact-source injectivity follows from the raw-HOAS tag, not from
  normalization. It does not assert literal equality of independent source
  type arguments `A` and `B`.
- This is a normalization-assisted semantic packet, **not a pure HOAS/PHOAS
  evaluator and not strong recovery of the unreduced source**. The decoder
  ignores its syntax field. Internal typed reification/evaluation and the
  generic elementary numeric compiler remain separate open work.

The research note's new conditional numeric self-reducer argument is
mathematically sound under its explicit elementary serialization and
manuscript representability assumptions. The report distinguishes it from a
checked compiler. The manuscript modulus correction `r f x`, rather than
`r X f x`, is correctly explained. Two wording corrections were reported to
the author: an input-dependent tower **upper bound alone** does not prove
non-elementarity; the fixed-head obstruction is a **rank** argument, not
diagonalization. The author owns the resulting note edits.
Both corrections are present in the reviewed final introduction. The new
literal-obstruction, canonical-HOAS and semantic-packet sections (lines
391--562 at review time), and final status, agree with the literal Rocq
contracts and explicitly leave internal dependent HOAS/PHOAS evaluation open.

Reviewed source SHA-256:

```text
8cba486895077ccbfa417cc4cdc22eb1a8cd7d26c447e3e88c4c3f3a9a9335e1  theories/self_interpreter/RankedNormalization.v
f391b5a5656d5f3428dffc497e931902355d10cfab3b65b185c112bdb3abb093  theories/self_interpreter/LiteralObstruction.v
ed2818269d20d89f7f8101fa6a756eaa2b3861c1840517e1cb0e92eb68a3244e  theories/self_interpreter/WeakFullInterpretation.v
c00f0f8a938d21acb5b6ec22f1a48f6e5b325eda5af24294fc6cc739c3ca4867  theories/self_interpreter/Audit.v
```

## Full local CI

Prepared fresh ignored evidence directory:
`_build/self-interpreter-complexity-ci.4sCyGR`.
The literal launcher is retained there as `RUN.sh` and invokes the unchanged
`bash tools/check-local-ci.sh`, including actionlint, pristine upstream and
the entire staged driver. No CI stage or timeout was weakened.

```sh
export DIRECT_R_LOCAL_HOME=/Users/akuklev/.local/share/pts-rk-ci
export DIRECT_R_LOCAL_SWITCH=pts-rk-ci
export DIRECT_R_LOG_DIR=/Users/akuklev/air/pts-rk/_build/self-interpreter-complexity-ci.4sCyGR/staged
export DIRECT_R_JOBS=2
export DIRECT_R_STAGE_SECONDS=1200
bash /Users/akuklev/air/pts-rk/_build/self-interpreter-complexity-ci.4sCyGR/RUN.sh
```

Result: **exit 0; actionlint passed and all 226/226 staged checks passed**.
The run began at `2026-10-20 09:32:18 UTC` and finished at
`2026-10-20 09:32:50 UTC`, after the author froze the complete Rocq/Dune
sources including the 15 new aggregate audit endpoints. HEAD was
`73c4303dca2228bb6b3a8ec6ba5099a86da00bb0`; this is a worktree verification,
not a claim that the changes are committed. The three new source hashes
were unchanged after CI.

Observed toolchain: Rocq core 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2, Dune 3.23.1, opam 2.6.1. The complete package inventory and
switch export are retained in the ignored evidence directory.

Raw evidence retained locally:

- `RUN.sh`, `driver.log`, `exit-code.txt`;
- `staged/stages.tsv`, `staged/result.txt`, `staged/versions.log`,
  `staged/opam-switch.export`;
- all individual stage logs, including `staged/01-upstream.log`,
  `staged/01-normalization-complexity.log` and
  `staged/01-self-interpreter.log`, plus the copied Dune logs.

The separate fresh aggregate build, assumption inventory and recursive kernel
audit are owned by the parent agent. Ordinary staged CI is not described as
a fresh replay of every cached `Print Assumptions` command. No failed stage,
timeout or interruption occurred in this run.
