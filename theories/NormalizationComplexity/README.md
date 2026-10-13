# Normalization complexity — partial formalization

This library uses the original `PTSrk.Syntax.Term nat`, including lambda
annotations, and the original beta relation. It does not change the calculus.

## Implemented and checked

- `Rank.v`: translation of all estimator variants in `rank.agda`. `RC`'s
  let-bindings are estimator bookkeeping, not additional PTS constructors.
  `rankPair_correct`, `rankCached_correct`, and `traversal_correct` prove
  the optimizations agree with the simplified estimator. They do **not**
  assert equality with the reference estimator on arbitrary ill-typed terms.
- `Greedy.v`: the paper's bottom-up parallel reducer, including annotations;
  each pass and its iterates are original beta reductions. `normalizeWithin`
  is a total *bounded attempt*. A `Some` result is beta reachable and normal;
  `None` is explicitly possible. This is not yet a total normalizer for typed
  terms at the computed budget.
- `Bounds.v`: substitution multiplies node sizes at most; a greedy pass has
  at most `2 ^ nodes t` nodes; `k` passes have at most `tower k (nodes t)`
  nodes. The estimator's numeric output is at most `2 * encodingSize t`.
  Its two-pass abstract traversal cost is at most `10 * encodingSize t`.
- `Audit.v`: 15 transitive `Print Assumptions` reports, all closed under the
  global context on Rocq 9.2.0. No additional axioms or admitted proofs.

## Cost and input conventions

`encodingSize` counts unary sort labels and unary de Bruijn indices, as well
as term constructors. The abstract word-operation model charges context
lookup by the index length, so lookup is **not** treated as constant-time.
Arithmetic/max operations on rank words have constant charge; constructor
cases have the explicit weights in `traversalCost` and `literalScanCost`.
The numeric bound justifies logarithmic-width words for closed inputs under
this encoding. This is a traversal-cost theorem, not a machine-verified
running-time theorem for Rocq's unary `nat` evaluator or extracted code.
In particular, binary sort labels need a separate bit-complexity analysis.

## Not proved: the requested full classification

The TOWER and fixed-rank ELEMENTARY normalization theorems remain open.
The paper's relevant section is `latex/paper.tex`, label `complexity`, with
the fixed-rank theorem labelled `bounded-sn`. It restricts the automatic
rank-bound result to **closed, well-typed** terms; raw/open terms cannot
silently be included.

The next obligations, in dependency order, are:

1. Define contextual redex-rank bounds using original `Typing.typ` at
   `Ranks.RankSorts`. Prove the estimator is a semantic upper bound on
   abstraction-domain ranks, accounting for typing conversion, substitutions,
   annotation reduction, and the maximum-literal default.
2. Prove strict redex-rank descent for `greedy`, hence normality after the
   claimed number of rounds. In particular, for a closed well-typed `t`,
   establish `normalb (rounds (S (RankEstimate.estimateRank t)) t) = true`.
   Qualitative strong normalization alone does not establish this budget.
3. Give a costed implementation of renaming/substitution and greedy passes,
   then derive the time bounds. The checked tower bound on **output node
   count** is not itself a proof of running-time class membership.

`elementaryBound` and `towerBound` are only numerical envelope definitions,
not certificates of class membership. No open obligation is assumed by any
checked theorem in this directory.

## Reproduce

Use the repository's dedicated local opam environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
opam exec --switch=pts-rk-ci -- timeout 180 dune build \
  --display=short --no-buffer theories/NormalizationComplexity/Audit.vo
```

The regular CI driver now includes this audit without removing other stages.
For a fresh audit use a new absolute `--build-dir`, since cached `.vo` targets
do not repeat `Print Assumptions` output. See the handoff state for exact logs.
