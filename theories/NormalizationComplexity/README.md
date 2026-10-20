# Normalization complexity — normalization bounds and STLC reduction

This library uses the original `PTSrk.Syntax.Term nat`, including lambda
annotations, and the original beta relation. It does not change the calculus.

See the [source map](../README.md) and [repository overview](../../README.md).
This directory is a separate `PTSrk.NormalizationComplexity` Rocq library.

The [development exposition](README.tex) and its [compiled PDF](README.pdf)
explain the infrastructure, semantic descent argument, executable cost model,
conservative rank repair, and two-way STLC conversion reduction.

The three requested results are proved in the explicit operation-cost model
described below. There are no assumed semantic rank, descent or termination
contracts. The automatic bound is a conservative repair of a false bridge in
the manuscript; the original Agda estimator translation remains unchanged.

## Public results

For encoding size `s = encodingSize t` and node count `N = nodes t`:

- `fixed_rank_normalization` in `BoundedNormalization.v`: every original-typed
  `d`-bounded term in a well-formed context normalizes in `d` greedy passes,
  with cost at most `tower (2*d+1) (N+5*d+2)`. This is ELEMENTARY for fixed `d`.
- `rank_bound_in_linear_time` in `Normalization.v`: for closed original-typed
  terms, compute the semantic redex-head bound
  `conservativeRank t = 1 + maxRankLiteral t + nodes t`, of magnitude at most
  `2*s+1`, with traversal cost at most `7*s`.
- `normalization_in_TOWER` in `Normalization.v`: the total executable
  `automaticNormalizer` succeeds on every closed original-typed input, returns
  a beta-reachable normal form of the SAME original type, and costs at most
  `tower (4*s+3) (18*s+8)`, including computation of the rank bound.

Here `tower 0 x = x` and `tower (S h) x = 2^(tower h x)`. Thus the last bound
has linear tower height and linear bottom argument, not fixed height.
`automaticNormalizer` is total on raw syntax; its `None` branch is proved
unreachable on the specified well-typed closed inputs. No input typing
decision procedure is being timed or claimed complete.

## Completeness: checked reduction, external hardness theorem

The updated paper's lower-bound statement concerns **beta-convertibility of
closed well-typed terms**, a decision problem. `STLCEmbedding.v` proves
`ChurchSTLC.church_stlc_reduction`: for two independently simply typed,
term-closed Church terms of the same simple type, the translation produces
closed original-PTS inhabitants of the same type, preserves AND reflects
beta-convertibility, and increases their combined encoding size by exactly 4.

The source shares scoped de Bruijn raw syntax with PTS, but defines its own
simple types, typing derivations and beta rules. Its only ground type is a
distinguished variable with no source term binding. Arrow types are encoded
as products; lambda annotations are retained. The translation adds a single
`lambda o:U0` around each input. Type-code normality, shape preservation under
substitution, and original confluence establish reflection; there is no
annotation-erasing bridge or assumption of target convertibility.

[Nguyen's Theorem 1](https://arxiv.org/html/2305.12601v4) supplies the external
STLC TOWER-hardness result (under elementary many-one reductions). The paper
covers Church-style inputs, so this reduction needs neither Curry type
inference nor a claim that explicit annotations can be reconstructed in
linear time. Our size measure counts those annotations and unary indices.
The wrapper constructs one lambda and one sort; its proved size equation is
not a machine-level time certificate for a serializer.

**Formalization boundary:** Rocq checks this reduction, not Nguyen's hardness
proof. No Turing-machine complexity classes, external-input encoding theorem,
or STLC TOWER-hardness theorem have been formalized here, and none has been
postulated as an axiom. Combining the reduction with that cited theorem gives
the manuscript's mathematical lower-bound argument; an unconditional Rocq
theorem of machine-level TOWER-completeness remains outstanding. The existing
upper bounds retain the operation-cost qualifications below.

## Implemented and checked

- `Rank.v`: translation of all estimator variants in `rank.agda`. `RC`'s
  let-bindings are estimator bookkeeping, not additional PTS constructors.
  `rankPair_correct`, `rankCached_correct`, and `traversal_correct` prove
  the optimizations agree with the simplified estimator. They do **not**
  assert equality with the reference estimator on arbitrary ill-typed terms.
- `Greedy.v`: the paper's bottom-up parallel reducer, including annotations;
  each pass and its iterates are original beta reductions. `normalizeWithin`
  is a total *bounded attempt*. A `Some` result is beta reachable and normal;
  `None` is possible at insufficient budgets. The semantic theorems now prove
  success at a supplied redex-rank bound and at the conservative automatic bound.
- `Bounds.v`: substitution multiplies node sizes at most; a greedy pass has
  at most `2 ^ nodes t` nodes; `k` passes have at most `tower k (nodes t)`
  nodes. The estimator's numeric output is at most `2 * encodingSize t`.
  Its two-pass abstract traversal cost is at most `10 * encodingSize t`.
- `Literals.v`: maximum sort literals are preserved by renaming and cannot
  increase through beta reduction; any reachable sort is bounded by the
  input maximum. This covers substitution and annotation reduction, not
  arbitrary beta expansion.
- `Runtime.v`: executable costed renaming, substitution, greedy reduction,
  iteration and normal-form checking. Projection equals the original
  operation in each case. Binder lifting and the shifts of substituted terms
  are charged explicitly. For a term with `n` syntax nodes, the bounded
  attempt with `k` passes costs at most `tower (2*k+1) (n+5*k+2)`.
  For a closed input with encoding size `s`, the estimator-budget attempt
  costs at most `tower (4*s+3) (11*s+7)`, whether or not it succeeds.
- `RedexRanks.v`: semantic redex-head ranks are witnessed by ORIGINAL typing
  derivations for the head and its product type. All subterm positions,
  including annotations, are covered. Every redex rank is positive, and
  every well-typed term in a well-formed context with rank bound zero is
  already normal. The bound is not defined in terms of normalization fuel.
  Type ranks are unique and invariant under conversion, substitution and
  reduction. Argument ranks are strictly below function ranks; application
  result ranks do not increase. A lambda newly exposed by a greedy pass has
  rank bounded by an original redex on its application spine. Consequently
  every head contracted in the greedy application clause is bounded by the
  original application's redex bound (`greedy_contracted_head_bound`).
- `Morphisms.v`, `Safety.v`: typed simultaneous substitutions, equivalent
  structural redex bounds, substitution residual bounds and context transport.
- `Descent.v`: `greedy_strict_descent` and `bounded_rounds_normal`, with no
  assumed descent contract. Both include annotation reductions.
- `SortBounds.v`: a sort-rank bound uniform over typed substitutions and
  application spines, proved using inversion, confluence and literal bounds.
- `AutomaticBound.v`: the conservative bound and its linear cost/magnitude.
- `BoundedNormalization.v`, `Normalization.v`: the public results above.
- `EstimatorChecks.v`: checked counterexample to the manuscript's claimed
  `estimateRank+1` semantic head-rank bound (see below).
- `STLCEmbedding.v`: independent Church STLC typing and reduction, the
  annotation-preserving closed embedding and two-way conversion theorem.
- `Audit.v`: 95 transitive `Print Assumptions` reports, all closed under the
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
The reducer cost model also treats cost counters as ghost accounting; their
unary evaluation is not part of the claimed charge. It counts constructor
operations and callback work, including every lifted renaming/substitution.
Loop overhead and the final normal-form test are included in the bounded
attempt's cost theorem. A successful result is beta reachable and normal.

## Correction to the manuscript's automatic-bound argument

The paper's relevant section is `latex/paper.tex`, label `complexity`, with
the fixed-rank theorem labelled `bounded-sn`. It restricts the automatic
rank-bound result to **closed, well-typed** terms; raw/open terms cannot
silently be included. Its claim that bounding abstraction-domain ranks by B
makes a term (B+1)-bounded is false for the stated semantic head ranks.

The kernel-checked counterexample uses:

```text
B = Pi _:U0. U0
A = Pi _:B. U0
t = Pi x:A. Pi y:B. ((lambda z:U0. x) U0) y
```

`t : U3` is closed, `estimateRank t = 0`, but the displayed lambda has type
`Pi z:U0. A`, of rank 2. Thus `t` is NOT `estimateRank t + 1`-bounded.
This does not refute TOWER normalization or show that the smaller-budget
attempt fails on this input. It refutes the proposed bridge to the fixed-rank
theorem. `EstimatorChecks.estimator_does_not_bound_head_ranks` proves this
distinction, rather than leaving a false statement as an open obligation.

The repair bounds sort ranks by `maxRankLiteral t + nodes t` uniformly under
typed substitution and application spines. Accounting for every binder,
including products, gives the conservative redex-head bound above. No kernel
rules, input typing conditions or definitions of head rank are weakened.
The sharper Agda-budget success statement is not used or claimed.

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
