# What remains before Theorem 5 is proved

This is an implementation checklist, not a list of new axioms. The lack of a
compiler and the lack of the following uniform proofs are separate limitations.
Installing a compiler alone does not discharge the latter.

## 1. Kernel compilation and infrastructure audit

Build the unchanged upstream first, then DirectRKernel, DirectREval and
DirectRCheck. Check the new dependent-pattern proofs, implicit arguments,
upstream API uses, and computed examples. The scripts are uncompiled; success
has not been established even for the previously written R1/R2 scripts.
`run_check_sound` is meant to conclude the original typing judgment. Do not
replace its conclusion by a different bidirectional judgment.

## 2. Uniform scope/totality of generators

In DirectRObligations.v:

```coq
Definition GeneratorTotal : Prop :=
  forall a, exists p, Generated.witness a = Some p.
```

Prove it from the named assembler and fresh-name invariants, for unbounded
external indices. A few successful calls to `assemble` do not give this result.
The branch for an invalid inequality is unreachable for `ax_distinct` because
its index includes a proof `m <> n`; this must be used in the totality proof.

## 3. Uniform typing of selectors and finite observations

Supply generic lemmas for arbitrary arity q:

* formation of the q-ary selector type (q > 0 at the required rank);
* typing of each selector indexed by Fin q and its beta projection equations;
* typed abstraction and application over variable-length telescopes;
* typing/elimination for `delta_q` at motive rank 3, with exact-rank lifts;
* operation-table closure and the 23 individually guarded algebra laws.

These conclusions must be upstream typing judgments about object terms.
DirectRArithmetic's native Prop facts can discharge finite numerical side
conditions; they cannot be coerced into object-language inhabitants.

## 4. The bounded-case invariant for arbitrary admitted objects

Prove the generators of `Inv_n` closure are typed for every n. Track the ranks
of Case_n (8), Inv_n (10), and Good (12). Preserve positive G evidence outside
negative case analysis. Use Good's bounded-rank eliminator, not host induction
on external expression trees. In particular, the theorem must cover an arbitrary
object d carrying a Good proof, not merely the encodings of finitely many trees.

Multiplication must keep both zero-factor cases; only a positive second factor
permits propagating a large-factor lower bound.

## 5. Assemble ALL axiom indices, not just test cases

In DirectRObligations.v:

```coq
Definition GeneratorSound : Prop :=
  forall a p, Generated.witness a = Some p ->
    Core.Typed ε p (Codes.axiom_type a).
```

Prove both contracts. `target_from_generator_contracts` then assembles the
unchanged `Kernel.Theorem5Target` record. It is deliberately conditional now:
no inhabitant of that record is asserted without these inputs.

This closes the uniform AXIOM-witness component, not the whole interpretation.
Ground faithfulness additionally needs uniform expression-to-numeral equality
witnesses, relation congruence, and finite-observation refutations for every false
ground equation/comparison.

## 6. Preservation of classical first-order derivations

FirstOrder currently has syntax and translation, not a source deduction
relation. Choose and define a precise classical proof calculus and formalize its
R schemes. Prove substitution/renaming of the translation, rank-correct stable
logical rules, nonempty/closed admitted domain, equality/congruence obligations,
and then induction over arbitrary source derivations.

A conditional theorem about a native Rocq arithmetic observation, or simply
exposing functions named R1--R5, does not establish this syntactic interpretation.

## Out of scope

Answer-type nontriviality, semantic models, and a proof of consistency of the
original PTS are intentionally not included and are NOT prerequisites for
constructing these typed witnesses. No impossibility theorem for same-level
computational Church arithmetic is invoked: the direct-R construction builds
arithmetic presentations and uses observational equality, not same-level beta
computation of numeric multiplication/remainder.
