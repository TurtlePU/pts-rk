# Next proof: arbitrary comparison-trace agreement

Read-only source review, 2026-10-23. This is an implementation plan, **not** a
compiled theorem or a completed part of milestone 4. The frozen checkpoint
contains Trace formation and the three local observation-agreement lemmas.

Use the motive

```text
mu x y z b := Same (compare x y z) b
```

Here `z : Zip x y` is the actual execution witness, and Same transports
exact-rank-one Boolean predicates. It is not syntactic identity. The motive
result has exact rank 3, as required by Trace; its predicate type has rank 5.
The Trace fiber has rank 6. The prospective full agreement type has rank 7.
These proposed assembly ranks must still be checked in Rocq. The motive
does not quantify over Trace evidence, so this route does not require a
same-index recursive rank increase.

## Minimal assembly

1. Define the closed motive and its scoped application. Prove formation and
   the four-head beta law to Same, using the structural NamedBeta helpers.
2. Abstract each existing local agreement case at its **exact applied-motive
   annotation**. For pair/pair, convert the two child hypotheses from applied
   motive to Same, invoke `pair_pair_observation_agreement`, then convert the
   conclusion back. This avoids converting dependent telescope domains or
   using eta. Atom and pair/atom use their existing local lemmas similarly.
3. Instantiate the 60 fields (motive, 29 atom cases, 29 pair/atom cases, one
   pair/pair case) with NamedSpine. A useful native annotation lemma states
   that evaluation of a field after assigning name 200 to the closed motive
   agrees with closing `substitute_named 200 motive` on that field. Derive it
   from `evaluate_substitute_named`, `evaluate_close` and update identity;
   later handler assignments do not occur in these annotations. Keep closed
   payloads opaque.
4. Before applying the spine, convert an arbitrary witness
   `h : trace_at x y z b` to the expanded field telescope F. Prove a native
   `trace_head_view` from typed indices and a well-formed ambient context:
   F has sort 6 and `trace_at x y z b` beta-converts to F. Formation must
   follow from **four forward head reductions** and original subject
   reduction, not from beta equivalence alone. A forward-reduction version
   of `named_application4_beta` supplies the needed directed path.
5. Apply the checked spine to h, convert the resulting applied motive to
   Same, and abstract only the five outer binders x, y, z, b, h. Their typing
   establishes context well-formedness; no object-language well-formedness
   assumption is added.

This route needs neither Trace constructor inhabitants nor lookup in their
large binder contexts. It uses no parametricity, cumulativity, eta, new PTS
rule or assumed endpoint agreement. Even success would prove comparison
observation agreement, not arbitrary lookup functionality, internally
combined source provenance, operational resource sufficiency or dependent
finite-fragment soundness.
