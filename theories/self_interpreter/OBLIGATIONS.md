# Self-interpreter obligations

This ledger reconciles the research-note versions at `73c4303`, `3411f31`,
`e822cd6`, `ade6387`, `2da7627`, and the concise exposition at `f5fdac0`.
Historical open-status paragraphs do not override the current endpoints.
CPS formalization is excluded from the present continuation by request.

## Discharged prerequisites

| Obligation in earlier notes | Current evidence |
| --- | --- |
| Executable derivation-directed quotation, agreement with the relational STLC construction, syntax injection | `ExecutableQuotation`; the independent full-source recursion is `RecursiveQuotation.quote_derivation` |
| Finite typed HOAS/PHOAS binder representation | `ChurchSyntax`, `PHOASAlgebra` and the dependent Tarski signature/operation modules |
| Represented source type as an ordinary object argument | `IndexedProgramInterpreter.interpreter`, with arguments `P` and `Q` |
| Full dependent context, substitution, application and conversion coherence | `QuotationViewSubstitution`, `LocalCodeAlignment`, `ApplicationQuotation`, `RecursiveQuotation` |
| Original typing, annotation normality, faithful syntax, literal recovery and full coverage | `FullDependentInterpreter.every_closed_original`, `closed_type_recovers`, `closed_conversion_injective`, `every_original` |
| Eliminate the earlier externally normalized semantic payload from interpretation | The final interpreter executes the PHOAS program at its constructed identity filling; it does not use `WeakFullInterpretation`'s payload |

The alternative numeric-normalizer route is not a missing premise of these
theorems. Its compiler and dependent reifier are distinct additional results.

## Improvements and precise limitations checked in this continuation

`SizedSyntaxEnumeration` generates exact node sizes directly. Its soundness
and completeness include all original annotated constructors and arbitrary
scope/literal bounds. `old_enumeration_agrees` proves equality of membership
with the depth-and-filter specification. `count_correct` proves the exact
output-count recurrence; this is not a machine-runtime theorem. At node
bound 5, scope 0 and literal ceiling 0 the vocabulary has 68 trees; at bound
7 it has 1209. The construction never generates a larger tree for filtering.

`CheckedEqualityFields.typed_descriptors_iff` validates carrier/operand
prefiltering before forming triples. `CheckedContextualFields` rejects an
invalid binder prefix before generating its descendants. Both
`entries_reference_agrees` theorems prove that exactly the reference-accepted
fields remain available. The original typing checks and filled-endpoint
conversion test are retained. Enumeration order is an implementation choice;
old byte-identical quotation or field-slot numbering is not promised.
The resulting signature still contains all accepted fields at its bounds:
these optimizations do not solve the smaller-coherence-interface problem.

`SourcePruning` removes conversion nodes with literally equal endpoint
types. It preserves the original annotated judgment, is idempotent, and
does not increase derivation size or repair count. The full closed quoter
now applies it before budget selection. `closed_padding_invariant` proves
literal equality of the final type program, faithful program and decoding
expression after arbitrarily many redundant wrappers. It applies to the
computational derivation data, without extracting a witness from Prop.

`QuotationCost.plan_length` proves the exact repair-count recurrence for
the actual six-rule quoter. After pruning the count is
`2 * Pi + lambda + 2 * application + 2 * conversion`, strictly less than
the derivation's rule count. Enumeration, normalization inside typechecking,
dependent substitutions, generated term size, and beta-evaluation are not
unit-cost operations in this theorem.

`PlanNonuniformity` supplies two infinite counterexample families:

- Nested applications of `lambda x:U0.x` have result type rank 0, literal
  ceiling 0 and redex bound 1. Their actual plans have length `3*h`, even
  after pruning (`QuotationCost.fixed_rank_plan_length`). Therefore the
  current plans have no bound determined by those source ranks alone.
- Even the identical judgment `U0:U0` has arbitrarily long conversion
  detours through `(lambda x:U0.x) U0`. Literal-reflexivity pruning retains
  them; their plans have length `7*h` (`fixed_judgment_plan_length`).
  `no_source_only_plan_bound` rules out a bound on this algorithm's plans
  determined solely by the final source judgment when arbitrary derivation
  data is accepted.

These theorems refute specific stronger claims about the present quoter.
They do not refute a canonical elaborator or a different rank-uniform
interpreter. In particular, growing plan length alone does not prove that
every possible interpreter's type rank must grow.

## Execution evidence and remaining work

The extracted actual full-source quoter was tested on a sort, a lambda and
an application. The sort's raw/type/faithful normality checks pass; both
non-leaf cases reach the 30-second limit (exit 124), without completing a
normality result. The small exact-size enumerator tests pass. Thus the work
extends execution evidence beyond the earlier leaf-only probe, but does
not establish practical non-leaf execution or a speedup for full quotation.
Standard extraction erases dependent proofs; direct Rocq evaluation of the
dependent records is a separate operational question. Exact commands,
versions, timings, failures and verification are recorded in
[the evidence report](../../docs/direct-r-handoff/verification/self-interpreter-improvements-2026-10-21/COMMANDS.md).

The remaining non-CPS research obligations are:

1. Replace all-accepted-field enumeration with a small, uniformly realized
   coherence interface. Candidate filtering is now improved, but actual
   dependent quotation still requires costly complete layers. The next
   concrete optimization is avoiding a checked layer when a type-code
   alignment is already literal, while proving normality and recovery.
2. Build canonical computational source evidence from the original annotated
   syntax and requested type, with correctness and completeness for original
   typing. `OriginalTypecheck` currently returns types/booleans;
   `CanonicalSource` only canonicalizes conversion paths in supplied data.
   Neither produces derivation-independent quotation. The detour theorem
   shows why literal-reflexivity pruning alone cannot finish this task.
3. Find a different rank-only interface, or prove an impossibility theorem
   for an explicitly specified class. The present fixed-head obstruction,
   raw-HOAS literal obstruction, and allocation counterexamples have narrower
   scopes. None establishes impossibility for all conservative-rank-indexed
   dependent PHOAS representations.
4. Prove end-to-end quotation/evaluator operation costs under a stated cost
   model. The new cardinality and allocation counts are components of that
   analysis; the contextual layer sizes and typechecking costs remain.
5. Independently formalize non-uniform elementary representability, including
   the corrected modulus construction, serialization and original numeral
   beta equations. Its normalization specialization would compute numeric
   codes. Actual typed HOAS/numeric adapters and dependent reification would
   still be needed to obtain a separate raw-HOAS interpreter. The completed
   PHOAS evaluator does not silently discharge this stronger specification.

No CPS translation or continuation algebra is added by this work.
