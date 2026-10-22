# Self-interpreter obligations

This ledger reconciles the research-note versions at `73c4303`, `3411f31`,
`e822cd6`, `ade6387`, `2da7627`, and the concise exposition at `f5fdac0`.
Historical open-status paragraphs do not override the current endpoints.
The current continuation explicitly includes general folds and CPS examples.
The earlier exclusion of CPS is superseded; full dependent CPS is still open.

## Shared-algebra continuation

The public interface is now `Algebra`: one original typed finite-telescope
filling, used by the SAME application-spine fold for type and term programs.
`UnifiedAlgebra` exposes full-source quotation and literal identity recovery
without the raw HOAS envelope. `PHOASFold.shared_fold` and
`CombinatoryAlgebra.fold_is_run` prove exact agreement of the existing
specialized folds with this shared operation; neither recodes the payload.
`GenericFold` abstracts the filling as ordinary arguments of an actual normal
operator for each fixed signature. Its syntactic composition law is not a
semantic fusion theorem or a compatibility theorem for arbitrary signatures.

| Checked result | Boundary |
| --- | --- |
| `UnifiedAlgebra.every_closed_original`, `open_original_type`, `open_recovers`: normal tag-free full-dependent programs, typed normal head, literal recovery | Signature and coherence fields still depend on the numerical plan; a generic typed filling is not a constructed nonidentity filling |
| `Algebra.fold_typed`, `fold_type_typed`, `fold_closure`, `fold_substitution`: original typing and actual application/substitution laws | Not a parametricity/no-junk theorem or one signature at each rank bound |
| `GenericFold.head_typed`, `head_normal`, `run_typed`, `run_computes`, `run_closure`: actual generic operator, ordinary algebra arguments, beta specialization | One head per finite signature, not one head per rank-only fragment; explicit expansion, no eta conversion |
| `UnifiedAlgebra.normal_recovery_injective` | Normal SOURCE terms through a common algebra only; arbitrary reducible-source and cross-plan intrinsic injection remain open |
| `PHOASFold.observe_quotation`: nonidentity constructor observation on existing intrinsically faithful STLC quotations | Outputs are distinct exact-rank sort tokens, not internally eliminable Church Booleans; `observer_not_conversion_invariant` proves failure to preserve all source beta equalities |
| `PHOASCPS`: originally typed CBN local handlers, beta laws and exact translated-type ranks | No complete term translation or full-dependent algebra; `no_rank_one_cps_type_budget` concerns THIS literal CPS type translation |
| `CombinatoryFold`: finite-dictionary Church trees, intrinsic fidelity, general fold, typed CBV continuation algebra and constructor observer on the SAME rank-correct code | Homogeneous tree interpretation, not source-type-indexed dependent unquotation; fidelity fixes the dictionary |
| `CombinatoryFold.catalogue_finite_fold` | Concrete 65-shape Hilbert extraction plus faithful finite-dictionary tree coding, not native PTS-to-Hilbert completeness or internal recovery of heterogeneous expanded subjects |

The full faithful compatibility API is retained. Removing its tag while
preserving its stronger all-source contract requires an intrinsic parser
for generated type/term payloads, distinguishing neutral constructors from
casts, and stable under signature insertion, binders and all six quotation
rules. Existing source views are external metadata, not such a parser.
No actual collision or impossibility of this intrinsic parser is established.
`PHOASConversion.no_small_type_shared_map` only forbids identifying a normal
faithful code with its conversion-preserving semantic type index.

No numeral conversion is used by the shared fold, STLC observer or combinatory
continuation algebra. Finite selectors can replace numeric atom selection.
External numerical resource indices and independently checked proof codes
remain; changing serialization does not prove their acceptance soundness.

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

The fragment-uniformity continuation adds three independent modules.
`FragmentUniformity.local_request_rank_bound` bounds the actual alignment
request by `k+2` when local declaration ranks and the motive rank are at most
`k+1`. Its capped allocator preserves exactly the accepted fields within the
cap, including normal original-typed realizations, for arbitrarily many layers.
`CappedInterpreter` supplies executable lookup, normal typed interpreters and
`rank_uniform`: their type-sort rank is at most `max(k+7,r+6)`, independently
of all plan lengths and enumeration budgets. This uses the actual base
signature and cap `k+3`.

The capped quotation port now supplies full-source coverage. Its state invariant
bounds local binder ranks and is derived recursively, starting from the empty
local spine. `CappedQuotationState.allocate_local` computes an actual slot from
original typed endpoints and their filled conversion; `CappedCodeAlignment`
proves normal typed coercion and literal erasure. `CappedRecursiveQuotation`
handles all six rules. `CappedDependentInterpreter.every_bounded_original`
quantifies over a caller-fixed `k`: every closed judgment with independent
pruned source budget at most `k` has normal codes and literal recovery by an
interpreter of type-sort rank at most `max(k+7,r+6)`. Cross-budget faithful
syntax injection, literal type recovery and all original closed/open coverage
are retained. For open inputs the rank bound uses their annotated closure's
budget. This discharges the quotation port. The closure construction below
additionally supplies a common application head; the bridge from semantic
redex bounds to quotation budgets remains open.

`FiniteCoherenceCatalogue.no_finite_literal_catalogue` rules out finite
exhaustive lists of concrete fields: rank-2 normal accepted equalities under
arbitrarily many rank-0 binders have `2*h+11` nodes and literal ceiling zero.
Finite generic law schemes and ordinary encoded environments are outside
this obstruction. `conservative_fragment_finite` distinguishes the finite
syntax fragment obtained by bounding the conservative estimator from true
rank bounds with unbounded source size.

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

The remaining research obligations are:

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
3. Supply one rank-fragment PHOAS constructor/coherence signature with
   independent nonidentity realizations. The new `Algebra` API already
   shares the fold operation, and concrete nonidentity folds are checked
   for STLC and combinatory trees; the full dependent signature still varies.
   **Execution interface discharged:** `FragmentClosureInterpreter` fixes
   one normal head of exact type-sort `k+10` before the source and covers
   every judgment in the independent quotation-budget fragment. Its ordinary
   argument spine is the padded normal result type, a normal closure code,
   and a fixed forcing argument. Original typing, literal term recovery and
   cross-budget syntax/conversion injection are proved. `FixedInterface`
   packages the original normal faithful PHOAS program with a normal runner;
   `RankPadding` realizes exact common sorts without cumulativity. The runner
   still depends on the source plan and represented type. Only the result
   type, not the source value, is externally normalized for this wrapper.
   Final forcing uses that type argument's explicit function shape; it is
   not an eliminator for arbitrary types of the common sort. The underlying
   capped theorem separately retains literal type-program recovery.
   The bound `k` is the existing formation/literal quotation budget. Relating
   it to a fragment specified only by semantic normalization redex ranks
   (with any required literal/type ceilings) is a further source-side bridge.
   The finite-catalogue obstruction rules out an exhaustive fixed list of all
   accepted concrete fields, not every rank-indexed dependent PHOAS representation.
   A common closure interface is not one shared PHOAS constructor algebra
   and does not internally reify numeric proof codes.
4. Prove end-to-end quotation/evaluator operation costs under a stated cost
   model. The new cardinality and allocation counts are components of that
   analysis; the contextual layer sizes and typechecking costs remain.
5. Independently formalize non-uniform elementary representability, including
   the corrected modulus construction, serialization and original numeral
   beta equations. Its normalization specialization would compute numeric
   codes. Actual typed HOAS/numeric adapters and dependent reification would
   still be needed to obtain a separate raw-HOAS interpreter. The completed
   PHOAS evaluator does not silently discharge this stronger specification.
6. Construct an internal PTS operation over represented certificate codes and
   resource budgets. Define the arithmetic domain and exact checker trace
   independently, and connect arbitrary admitted trace witnesses to internally
   produced typed programs. For consistency, an internal reifier
   `Accepted_k(p) -> Code_k(Bottom)` and typed evaluator
   `Code_k(Bottom) -> Bottom` suffice at fixed k. Syntax fidelity can be omitted
   for this specialized interface. External derivation-directed quotation is
   not that internal reifier. A full consistency sentence additionally needs
   internal budget/domain handling; an externally indexed family does not
   supply it. See the self_consistency note for both formalization routes.
   `FixedInterface.inhabited_iff`, backed by actual introduction/evaluation
   terms and their beta roundtrip, shows that `Code(Bottom)` is inhabited
   iff Bottom is: accepted-code reification already carries soundness.
   `BudgetInternalization` rules out the stronger *unbounded full-source*
   literal reifier/evaluator from bounded-literal numeral inputs, regardless
   of their represented values or number. This does not rule out the intended
   Bottom-specific internal soundness or a fixed literal-bounded fragment.
   `FiniteLiteralBank.one_head_for_bounded_sorts` supplies the positive bounded
   sort-leaf primitive with normal literal-zero selectors and one normal
   rank-2 decoder. It does not supply a certificate checker or soundness.
   `NumericLiteralBank` implements a fixed rank-4 head on actual monomorphic
   Church numerals, recovering `U_(min(i,k))`. Its normal numeric inputs have
   literal ceiling zero; the selector carrier depends externally on k.
   Saturation is not an acceptance check. Next connect independently accepted
   bounded sort-rule certificates to this operation, including arbitrary
   admitted trace witnesses rather than standard numerals alone.

7. Construct a full dependent continuation algebra, retaining direct semantic
   indices or otherwise proving original substitution/conversion coherence.
   Local typed handlers and the binder-free CPS fold are now checked; neither
   realizes the full dependent laws. The existing literal CBN type translation
   has unbounded output ranks at source order one, so a rank-fragment-uniform
   CPS interface needs a different organization or additional type bounds.

The focused fold audit checks the seven new source modules and 106 public
endpoints in `FoldAudit`; the main audit alias also retains the complete
compatibility `Audit`. Exact verification is recorded in the newest handoff
entry, not inferred from a previous cached build.
