# Indexed self-interpretation research

This separate library, `PTSrk.SelfInterpreter`, investigates Brown and
Palsberg's *Breaking through the Normalization Barrier: A Self-Interpreter
for F-omega* (POPL 2016). See the repository-root research note
[PTS-rk_self_interpreter.tex](../../PTS-rk_self_interpreter.tex) and its
[compiled PDF](../../PTS-rk_self_interpreter.pdf).

The original annotated `PTSrk.Syntax.Term nat`, `Typing.typ`,
`Ranks.RankSorts`, and beta reduction are used throughout. Imports are from
the kernel and `PTSrk.NormalizationComplexity`; there is no dependency on
either arithmetic interpretation or either set model. No PTS rule changes.

## Full dependent numerical-plan-indexed interpretation

The positive construction covers the full original dependent calculus in
well-formed contexts. Its interpreter is indexed by ranks and a finite plan
of numeric equality-layer budgets; the represented type and term are ordinary
object-language arguments. Rank-only uniformity is a separate open question.

The final public endpoints are in `FullDependentInterpreter`:

- `closed_quote`: structural quotation with an automatically computed budget
  from independent original `FullSource` derivation data.
- `every_closed_original`: every original closed typing judgment has normal
  represented type/term programs and a normal originally typed interpreter,
  with literal unreduced-source recovery and original result typing.
- `closed_type_recovers`: executing the represented type program recovers the
  literal source type.
- `closed_injective` / `closed_conversion_injective`: full annotated-source
  fidelity across derivation choices and numerical plans.
- `every_original`: open-source coverage by literal dependent closure and
  reopening; `program_injective` / `program_conversion_injective` retain
  fidelity at a fixed source scope, including different same-length contexts.

`RecursiveQuotation.quote_derivation` implements all six original rules.
It never recursively quotes a synthesized validity/substitution derivation.
Application allocates exactly two actual checked equality-only layers;
conversion repairs independently recovered code endpoints. No source semantic
payload table or target-quotation premise is supplied. The interpreter selects
the actual PHOAS program and RUNS it; the extra raw HOAS tag supplies fidelity.

The construction combines these checked components:

- `OpenTelescopeRecovery`, `ContextualTelescopeRun` and
  `ConcreteContextualBeta`: arbitrary open bodies, literal annotated closure
  recovery, independent original typing and actual finite-field application.
- `OriginalTypecheck` and `BoundedSyntaxEnumeration`: executable original
  typing checks with soundness/completeness, and independent finite syntax
  enumeration including annotations.
- `RealizedEquality`, `ContextualEqualityRealizer`,
  `ContextualEqualityExtension`, `CodeAlignment`, `CheckedEqualityFields`
  and `CheckedContextualFields`: equality-only realized extensions,
  normal actual closed erasers, executable finite lookup and literal payload
  recovery. Payload values are not precomputed by this construction.
- `SourceValidity`, `QuotationTree`, `QuotationCache`,
  `QuotationViewRenaming` and `QuotationViewSubstitution`: original validity
  data and finite typed Pi-constructor views, structurally substituted while
  retaining literal root caches. A variable-to-Pi replacement uses stored
  argument shape, not a recursive quotation of synthesized type derivations.
- `TelescopeInstantiation` and `DependentProgramDecoder`: actual ordinary
  arguments P:Pi Sig.C and Q:Pi Sig.El(P Sig), a normal originally typed
  decoder returning Q idfill, exact formation rank and literal closure
  recovery. Generic typed packaging and fixed-signature closure injectivity
  are proved; all-source quotation is not assumed or established by them.

`LocalQuotationSpine`/`LocalSpineNaturality` retain literal local contexts as
the global signature grows. `LocalCodeAlignment`, `ApplicationQuotation` and
`FullQuotation` supply the actual state-threading/repair operations.
`FaithfulProgramDecoder`, `ClosedQuotationPackage`, `NormalEqualityFill` and
`IndexedProgramInterpreter` close the full source construction with independently
derived normal signature/filling values. `SourceClosure` handles open inputs.

The external plan contains only numeric length/node/literal bounds, not source
syntax or a derivation. Its length and bounds may grow with that derivation;
no rank-only fragment-uniform decoder or practical enumeration cost is proved.
The actual proof-erased OCaml sort path has been tested, including normal
type/term programs; this is not a general runtime benchmark or a direct
`vm_compute` claim for dependent records. Own scoped checks and the final fresh
audit/CI record are under
`docs/direct-r-handoff/verification/self-interpreter-open-telescope-2026-10-21`.
The complete local CI has passed all 226 stages. The fresh build reports
2229 closed self-interpreter assumption reports plus the unchanged upstream
normalization report. Recursive kernel/pristine comparisons, frozen original
source checks and all 110 source-manifest stability checks pass.

## Complexity motivation and full-PTS results

For fixed redex bound `d`, the existing full-PTS normalizer has the checked
operation-cost bound `tower (2*d+1) (nodes t+5*d+2)`. Every closed originally
typed term has the computable sufficient bound
`conservativeRank t = 1 + maxRankLiteral t + nodes t`. This motivates an
externally indexed numeric self-reducer: implement the fixed-budget
normalization algorithm using non-uniform elementary representability.
The latter is theorem `non-uniform-rep` in the manuscript, NOT yet a Rocq
compiler theorem; `latex/ROCQ_REFERENCES.md` records that distinction.
The note states the numeric construction conditionally, without adding an
axiom. Numeric code-to-code computation does not supply dependent unquotation.

`RankedNormalization.v` supplies executable metalevel normalization followed
by raw HOAS quotation, for the full original annotated PTS. Its automatic
variant covers every closed original typed term without a supplied budget
or success premise. `automatic_quote_conversion_iff` says the resulting
canonical codes are convertible exactly when their carrier ranks agree and
their sources are beta-convertible. Unlike raw quotation, this intentionally
forgets distinctions between convertible syntax. Original source-type
preservation, normalization-stage costs and HOAS output-size bounds are
proved separately; output-size bounds are not runtime charges.

`LiteralObstruction.v` proves that a raw HOAS quote at carrier rank `r`
contains no literal sort label greater than `r` (indeed its maximum is `r`).
Beta reduction cannot create a larger literal label. Hence a fixed raw
head cannot decode the quotes of all `U_k`, even with ordinary type
argument `U_0`: these sources all have redex bound zero and result-type
rank zero. This excludes indexing that decoder by ONLY those two bounds.
It does not exclude an additional literal ceiling, the conservative bound
which includes literals, or literal-bearing semantic payloads.

`WeakFullInterpretation.v` constructs an actual **full closed weak
semantic-payload interpretation**. For `t:A`, its executable external quoter
normalizes `t` and `A`, then forms the normal package

```text
C_r = ChurchSyntax.code_type r 0
W_r(A) = (A -> C_r -> A) -> A
Q_r(t:A) = lambda h:nf(A)->C_r->nf(A). h (nf t) (ChurchSyntax.quote r t)
WDec_(r,s) = lambda A:U_s. lambda q:W_r(A). q (lambda x:A. lambda c:C_r. x)
```

`full_closed_weak_interpretation` covers EVERY closed original judgment
`t:A`, obtains the exact sort `A:U_s` from original validity, types the
normal package and the decoder in the unchanged PTS, and proves
`WDec_(r,s) (nf A) Q_r(t:A) ->* nf(t)`, convertible to `t` and originally
typed at `A`. The decoder type has exact rank `max(s+3,r+6)`.
`quote_conversion_injective` separately retains exact annotated source-term
syntax across convertible packages, even with different supplied source
types. It does not claim injectivity of the supplied derivation/type.

The decoder performs five administrative beta steps and **ignores its HOAS
tag**: external quotation already computed the semantic value. This is a
faithful normal weak representation covering full dependent syntax, not an
internal evaluator of pure HOAS, and not strong recovery of the original
unreduced source. It needs no elementary-representability premise. The
remaining computational challenge is replacing the supplied value with an
internal fixed-budget normalizer and a typed dependent reifier.

## Full dependent canonical contexts and hereditary indices

`OpenCanonical.v` extends automatic normalization to every originally typed
open term. Its computable budget uses the maximum declaration literal/node
counts together with those of the input. `nf_correct` proves normalization,
reduction and original typing from original well-formedness and typing alone.
`nf_conversion_iff` characterizes equality of normal forms by original beta
conversion, even across valid contexts at the same scope. This is equality
of scoped syntax, not equality of variable meanings in different contexts.

`CanonicalSubstitution.v` defines `hsubst D sigma t = nf D (replace sigma t)`.
It proves that pointwise normalization preserves actual original `TypedSub`,
including the dependent lookup types. `hereditary_substitution` gives

```text
nf D (replace sigma t) =
nf D (replace (fun i => nf D (sigma i)) (nf G t)).
```

Identity/composition and conversion coherence are checked.
`hsubst_canonical_typed` normalizes both term and dependent result type using
original validity's exact sort witness, without cumulativity.

`CanonicalContexts.v` normalizes each declaration in its original prefix.
It constructs original well-formedness and identity typed substitutions in
both directions. `normalize_typing_iff` retains the literal original term
and type, including annotations. Declaration normality, idempotence, actual
context/index reduction and agreement of term normal forms are proved.

`CanonicalTypeIndex.v` separates faithful `quote t` from canonical
`quote (nf G A)`. Both are normal closed homogeneous HOAS codes. The latter
identifies exactly original conversion on originally typed inputs and obeys
the hereditary substitution/composition equations. A checked pair of distinct
convertible types has different faithful codes but equal canonical indices.
A typed open regression shows why the outer normalization is essential:
normal `f U0` with normal substitution `f := lambda X:U0.X` becomes a redex.

These results cover the FULL original dependent calculus, not a simply typed
source subset. They are executable metalevel syntax operations. They do not
yet construct a PTS program performing code substitution, an internal typed
`El` operation, or a dependent PHOAS quoter over abstract represented domains.
The canonical index is a code for a type, not that source type itself.

## Executable full source evidence and canonical conversion

`FullSource.v` supplies independent derivation data in Type for ALL six
original typing rules, retaining exact scoped contexts, terms, types and
lambda annotations. `step_data` mirrors all seven original reduction
constructors, including annotation and binder-body reduction; `reduction`
is a forward chain and `conversion` a finite forward/backward path.
Conversion contains explicit step data, not an opaque `def_equiv` oracle.
The four iff theorems equate inhabitation with the original judgments,
without adding a wf guard to original sort/variable rules. Completeness
is a proposition about inhabited data, NOT computational extraction from
an erased typing proof. Given data, its traversals are executable.
`source_budget` bounds literal labels throughout judgment contexts/terms/types
and conversion intermediates, plus explicit source-rule formation ranks.
It is not yet a sufficient palette bound for translated dependent quotation.

`FullConversion.v` computes forward certificates for greedy passes and
normalization. `join_attempt` compares computed endpoints by structural
equality and, on success, returns both actual forward traces to their common
term. Success always implies original conversion; normality and completeness
require original wf/typing. `convertibleb_correct` decides conversion of
originally typed endpoints in a well-formed context, while
`every_forward_stage_typed` preserves original typing throughout each trace.
This avoids relying on the possibly untyped intermediates of an arbitrary
source conversion zigzag. It remains metalevel syntax computation, not an
internal equality witness in the Tarski representation.

`CanonicalSource.v` recursively transforms supplied FullSource derivations
in a well-formed original context, replacing each conversion by a computed
forward joining. `canonicalize` preserves the literal source judgment,
including annotations: it changes evidence, not source terms or types.
Its successful data comes from `join_attempt`; original validity's existential
formation rank is eliminated only to refute the impossible failure branch,
never to select computational data from Prop. `canonicalize_certified` proves
normal common endpoints and originally typed stages at EVERY conversion node.
`every_original_typing_has_certified_data` covers all original typings in
well-formed contexts. Certification is proved separately, not assumed in the
source datatype. This supplies canonical source evidence for a future recursive
translation, not that translation or its internal conversion coherence.

`SourceSubstitution.v` computes renaming and simultaneous substitution of
the supplied FullSource step, reduction, conversion and typing data,
including dependent lookup types and all annotations. `substitution_data`
contains actual variable derivations; its inhabitedness is equivalent to
the original `TypedSub` judgment. This equivalence remains in Prop, not an
extraction procedure from erased proofs. `derivation_replace` recursively
constructs the exact substituted derivation and lifts the substitution at
each binder, without adding a well-formedness restriction to the original
deduction domain. `beta_contractum_derivation` computes the literal beta
contractum's derivation from supplied body and argument derivations;
`beta_source_preservation` also uses the supplied domain-formation derivation
to type the redex at the same substituted result type. This is not yet a
Type-valued subject-reduction procedure for an arbitrary typed source step,
nor does it generate target equality witnesses.

## Local Tarski codes, explicit transport and identity realization

`IndexedEquality.v` implements actual original Leibniz transport syntax
`Eq_b(A,u,v) = Pi P:(A->U_b). P u -> P v`, with exact sort
`max(a+2,b+1)` when `A:U_a`. Reflexivity, direct transport typing, beta
recovery, closed reflexivity programs, substitution laws and normality are
proved. No equality primitive, same-level symmetry or cumulativity is added.

`TarskiProducts.v` uses code carriers `C_a:U0` and decoders
`El_a:C_a->U_a`. With `c=max(a+1,b)`, the product constructor type
`Pi A:C_a. (El_a A->C_b)->C_c` has exact sort `U_(a+2)`. Its decoded
dependent product has sort `U_c`. The actual closed normal identity
constructor is `lambda A:U_a. lambda B:A->U_b. Pi x:A.B x`, with original
typing and beta specialization proved independently of an arbitrary algebra.

`TarskiUniverses.v` gives the law `Eq_1(U0,El_0 u_a,C_a):U2`, substitution
naturality, and actual normal closed identity witnesses at EVERY external
rank: `C_a=U_a`, `El_0=id_0`, `u_a=U_a`. These are all-index original PTS
inhabitants, not finite examples or native arithmetic witnesses.

`TarskiCasts.v` constructs both cast directions from
`e:Eq_(c+1)(U_c,X,Y)`. Arrow motives `X->T` and `T->X`, applied to `id_X`,
give `X->Y` and `Y->X`; predicate rank c+1 and law sort c+2 are explicit.
The dependent product law connects `X=Pi x:El_a A.El_b(B x)` and
`Y=El_c(p A B)`. Casted Abs/App are directly originally typed, and universe
casts use the same interface at c=0. Neutral casts of normal inputs are
normal; reflexivity casts beta-reduce to their literal arguments.

`TarskiIdentity.v` constructs the actual product-law witness from reflexivity
at the common product reduct. It proves original identity-specialized Abs/App
typing and strong beta recovery to literal `f` / `f u`, without eta or any
precomputed normal semantic payload. `ClosedTarskiCasts.v` closes the generic
cast programs over X, Y and e: the programs are normal, their types have rank
c+3, and direct application typing and reflexivity computation are checked.

These are LOCAL object-language components, not by themselves a complete
full-PTS PHOAS representation. Their finite context and actual identity
instantiation are constructed below. The final numerical-plan construction
adds derivation-directed dependent quotation, generated source-conversion
witnesses, full quotation-annotation normality and all-source coverage.
Existing faithful raw syntax and STLC PHOAS injectivity results are retained;
the new full-source fidelity theorem uses an explicit raw HOAS tag.
Neutral cast roundtrips are not definitional equalities. Pointwise internal
equality of families cannot simply be used as equality of host functions.

`EtaBoundary.v` checks that distinction: closed normal `lambda f:D.f` and
`lambda f:D.lambda x:U0.f x`, D=U0->U0, have the same original type and
pointwise beta behavior but are not beta-convertible. The dependent types
`K f` and `K (lambda x:U0.f x)` in an actual well-formed original context
are also normal, typed and nonconvertible. This rules out silently adding
eta conversion, not all full dependent PHOAS encodings or all internal
equality witnesses.

## Finite dependent Tarski signature and constructive instantiation

`TarskiLawFamily.v` binds A and its genuinely dependent code family B in
one polymorphic product-law declaration per rank pair. Its type has exact
sort c+2, c=max(a+1,b); direct typing of the two applications is proved.
The closed normal identity inhabitant is lambda A:Ua.lambda B:A->Ub.
refl_(c+1)(Uc,Pi x:A.Bx). Original conversion gives the actual specialized
signature, and two applications recover the literal local identity law.

`TarskiPalette.v` constructs four finite dependent layers, each indexed by
r=0..k+1: carriers C_r, decoders El_r, universe codes u_r and universe-law
witnesses. The generic block/fill infrastructure computes actual original
contexts and substitutions with scope-correct weakening, lookup, normality
and original typing proofs. The base has exactly 4*(k+2) declarations.

`TarskiSignature.v` adds (k+1)^2 product constructors and as many
polymorphic law families, one of each for every a,b<=k. Carrier ranks
through k+1 suffice because max(a+1,b)<=k+1 for those pairs. No closure
under products at ALL available ranks is asserted. The final context has
exactly 4*(k+2)+2*(k+1)^2 declarations; it is originally well-formed and
all declarations are normal. All six field classes have bounded original
lookup typings. Out-of-range fallback selectors have no promised contract.

The executable `fill` supplies actual identity terms for EVERY field,
including the universe and polymorphic product laws. `fill_typed` proves
the original typed-substitution judgment into any target context without
an algebra-existence premise. Field substitution equations are literal.
The telescope close/run contracts provide originally typed closed bodies
and directly typed application to these identity arguments, with actual
substitution recovery. They are generic packaging theorems, not a quoter
whose source domain has been strengthened by the desired result.

`TarskiOperations.v` uses the actual finite law fields: product evidence
is computed as law_ab A B, not supplied independently at each operation.
It proves original typing of product codes, decoded/encoded products,
casted abstraction and casted application. Actual substitution by fill
recovers the literal dependent product, identity law, substituted function
and its application. This neither eta-expands nor projects a precomputed
normal source payload. This original constructor's normality theorem needs
normal decoded annotations: a normal lambda-valued family can introduce an
administrative redex. The smart local constructor below removes that extra
premise; the earlier theorem is retained unchanged.

`IndexedCoherence.v` constructs original equality composition at the SAME
predicate level b, and congruence for an ordinary nondependent map A->B.
Replacement naturality and beta equations are proved. Composition of two
reflexivity witnesses and mapping reflexivity recover literal reflexivity.
Arbitrary-evidence identity equations are only claimed after applying to a
motive and argument, not via eta contraction. This is not dependent function
extensionality or a proof of all source-conversion coherence.

## Sort quotations, dependent scopes and smart local binders

`TarskiSorts.v` constructs `code_to_term` from C_r to El_0(u_r) using the
backward universe cast, and `term_to_code` in the forward direction. They
are originally typed, preserve normal inputs, and actual identity replacement
recovers the literal substituted input. `sort_quote k r` applies the rank-ZERO
code-to-term cast to u_r: this represents the original axiom U_r:U0 and has
type El_0(u_0). Using law_r instead would have the wrong input carrier.
For r<=k+1 the quote is normal and recovers U_r. `closed_sort_quote_typed`
and `closed_sort_quote_normal` close it over the finite signature;
`closed_sort_run_typed` directly types its actual identity application at U0,
and `closed_sort_quote_recovers` reduces that application to literal U_r.
Thus every source sort has a finite closed representation; this is not
yet coverage of every original source derivation.

`TarskiContext.v` constructs actual dependent context extensions of the
finite signature. A `spine` carries independently proved formation of each
new declaration; `spine_environment` embeds all signature variables with
their original typings. `identity_context` and `identity_fill` specialize
the signature while retaining each newly bound variable. `identity_fill_typed`
is an original typed substitution, built by lifting at every binder;
`identity_fill_new` fixes the fresh variable and `identity_fill_weakening`
commutes with shifting older terms. Both contexts are well-formed, inherited
fields retain their exact identity equations, and `identity_typing` transports
original typings. Normality of the abstract extension requires normal added
declarations; the specialized context is not asserted normal. The signature
embedding is injective. Local product/law/Abs/App APIs admit arbitrary terms
in the enlarged scope, including fresh dependent variables, and prove original
typing and actual identity recovery. This is scope infrastructure, not a
source-context translation supplied by an assumed quotation theorem.

`TarskiBinders.v` replaces application of a family to the fresh variable by
`bound_apply B`: the literal body if B is a lambda, otherwise `(shift B) 0`.
`bound_apply_reduces` contracts only this administrative redex;
`bound_apply_normal` preserves full normality, including annotations.
`bound_apply_rename` is exact, while `bound_apply_replace` correctly states
one-way reduction, not equality, when replacement makes a neutral family
lambda-headed. The smart decoded product uses this normal family body.
Existing law evidence is retyped by original conversion; the smart Abs/App
are originally typed under the original input typing and rank premises.
Normal inputs suffice for normal output without a separate
decoded-annotation-normality premise. Actual identity replacement recovers
the literal substituted function and its application.

`binder_typed` introduces a genuinely dependent family and term body under
x:El_a A. `binder_normal` requires normal A, family body and term body.
`binder_recovers` returns the literal substituted underlying lambda, whose
annotation is still `replace fill (El_a A)` and whose body uses the lifted
substitution; it does not state recovery with an already contracted annotation.
For fixed k,a,b, `binder_inputs_injective` recovers all three supplied inputs
from equality of binder terms. `binder_conversion_injective` gives the same
conclusion from beta conversion when all inputs are normal. These are LOCAL
fidelity and normality results, not properties of a full derivation quoter.
The earlier module uses fixed signature scope; `ScopedTarski.v` now lifts
the smart operations to ANY typed `TarskiContext.environment`. Their inputs
may mention all current dependent binders. Original typings use wf, rank
bounds and independent input typings; normality follows separately from
normal inputs. Smart binder input/conversion injectivity remains local at
fixed environment and rank indices. Sort quotations and both universe views
are available at the same arbitrary scopes. Exact renaming and weakening
laws are proved. The underlying `bound_apply` replacement law is still
one-way reduction; literal substitution naturality for the whole smart
translation is not asserted.

For a concrete `TarskiContext.spine`, scoped Abs/App, binders and universe
views recover their actual identity-substituted inputs. The additional
`binder_annotation_recovers` contracts the identity decoder in the domain,
returning `lambda (replace identity_fill A). replace (transpose identity_fill) body`.
`extend_code` constructs the next dependent spine from an independently
typed code A; its inherited environment is weakened and its fill is exactly
lifted. Normal code inputs preserve normal declarations.
`nested_binder_typed` connects the binder to that actual next environment,
so the operation can be iterated. This removes the old fixed-scope interface
restriction; it does not supply the missing full source-derivation quoter.

`TarskiRoundtrip.v` checks a precise remaining limitation. In an actual
well-formed original context S:U_c,T:U_c,e:Eq_(c+1)(U_c,S,T),x:S,
`backward e (forward e x)` and x are typed, normal and distinct, hence not
beta-convertible. Adding K:S->U0 gives normal, typed, nonconvertible dependent
indices at those arguments. At actual reflexivity evidence the roundtrip
does reduce to x. This rules out definitional cancellation of the EXISTING
neutral casts, not internal equality witnesses, independently realized extra
coherence fields, alternative casts or full dependent PHOAS.

## Finite internal beta-law fields

`TarskiBeta.v` constructs an additional polymorphic beta-law TYPE. Writing
X=Pi x:El_a A.El_b(B x) and e=law_ab A B, its conclusion for f:X and
u:El_a A is `Eq_d(El_b(B u), App_e(Abs_e f,u), f u)`.
The complete field binds A,B,f,u and has formation rank
`max(c+1,max(b+2,d+1))`, where c=max(a+1,b) and d is the explicitly chosen
predicate rank. Formation, substitution naturality and four-argument
application typing are proved in the original PTS.
The closed normal `identity_family` independently inhabits the actual
identity-specialized field type; its four applications recover the literal
reflexivity witness at B u and f u. This is not a derivation of the new law
from arbitrary old product-law evidence, or definitional neutral-cast
cancellation. It adds independently realized object arguments, not a new
kernel equality rule or axiom.

`TarskiBetaSignature.v` appends one such field for each a,b,d<=k to the
unchanged finite Tarski signature. Its actual original context has exactly
`4*(k+2)+2*(k+1)^2+(k+1)^3` declarations and is well-formed and normal.
Bounded field lookup typings and the concrete identity `fill_typed` are
proved; no algebra-existence premise supplies the beta witnesses.
`apply_beta_typed` specializes the field using independently typed A,B,f,u;
`apply_beta_normal` preserves normal inputs. `apply_beta_recovers` proves
actual replacement by fill reduces the applied witness to reflexivity at
the literal substituted B u and f u. Predicate levels outside the selected
finite ceiling are not silently available.

The extension's `environment` is an actual typed inherited-variable map,
so ScopedTarski typing and normality apply in this larger context. Its
`environment_fill` and `fill_inherited` retain the original field identities.
This environment bridge alone is not the concrete `TarskiContext.spine`
required by that module's recovery theorems; their recovery specialization
to this enlarged signature has not been inferred automatically.
These local beta fields do not by themselves generate all source-conversion
witnesses or global quotation/substitution coherence. The next components
provide explicit internal congruence constructions with narrower contracts.

## Internal dependent equality and structural binder congruence

`IndexedEqualityLevels.v` constructs level-changing equality programs.
For A:U_a and `h=max(a+2,d+1)`, an actual witness `Eq_h(A,u,v)` produces
either `Eq_d(A,u,v)` or `Eq_d(A,v,u)`. The motives are respectively
`lambda x:A.Eq_d(A,u,x)` and `lambda x:A.Eq_d(A,x,u)`, with independently
typed reflexivity seeds. This is a constructed change of predicate level,
not cumulativity or same-level symmetry. `join_typed` combines high-level
witnesses from u and v to a common endpoint w into equality from u to v.
For a type law, this reversal construction uses input predicate c+2 to
produce output predicate c+1, since U_c:U0.
Replacement is literal and actual reflexivity inputs beta-recover literal
reflexivity. Normality requires normal inputs with non-lambda proof heads.

`DependentEquality.v` introduces synchronized graph equality for
A:U_a and B:A->U_b:

```text
GraphEq_d(A,B,u,y,v,z) = Pi P:(Pi x:A.B x->U_d). P u y -> P v z.
```

Its predicate type has rank max(a+1,b+1); the graph equality has exact rank
max(a+2,b+2,d+1). For f:Pi x:A.B x and e:Eq_d(A,u,v), the actual term
`lambda P.e(lambda x:A.P x (f x))` produces graph equality between
(u,f u) and (v,f v), at the SAME input predicate level d. Its direct
original typing tracks values in different dependent fibers together.
`fiber_congruence` embeds ordinary `Eq_d(B u,y,z)` at one fixed index by
`lambda P.e(P u)`. Graph transport, exact substitution laws and literal
reflexivity computations are proved. Normality requires a normal
non-lambda family B, and suitable non-lambda function/proof inputs:
normal B alone does not make the annotation B x normal. These witnesses
do not prove agreement with an independently chosen transport from B u
to B v, or supply a proof-dependent eliminator or function extensionality.

`BinderCongruence.v` handles a structurally shared map, rather than arbitrary
pointwise evidence. Its independently typed body is scoped under z:D and
x:X and may use both variables; X and the result carrier C do not depend
on z. The original term `lambda z:D.lambda x:X.body` maps an equality
between u,v:D, supplied OUTSIDE the x binder, to equality between the two
literal substituted lambda families. Applying the actual product constructor
p A then gives equality of dependent product codes. Original typings, exact
substitution, reflexivity recovery and the identity-product specialization
are checked. This does not turn unrelated proofs e_x into function equality
or solve arbitrary binder conversion. These programs can contain
administrative beta redexes; no general normality is claimed.

`TarskiGraphBeta.v` connects graph equality to the ACTUAL finite beta fields.
Its decoded family is `F=lambda x:El_a A.El_b(B x)`. The independently
proved reduction `F u -> El_b(B u)` retypes the bound predicate application,
allowing `TarskiBetaSignature.apply_beta` to feed `fiber_congruence` without
assuming another equality witness. `beta_graph_typed` proves original typing
of that computed term, and `filled_beta_graph_typed` uses the existing actual
identity TypedSub. `beta_graph_recovers` reduces the identity-filled program
to graph reflexivity at the literal substituted u and f u, retaining the
literally substituted domain and lambda family. No eta contraction or external
normalization occurs. The lambda-valued family does not satisfy the generic
graph-normality guard; no normality claim is made for this specialization.

## Contextual beta laws over arbitrary dependent telescopes

`ContextualTelescope.v` supplies executable dependent telescopes over any
original base context, indexed by an explicit vector `rs` of declaration
ranks. `formed` contains only the original declaration-sorting judgments;
it assumes no quotation or coherence property. Products and lambdas retain
every literal annotation. Writing `R(rs,b)=max(b,max({0} union {r+1 | r in rs}))`,
`close_type_sort` proves exact formation rank R(rs,b). Original closure
typing, lifted renaming/substitution, reduction and annotation-sensitive
normality are checked. A closure of a normal body is normal exactly when
all its domain annotations are normal.

`ContextualBeta.v` constructs the specific equation under such a telescope
Delta:

```text
Eq_d(Pi Delta.El_b(B u),
     lambda Delta.castApp(e,castAbs(e,f),u),
     lambda Delta.f u).
```

Its exact formation rank is `max(R(rs,b)+2,d+1)`. Original formation follows
from the independent original input typings. At the actual identity
interpretation both endpoints reduce to the same literal multi-lambda.
The module independently constructs and types reflexivity there, then uses
original TYPE conversion to assign the specialized equation type. This is
not subject expansion, eta, or a rule turning arbitrary pointwise equality
into function equality. Normality has explicit annotation/body guards.

`TelescopeBetaFamily.v` binds four actual object arguments A,B,f,u, each
abstracted over Delta. Their uses are the actual application spines to all
fresh telescope variables; the product evidence is the existing law family
applied to those A/B values. The complete family has exact formation rank
`max(R(rs,0)+2,a+2,b+2,d+1)`. Its identity program is constructed with plain
annotations and ends in reflexivity at `lambda Delta.f_Delta u_Delta`.
`identity_family_typed`, `identity_family_normal` and
`identity_family_specializes` separately prove original typing, normality
under normal domain annotations, and literal recovery after four applications.
Substitution naturality is exact. No concrete telescope is assumed normal
merely because it is originally formed.

`UniformTelescope.v` removes concrete domain syntax from the external field
index. `parameters` binds one domain-family variable X_i for each r_i in rs;
its type is `Pi previous_domains.U_(r_i)`. `domains` uses the neutral spine
`X_i previous_variables` as its next domain. Both generated telescopes have
original formation and normal annotations for EVERY rank vector. Parameter
declaration i has formation rank `R(prefix_i,0)`, since `U_(r_i):U_0`.
The number of parameters is exactly the vector length. Literal application,
renaming/substitution and beta recovery of telescope lambda closures are
proved; no concrete source annotations are stored as external field indices.

`UniformTelescopeRecovery.v` proves exact generator naturality and computes
`realize W` from ANY concrete telescope W. Each parameter value is its actual
declaration lambda-closed over the preceding literal domains. With only
original formation of W, `realize_correct` gives an original TypedSub from
the generated parameter context to the original base context, and
annotation-wise forward beta recovery of the instantiated domains to W
in the accumulated scope order.
The scope transports change only Rocq indices, not PTS constructors.
`realize_closure_recovers` recovers the exact original product closure
ending in any U_s. This is constructive concrete-domain coverage; an exported
arbitrary open-body/lambda-closure transport is still a separate obligation.

`UniformContextualBeta.v` abstracts the four-argument family over those
normal domain parameters. The field depends externally ONLY on rs,a,b,d,
not on domain terms. It has an independently typed CLOSED NORMAL identity
program, exact replacement/renaming laws for its type, and substitution
invariance of its identity value. If all entries of rs and a,b,d are at most
k, its formation rank is at most k+3. This bounds the actual proved rank;
it does not retype the field in U_(k+3) by nonexistent cumulativity.

`ContextualBudgets.v` computes all vectors of length at most L with entries
at most k. `vectors_spec` proves completeness and `vectors_length` gives
`sum_(j=0..L) (k+1)^j` entries. `rank_does_not_bound_length` proves the need
for a separate length bound: arbitrarily long nonempty zero-rank vectors
still have closure rank one. Every finite vector has a computed sufficient
length/rank budget.

`TelescopeBetaSignature.v` adds exactly
`sum_(j=0..L) (k+1)^j * (k+1)^3` contextual fields to the unchanged finite
local-beta signature. Executable lookup retrieves each bounded vector and
triple a,b,d. The actual context is originally well-formed with normal
declarations. `contextual_typed`, `fill_contextual` and `fill_typed` prove
bounded lookup typing, literal identity-field replacement and the actual
original identity TypedSub, without an algebra-existence premise.
Every added declaration's formation rank is at most k+3, independently of L.
`every_descriptor_has_typed_field` computes a sufficient budget for any
finite vector/triple; this is descriptor coverage, not coverage of translated
full source derivations. Closed packaging preserves original typing and
normality, and actual identity application is directly typed and recovers
the literal substituted body. These packaging contracts do not by themselves
instantiate arbitrary open payloads at the generated domains.

The separate one-binder `ContextualBetaFamily.v` explicitly binds X:U_s
before A,B,f,u and has exact rank `max(s+3,a+2,b+2,d+1)`. Its closed normal
identity program and five-argument literal reflexivity computation are
checked. `ContextualBetaSignature.v` appends `(k+1)^4` such fields to the
local-beta signature, with actual typed identity fill and applied-field
typing, normality and recovery. At fixed indices,
`apply_contextual_inputs_injective` recovers all five supplied arguments;
`apply_contextual_conversion_injective` does so from beta conversion when
both input tuples are normal. This is LOCAL fidelity of the applied field,
not a full dependent quotation theorem.

`RealizedSignature.v` separately packages any finite list of independently
sorted field families over a base context, supplied with an ACTUAL closed
typed base substitution and independently typed closed field values.
Formation, lookup, typed instantiation and closure/application recovery are
checked; normality has separate normal-annotation/value premises. It is a
reusable packaging theorem, not a generator of those values or an assumed
source interpreter.

These eleven modules establish formation, independent identity realization,
normal uniform programs and finite integration of the contextual cast-beta
family. These modules alone do not supply general open-body instantiation,
composition with arbitrary source-reduction witnesses or general dependent
function congruence. The later open-telescope and checked equality-layer
construction supplies the particular transport and repair operations used
by full quotation, without assuming general function extensionality.

`RecursiveQuotation` now assembles the checked components into a translation
of all original source derivations. `FullDependentInterpreter` establishes
normality, strong recovery and source-syntax injectivity. Its computed budget
also includes source literal labels; result-type rank alone is insufficient.

## The uniform obstruction

`RankObstruction.v` proves `no_universal_fixed_head_evaluator`: no one
closed typed PTS term can recover every closed typed PTS term, up to beta
conversion, by arbitrary finite typed application spines. Applications
cannot increase the rank of a term's TYPE, but explicit closed inhabitants
`rank_value r : rank_type r` exist at every type rank `r`.

The specification even permits arbitrary externally chosen code and type
arguments, with arbitrary argument counts. It does not assume a fixed code
type, effective quotation, normality, or injectivity. The result excludes
the actual fixed-unquote interface of the paper. It does not exclude
externally indexed program families, arbitrary externally added abstraction
wrappers, or other observational notions of recovery. The paper's informal
allowance of implicit type abstractions is therefore not categorically
refuted by this theorem.

## Positive components

`ChurchSyntax.v` supplies an executable Church **raw HOAS** encoding of
every original annotated `Term nat m`, for terms and types alike. Source
variables become host variables, and each product/lambda body becomes a host
function `X -> X`; its original annotation remains a separate constructor
argument. No source typing, normalization or rank bound is required.
The carrier `X : U_r` and six algebra arguments (zero, successor, sort,
product, lambda, application) are abstracted by seven original lambdas;
another `m` carrier binders close the source variables. Product and lambda
handlers have type `X -> (X -> X) -> X`, and the application handler has type
`X -> X -> X`. The actual closed `quote r t` is beta-normal and has type
`code_type r m : U_(r+3)`; `every_original_term_has_church_code` bundles these
three proved judgments. Source sort labels become numeral data: they need
not be below `r`. This replaces the earlier first-order Church AST encoding.

`ChurchSyntaxFaithful.v` proves exact syntax fidelity at a fixed source scope.
`quote_conversion_iff` states that `quote r t` and `quote s u` are beta
convertible exactly when `r=s` and `t=u` as original annotated syntax. This
is stronger than recovery up to conversion; reducible annotations are not
identified with their contracta. The source scope determines the number of
additional carrier binders; the fidelity theorem compares equal scopes.

`ChurchSyntaxFold.v` proves `run_fold`: application of a quote to its carrier
and six actual algebra arguments reduces to the structural HOAS
`fold_closure`, retaining the source-variable binders. For closed source
syntax these extra binders disappear, leaving the literal `ast_fold`.
`run_typing` derives the original typing of that application directly from
the carrier/handler typings, not by subject expansion from the reduct.
These are raw syntax folds, not dependent typed evaluators. Target typing at
one carrier is not the paper's intrinsically source-type-indexed HOAS:
`code_type r m` does not depend on the represented source's type. Nor does
exact raw fidelity supply the paper's conversion-preserving type
interpretation. Instantiating the carrier by `code_type s m` uses the external
index `r=s+3`; there is no cumulativity or internal rank polymorphism.

`BrownPalsberg.v` analyzes the paper's literal single-family interface
separately. If `F : U_a -> U_b`, forming `F (F A -> F B)` forces `a=b+1`,
whereas admitting the type-level identity at that same family type forces
`a=b`. `no_literal_interface` proves the contradiction in the original
typing judgment, including arbitrary alternate typing/conversion derivations.
This excludes that specific interface, not raw HOAS or externally indexed
PHOAS families.

The same module proves positive **indexed PHOAS components**, separate from
the raw-HOAS encoding. `pretype` and `interpreted_type` translate independent
ChurchSTLC types using a family `F_r : U_r -> U_r` at each needed external
rank. `pretype_sort_bounded` and `interpreted_type_finite_palette` show only
indices up to the source type's order are used;
`interpreted_type_identity_recovers` proves strong recovery at the identity
families. `indexed_handler_type_sorts` constructs well-sorted polymorphic
Abs/App types using the three family indices `a`, `b`, and `max(a+1,b)`.
`indexed_identity_handlers_typing` supplies actual closed original PTS
identity-specialized handlers, and `indexed_abs_recovers` /
`indexed_app_recovers` prove their beta behavior. These components do not by
themselves construct a complete closed source-indexed quotation package.

`TypedHOAS.v` adds an executable **source-type-indexed PHOAS prequotation**
for the independent ChurchSTLC derivation data. Unlike the raw-HOAS code,
`prequote` has result type `interpreted_type F o A`, indexed by the actual
source type `A`. Abstraction uses a target function on the interpreted
domain, and application uses its separately typed App operation.
`prequote_typed` proves original typing from the family, operation and source
environment typings. `prequote_bounded_typed` restricts family/operation
obligations to a computed finite rank budget, including abstraction
annotations; it does not construct the corresponding package.
`prequote_substitution` proves literal simultaneous-replacement naturality,
and `substitution_identity_recovers` proves strong recovery after replacement
by the actual indexed identity families and handlers. This is an actual
substitution theorem, not merely regeneration of syntax with different
external parameters.

`TypedHOASFaithful.v` proves full `prequote_normal` when families and Abs/App
operations are represented by neutral variables. Its structural eraser
recovers the exact renamed original source, including annotations.
`prequote_injective` and `prequote_conversion_injective` therefore recover
literal source equality under an injective variable embedding, even across
different derivations and result types. These are generic variable-palette
results: this module does not construct a finite originally typed neutral
package or claim its closed existence.

`TypedHOASAlgebra.v` proves `actual_identity_cases_typed` for the real
polymorphic indexed handlers, instantiated by original application rules.
`typed_identity_interpretation` combines original typing and strong recovery
for the computed identity-specialized prequotation, assuming only the
independent source derivation and original ground/source-context typings.
This specialization contains beta redexes; it is not asserted normal.
Thus the generic normality/fidelity results and the concrete typed recovery
result were checked separately. The new finite construction below now
connects them for the independent STLC source.

## Finite closed indexed PHOAS

`PHOASAlgebra.v` specializes one polymorphic Abs/App pair per rank pair at
the two source pretypes. It proves original typing of those applications.
`PHOASFaithful.v` adjusts the structural eraser for their two explicit type
arguments and proves full normality, literal syntax fidelity and conversion
injectivity. No parametricity axiom or no-junk theorem is assumed.

`PHOASPackage.v` constructs an actual finite context for each budget `k`:
one ground parameter, `k+2` families for ranks `0..k+1`, and two handlers
for each pair `0<=a,b<=k`. The extra family supports pairs with arrow rank
`k+1`. All declaration normality, original well-formedness, lookup typings
and identity instantiation typings are proved. Infinitely many simple type
shapes at each rank are covered by polymorphic specialization, not infinitely
many object-language parameters.

For a term-closed independent source derivation `D:t:A`, `quote k D` closes
the actual prequote over this context. `quote_typed` needs only the computed
`TypedHOAS.rank_budget D <= k`; `quote_normal` and
`quote_conversion_injective` retain full normality and exact annotated
source syntax. `every_source_quote` covers every independent ChurchSTLC
`has_type` judgment at some sufficient computed budget.

`PHOASTelescope.v` implements finite dependent closure and actual application
using original contexts/lambdas/products. `run_typing` derives application
typing directly from a typed argument substitution, not subject expansion.
`PHOASRecovery.v` requires identity laws only within the used rank budget;
`quoted_substitution_recovers` proves strong recovery after actual replacement
of the generated syntax. No laws on fallback parameters outside the palette
are assumed.

`PHOASDecoder.v` constructs a real CLOSED decoder. Its
`closed_phoas_interpretation` bundles normal closed quotation, original
quote/decoder/application typing and strong reduction to the original
source with the ground abstraction inside the decoder. Unlike the earlier
weak full-PTS packet, this quote contains no precomputed normal semantic
payload. A reducible-source regression computes budget one and a normal
quote, then strongly recovers the still-reducible source.

The decoder is externally indexed by **budget k and full simple type A**,
not merely the result type's order. At fixed `(k,A)` it is the same original
program for all independent source derivations within budget, regardless of
size. This earlier decoder does not internalize A's interpretation as an
object argument; the later dependent program decoder supplies that interface.
Quote/decoder type formation has existential universe witnesses; no exact
closed-form rank bound is claimed by these new package theorems.

`DependentPHOAS.v` separately constructs genuinely dependent local handlers:
for `B : (F_a A) -> U_b`, the product `Pi x:F_a A. F_b(B x)` has rank
`c=max(a+1,b)` and the indexed dependent Abs/App interfaces rank `c+1`.
Actual closed identity handlers inhabit these interfaces and recover `f` /
`f u`; the real applied App term is directly typed at `B u`. The candidate
universe-decoder type `F_0(U_b)->U_b` has rank one and an actual identity
specialization. These facts do not translate arbitrary source families
`B0:A->U_b` into families on `F_a A`, or supply conversion coherence.

`PHOASConversion.v` proves a precise limited obstruction: no normal,
literal-syntax-injective map can also preserve beta conversion on a domain
containing the two distinct original types `(lambda X:U0.X) U0` and `U0`.
They share small fixed rank, literal, size and redex bounds. The same holds
for a faithful code pointwise convertible to a conversion-preserving index
map. It does NOT exclude separate syntax and semantic/canonical indices,
or arbitrary indexed dependent PHOAS. The specialized neutral STLC quoter
also has a concrete checked example where convertible sources yield
nonconvertible codes, as expected from exact fidelity.

## Earlier shallow quotation and decoder infrastructure

`RankedDecoder.v` builds the actual PTS identity and shallow decoder terms:

- `identity_type r : U_(r+1)` and its inhabitant `identity_value r`;
- `representation_type r A = I_r -> A`;
- `decoder r s : Pi A:U_s. (I_r -> A) -> A`, whose TYPE has exact rank
  `max(r+3,s+1)`;
- `typed_ranked_retraction`, recovering any typed raw packet in three
  original beta steps.

Raw packets retain the source redexes. This retraction is not a normal
quotation construction. `decoder_type_not_in_result_universe` proves that
this family member's type cannot inhabit its own output universe `U_s`.

`RankedQuotation.v` gives a genuine quotation construction for the existing
**independent** `ChurchSTLC` source, preserving its annotations:

- `bounded_type` bounds the order of every application FUNCTION type;
  `bounded_type_source` forgets the bound and `every_source_has_budget`
  supplies one for every source derivation. Final result rank alone is
  insufficient. The source domain assumes no quotation or recovery property.
- `quotation_exists`, `quotation_typed`, `quotation_normal`, and
  `quotation_recovery` establish structural quotation with explicitly typed
  neutral blockers and strong original beta recovery after substitution.
- `finite_budget_quotation` constructs the actual finite blocker telescope
  and discharges those blocker assumptions. Blockers are abstracted in
  descending rank order, `k,...,0`, and interpreted by the corresponding
  original identity terms.
- `finite_package_injective` proves syntax-level injectivity at each fixed
  budget using a structural eraser, separately from beta recovery.
- `every_source_has_normal_representation` covers every independent STLC
  derivation at some finite budget.
- `closed_source_normal_representation` adds the ground-type abstraction
  and produces closed original-typed normal codes and strong recovery.

`ExecutableQuotation.v` now makes this separate STLC construction executable:

- `derivation` is independent source evidence in `Type`, indexed by original
  annotated syntax. `source_derivation` proves equivalence between its
  inhabitation and `ChurchSTLC.has_type`. This propositional coverage result
  does not compute derivation data from an erased `Prop` proof.
- `quote_budget`, `prequote`, `quote_at`, `quote`, and `closed_quote` are
  structural computations. The input is a source derivation, not a target
  PTS typing or an assumed quotation witness.
- `quotation_executable` is an exact iff with the existing `quotation`
  relation: relational outputs are precisely outputs of some computational
  derivation whose computed budget is sufficiently small.
- `quote_at_correct` and `closed_quote_correct` prove normality, original
  typing and strong recovery for the actual computed output. The latter
  uses the existing CLOSED decoder with the automatically computed budget.
- `quote_at_injective` and `closed_quote_at_injective` retain exact source
  syntax injectivity at each fixed sufficient budget.
- A reducible-source regression computes budget 1 and a normal closed quote
  using `vm_compute`; a separate theorem recovers the original unreduced
  source, while another computation checks decoder normalization.

No separate extracted command-line quoter or source type-inference frontend
is claimed. The functions are executable in Rocq. Budget and rank indices
are external natural numbers generating syntax, not internal rank polymorphism.
`TelescopeDecoder.v` internalizes telescope interpretation as an actual
closed `family_decoder count start s`, with an exact recursive type-rank
calculation. `fixed_decoder_bounded_quotation` uses the same family member
for every source with budget `k` and result order `s`.

`ClosedDecoder.v` internalizes the ground-type binder as well. The decoder
takes a type family `P : Pi o:U0. U_s` and a CLOSED normal code of type
`Pi o:U0. package_type count start (P o)`. Its body introduces `o` and
interprets the code at `o` with the actual identity terms. Thus
`closed_fixed_decoder_bounded_quotation` proves recovery by application of
one CLOSED decoder to CLOSED arguments, rather than relying on an external
lambda wrapper during evaluation. This still interprets the STLC fragment,
not all original dependent terms or the decoder's own syntax.
`closed_every_source_interpreted` chooses a finite budget for every
independently typed term-closed ChurchSTLC source and applies that closed
decoder to the closed representation.

## Remaining boundary

Full original dependent PTS now has a strong PHOAS-based interpreter family:
its represented type and term programs are normal, evaluation recovers literal
annotated source syntax, and a faithful envelope preserves syntax injectivity.
Open terms are covered by literal dependent closure and reopening. Every
originally typed interpreter member is itself eligible source syntax, possibly
requiring a different or larger numerical index.

The family depends on a finite numerical equality-allocation plan in addition
to ranks. Neither a decoder uniform over an entire rank-bounded fragment nor
same-index self-applicability is established. Enumeration is finite but may be
very large; the extracted sort-path smoke test is not a general complexity or
performance result. A smaller coherence interface and stronger rank-only
uniformity remain research questions.

The independent complexity route still requires a formal elementary compiler
and its application to fixed-budget numerical normalization. Those results
are not premises of the constructed dependent interpreter. Raw syntax fidelity
or numerical normalization alone would not have supplied dependent unquotation;
the actual dependent program and its checked equality repairs do that work.

## Build and audit

Use the [pinned environment](../../docs/DirectR-CI.md): Rocq 9.2.0,
Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2, Dune 3.23.1.

```sh
opam exec -- dune build @theories/self_interpreter/audit
bash tools/build-self-interpreter-note.sh
```

Use a fresh absolute Dune build directory for fresh assumption reports.
New declarations have transitive `Print Assumptions` reports; recursive
kernel inventories are compared with pristine upstream. The context-level
upstream functional-extensionality inventory is distinct from closed
theorem-level reports. Exact verification and intermediate failures are
recorded in `docs/direct-r-handoff/verification/self-interpreter-2026-10-20/`,
`docs/direct-r-handoff/verification/self-interpreter-church-2026-10-20/`,
`docs/direct-r-handoff/verification/self-interpreter-hoas-2026-10-20/`,
`docs/direct-r-handoff/verification/self-interpreter-complexity-2026-10-20/`,
`docs/direct-r-handoff/verification/self-interpreter-phoas-2026-10-20/`,
`docs/direct-r-handoff/verification/self-interpreter-publish-2026-10-20/`,
`docs/direct-r-handoff/verification/self-interpreter-canonical-2026-10-20/`,
`docs/direct-r-handoff/verification/self-interpreter-tarski-2026-10-20/`,
`docs/direct-r-handoff/verification/self-interpreter-signature-2026-10-20/`,
`docs/direct-r-handoff/verification/self-interpreter-binders-2026-10-20/`,
`docs/direct-r-handoff/verification/self-interpreter-conversion-2026-10-21/`,
`docs/direct-r-handoff/verification/self-interpreter-coherence-2026-10-21/`,
and `docs/direct-r-handoff/verification/self-interpreter-contextual-beta-2026-10-21/`.
New bulky raw logs remain in ignored `_build`; the last directory records
their exact paths, commands and source hashes.

`bash tools/check-local-ci.sh` runs the full staged repository check,
including pristine upstream and this library. Generated caches are not
source artifacts.
