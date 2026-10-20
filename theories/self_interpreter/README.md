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
size. Internalizing A's interpretation as an object argument remains open.
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

Strong unquotation is checked for a fragment; full original closed PTS is
covered only by the weak semantic-payload construction above. Neither is
yet a full pure-HOAS/PHOAS interpreter. The strong source fragment does not
include the decoder's own polymorphic syntax. Full dependent strong
quotation still needs compatible
translations of contexts, types, substitution, and conversion. Naively
blocking a redex can break conversion in a dependent result type; leaving
annotations unchanged can violate full quotation normality. No theorem or
hypothesis here claims those obligations are solved.

The finite closed strong STLC PHOAS package is now constructed. Next goals
include internalizing its full-simple-type decoder index, extending the
dependent handlers with a compatible source-family/term/type translation,
and proving substitution/conversion coherence. Separately, formalizing the elementary compiler and applying
it to numerical fixed-budget normalization, then constructing typed HOAS
adapters and dependent normal-form reification with sufficient rank/literal
indices remain the complexity route. Raw syntax fidelity and
numerical normalization do not supply that missing typed evaluator.

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
and `docs/direct-r-handoff/verification/self-interpreter-phoas-2026-10-20/`.
New bulky raw logs remain in ignored `_build`; the last directory records
their exact paths, commands and source hashes.

`bash tools/check-local-ci.sh` runs the full staged repository check,
including pristine upstream and this library. Generated caches are not
source artifacts.
