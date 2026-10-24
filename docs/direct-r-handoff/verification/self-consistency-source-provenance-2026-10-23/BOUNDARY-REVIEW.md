# Why a local source graph repairs one boundary, not soundness

ComputationBoundary refutes a contract with actual source-generation,
capacity, traversal and execution-typing witnesses but no connection between
the source and its executed operations. For a scoped rejected application q,
Compare(q,q) is an actual true-returning comparison with all those witnesses.

A constructor-by-constructor graph can rule out precisely this mismatch
without assuming evaluator agreement. Its constructors should be indexed by
the original source certificate and context, and fix the residual operation
tree and comparison operands from the source's local fields. Recursive child
graphs fix the subcomputations. Independent graph induction can then prove
agreement with the existing externally executable compiler and hence with
both Boolean results of the unchanged native checker. Completeness constructs
a graph for every source, including well-scoped rejections. Neither graph
membership nor coverage may require acceptance, rejection, normalization, or
the agreement theorem being established.

The local definition must preserve all six typing rules, equality-tree
composition, context checking and malformed-input defaults. In particular,
variable comparison operands come from context lookup, application certificate
type extraction uses the original substitution, and conversion operands come
from the equality witnesses' actual endpoints. Native Coq computation of
these fields is a legitimate external specification but is not internal PTS
certification of those operations.

Thus native determinism, graph/compiler agreement and a theorem that a
graph-associated quoted residual program reduces to the checker's answer
repair the earlier **native** contract. They are not an internal theorem over
arbitrary represented sources and graph witnesses. The latter additionally
needs actual fixed-rank PTS graph types and terms, independently justified
internal lookup/substitution/endpoint provenance, suitable generation guards,
and elimination/correctness for every admitted represented witness. Quoting
an externally validated graph alone does not establish that elimination law;
unproved Church parametricity cannot supply it.

Even a completed internal checker-agreement theorem would not prove rejection
of every alleged Bottom certificate. That further step requires a sufficient
dependent invariant with internal preservation and terminal exclusion, or an
equivalent independently justified bounded negative-continuation argument.
Native certificate soundness, normalization and canonicity remain external
and cannot silently discharge this obligation. Storage capacity is separate
from operational resource sufficiency. No impossibility result for a correct
source graph, internal checker or internal consistency follows from the prior
counterexample.

The complete CheckerSourceGraph source was reviewed against these criteria.
Its 35 proof endpoints cover local fields, graph agreement, uniqueness,
coverage, both Boolean outputs and exclusion of the previous counterexample.
LookupIndex, original subst and decoding remain explicitly native. The review
found no hidden evaluator/checker agreement or typing premise in admission.
Fresh integrated kernel evidence remains a separate verification obligation.

InternalExecutionGraph and CheckerGraphRealization were then reviewed in full.
The former defines independent leaf/conjunction Run constructors and an actual
fixed-rank agreement term, obtained by its Church elimination at the exact
rank-three Same motive. Same transports exact-rank-one Boolean predicates;
it is not unrestricted equality. Run has rank five and its complete agreement
type has rank six. Agreement and Holds transport apply to arbitrary represented
Run witnesses, not merely canonical quotations. The conditional rejection
consumer requires independently supplied Run(e,false); it does not generate
such evidence for all Bottom sources.

The realization recursively builds Run evidence for the symbolic Boolean
program consisting of the actual comparison leaves and conjunctions. It
does not inspect the whole checker's Boolean answer while constructing that
witness. Conversion to canonical answers uses separately proved native
comparison/graph agreement. SourcedResources adds the independent native
RawGraph to the old Resources contract; coverage and both-output agreement
repair that native contract and exclude the old self-comparison example.
Conditional rejection explicitly retains its false-output premise. Actual
acceptance of an ordinary sort example avoids claiming that both-output
correctness is established by the absence of accepted Bottom certificates.

No missing raw-source operation law is hidden by the internal execution graph:
it certifies composition of Boolean leaves supplied as data, not that any leaf
belongs to a particular source or has the required comparison provenance.
Those local source rules remain native in this checkpoint. Consequently the
new internal residual law is genuine progress but not milestone-four soundness
and not the full milestone-two arbitrary-source internal theorem.
