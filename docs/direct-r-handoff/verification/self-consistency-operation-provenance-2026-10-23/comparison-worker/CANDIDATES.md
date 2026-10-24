# Preserved comparator-graph candidates and mathematical boundary

The repository module InternalComparisonGraph contains only checked formation,
application and rule-local observation transport, not the proposed universal
graph eliminator. No old source was edited, and no artifact was deleted.

The graph is proof-indexed: Trace(x,y,z,b) retains the actual z:Zip(x,y).
Its independent constructor fields mention atom_zip / pair_atom_zip /
pair_pair_zip and symbolic is_atom / false / conjunction outputs. There is no
field asserting compare correctness. Its fiber rank6 is checked.

AgreementBase.v checks formation at rank7 of the intended closed type
Pi x,y:C. Pi z:Zip(x,y). Pi b:Bool. Trace(x,y,z,b) -> Same(compare x y z,b).
AgreementProbe.v / AgreementShared.v / LocalBranchProbe.v preserve unsuccessful
whole/checker proof attempts. NativeConstructorProbe.v preserves the last
native lookup attempt. ConstructorProbe.v preserves the checker-based one.
They are experiments, NOT modules to install in the development.

The atom and pair/atom constructor-context WF proofs completed, as did the
atom-family body and abstraction in constructors03; that whole file later
timed out and therefore produced no complete .vo. Native tV/tApp should replace
the expensive checker, but its current index equality expands the entire
61-binder assembled telescope before it can simplify shifts. Increasing fuel
does not address this problem; several attempts exceeded8GB RSS.

The next missing infrastructure is a symbolic named-context lookup theorem:
derive a selected variable's ORIGINAL Context.index type from its named field
annotation, its successful assembly, and non-shadowing of the names free in
that annotation by the suffix. The proof should recurse over the context and
use evaluate/extend plus rename_lift_closed; it must not unfold closed Zip or
operation payloads. Apply it to the29+29 constructor families, then use the
already checked NamedSpine and trace_head_beta for recursive constructor/fold
assembly. The three scoped observation-agreement schemata already discharge
the actual local CMP beta/Boolean transport obligations.

This lookup theorem is NOT logically necessary for arbitrary-Trace agreement.
That fold can be tackled independently: lambda-abstract the checked scoped
local agreement terms to obtain closed branch arguments; use NamedBeta for
the four applied motive heads; then instantiate the59 cases via NamedSpine
at the arbitrary Trace variable in the small five-binder outer context.
Only the present constructor implementation needs the61-binder lookup first.
Neither the lookup lemma nor a particular assembler should be elevated to a
mathematical soundness premise if a simpler proof avoids it.

Same is exact-rank-one predicate transport, not beta equality or endpoint
identity. Even a completed arbitrary-Trace agreement theorem would not show
true comparison implies arbitrary represented endpoints are coherent raw
syntax: atom-left allows arbitrary y and only observes is_atom(t,y). Endpoint
generation/canonicity or stronger source provenance must still be supplied.
