# Mathematical specification for the direct interpretation

Source: the included original `reference/Direct_interpretation_of_R_in_PTS_rk.tex`,
sections 1–5. This summary preserves the construction; it is NOT a proof already
accepted by Rocq. See LATEST_DECISIONS.md for two subsequent clarifications.

## Target PTS and answer type

Sorts rk_i, axiom rk_i : rk_0, and exactly the product formation rule

    A : rk_a,  B : rk_b under x:A
    ---------------------------------
    Pi x:A. B : rk_max(a+1,b).

No cumulativity, eta, primitive sums, inductive naturals, or recursion rule.
Target syntax retains lambda-domain annotations and uses intrinsic scoping.

    Bottom = Pi Z:rk_0. Z              : rk_1
    Top = rk_0 -> rk_0                 : rk_1
    top_proof = lambda Z:rk_0. Z       : Top

Fixed-answer negative logic:

    not_c A = A -> Bottom
    and_c A B = (A -> B -> Bottom) -> Bottom
    FlatOr(A_0,...,A_k) =
      (A_0 -> Bottom) -> ... -> (A_k -> Bottom) -> Bottom.

Implication is an arrow. A proof type A is stable when
`((A -> Bottom) -> Bottom) -> A` is inhabited. Translate atoms to negative
relations; composite formulas remain stable. No elimination of Bottom or of
negative case evidence into arbitrary positive types may be assumed.

Exact-rank lifts: J_1=Top; J_(k+1)=J_k -> J_k, with canonical inhabitants j_k.
For A:rk_a, a<=k, k>=2, L_k(A)=J_(k-1) -> A : rk_k. Introduction and evaluation
at j_(k-1) provide maps both ways. These are used instead of cumulativity.

## Fixed presentation domain

    D = Pi X:rk_1.
        X -> (X -> X) -> (X -> X -> X) -> (X -> X -> X) -> X : rk_3.

The arguments after X represent zero, successor, addition, multiplication.
Constructors:

    z        = lambda X z s a m. z
    s_D d    = lambda X z s a m. s (d X z s a m)
    a_D d e  = lambda X z s a m. a (d X z s a m) (e X z s a m)
    m_D d e  = lambda X z s a m. m (d X z s a m) (e X z s a m)
    nu_n     = s_D^n z.

These build arithmetic-expression presentations, NOT canonical numerical
results by beta reduction. The arithmetic equations will be proved in E.

    Good(d) = Pi Q:(D -> rk_10).
      Q z ->
      (Pi u:D. Q u -> Q(s_D u)) ->
      (Pi u v:D. Q u -> Q v -> Q(a_D u v)) ->
      (Pi u v:D. Q u -> Q v -> Q(m_D u v)) -> Q d.

Good(d):rk_12. This is a defined proof type, not an extra induction axiom
for all raw D. All four constructors have explicit Good-preservation terms.

## Certified observation telescope (8 data arguments + 23 law arguments)

Data:

    X:rk_1, z:X, s:X->X, a,m:X->X->X,
    delta:X->rk_4, R0,C0:X->X->rk_1.

Local relations are NEGATIVE:

    u ~= v = R0 u v -> Bottom          : rk_2
    u <=~ v = C0 u v -> Bottom         : rk_2.

Each object variable in each law is followed by its delta guard. The laws
are separate telescope arguments, not native records/sigmas:

1–4: delta(z), and closure under s,a,m.
5–7: ~= reflexivity, symmetry, transitivity.
8–10: congruence of s,a,m.
11: order congruence in both arguments.
12–13: order reflexivity and transitivity.
14–18: a(z,u)~=u; a(su,v)~=s(a(u,v)); m(z,u)~=z;
       m(su,v)~=a(v,m(u,v)); m(u,z)~=z.
19–23: u<=~su; u<=~a(u,v); v<=~a(u,v);
       1<=~v -> u<=~m(u,v); 1<=~u -> v<=~m(u,v), where 1=sz.

The largest individual law rank is <=5. The missing proof inputs are supplied
by concrete observations; they are not new axioms of PTS-rk.

    ev_A(d) = d X z s a m
    E(d,e) = Pi A. ev_A(d) ~= ev_A(e)
    O(d,e) = Pi A. ev_A(d) <=~ ev_A(e)
    G(d)   = Pi A. delta(ev_A(d)).

E,O,G have rank 6. E/O are stable; G is positive. Good(d)->G(d) is obtained
by using the exact rank-10 lift of G as a Good motive. G closure and all
global laws follow by opening the observation telescope and supplying G guards.

External induction on m,n constructs E(a_D nu_m nu_n,nu_(m+n)),
E(m_D nu_m nu_n,nu_(mn)), and O(nu_i,nu_j) for i<=j.
External induction produces a finite proof term per axiom index; there is no
internal unbounded arithmetic induction rule.

## Finite observations and internal separation (retain this)

For external K>=0, c=K+1, use the capped chain C_K={0,...,c} with

    s(i)=min(i+1,c), a(i,j)=min(i+j,c), m(i,j)=min(ij,c).

Use ordinary equality and order on this finite chain. In particular,
`m(c,0)=0`, NOT overflow. These tables satisfy the 23 guarded observation laws.
That external fact must be compiled into object-language proof terms.

For q=K+2 use

    F_q = rk_1 -> ... -> rk_1 -> rk_1 : rk_1   (q arguments)
    e_i = lambda Z_0 ... Z_(q-1). Z_i.

Unary and binary tables are realized by applying selectors to permuted or
repeated arguments. Relation-table entries use Bottom for TRUE and Top for
FALSE, because the observed relation is the NEGATION of that entry.
Thus a true observation is Bottom->Bottom; a false observation is Top->Bottom
and yields Bottom after application to top_proof.

The admitted-selector predicate is

    delta_q(u) = Pi Q:(F_q -> rk_3).
        Q(e_0) -> ... -> Q(e_(q-1)) -> Q(u) : rk_4.

Do NOT assume every raw inhabitant of F_q is a selector. Domain guards supply
exactly the finite elimination needed. For operation closure, open the positive
output delta first and eliminate inputs into its rank-3 motive. For relation
laws, open all guards and eliminate into remaining rank<=3 goals (lift when
needed). Reduce the resulting finite cases using beta table equations.

Specializing E/O proofs to these CLOSED observations gives internal
refutations. It is enough to export for every n:

    no_back_n : O(nu_(n+1),nu_n) -> Bottom.

Use cutoff K=n. General reversed ground order and unequal numerals follow by
ground comparison, congruence, symmetry and transitivity. This API simplification
is on-paper only and still needs implementation/proof.

## Bounded-case lemma and positive invariant

For each fixed external n:

    Case_n(d) = FlatOr(E(d,nu_0),...,E(d,nu_n),O(nu_(n+1),d)) : rk_8
    Inv_n(d) = Pi Z:rk_8. (G(d) -> Case_n(d) -> Z) -> Z      : rk_10.

The final branch is a GLOBAL O lower bound, not just classifier overflow.
Goal: construct a term of `Pi d:D. Good(d) -> Case_n(d)` for EVERY n.

Prove constructor closure of Inv_n. Open the parent's continuation and eliminate
child invariants at that SAME result type Z. This exposes positive G evidence
and negative cases separately. Build parent G without case elimination. Then
construct parent Case by opening its continuation arguments; all remaining
branches return Bottom, so negative case analysis is permitted.

- Zero: reflexive E.
- Successor: finite index i<n moves to i+1; i=n gives the large bound by
  equality/congruence; a large child stays large by order transitivity.
- Addition: finite/finite computes i+j, then chooses finite or large using
  external comparison; a large factor bounds the sum by propagation.
- Multiplication: finite/finite computes i*j. Either zero case gives equality
  to zero using BOTH zero laws. A positive finite other factor or a large
  other factor is >=1, permitting multiplication propagation. Without that
  positivity the large-factor step is invalid. Cover both mixed and large/large.

Instantiate Good directly at Inv_n. Project Case by setting Z=Case_n(d) and
using `lambda g c. c`. Do not extract an ordinary positive case split from a
continuation-encoded disjunction. Host induction over native expression trees
is insufficient for arbitrary d:Good.

## R schemes and translation

Source signature {0,S,+,*,<=}, with equality, and external numerals bar_n=S^n0:

    R1: bar_m + bar_n = bar_(m+n)
    R2: bar_m * bar_n = bar_(mn)
    R3: bar_m != bar_n                    when m != n
    R4: forall x. x<=bar_n -> (x=bar_0 or ... or x=bar_n)
    R5: forall x. x<=bar_n or bar_n<=x.

Translate operations to presentation constructors, equality/order to E/O,
logical connectives to the fixed negative encoding, and quantifiers to

    (forall x phi)^I = Pi x:D. Good(x) -> phi^I(x)
    (exists x phi)^I = (Pi x:D. Good(x) -> phi^I(x) -> Bottom) -> Bottom.

R1/R2 use ground recursion. R3 uses separation. R4 splits Case_n(d): finite
branches are the required disjunction; a large branch plus O(d,nu_n) gives
O(nu_(n+1),nu_n), internally refuted by no_back_n. R5's finite branch gives
O(d,nu_n); its large branch composes O(nu_n,nu_(n+1)) with O(nu_(n+1),d).

Prove equality/congruence obligations for admitted arguments. Good need not
be invariant on ALL raw E-equivalent objects. Classical rules require typed
stability/logical combinators and scope/substitution lemmas, not native excluded
middle assumed in the object calculus.

For ground faithfulness, externally evaluate a closed expression and construct
its E-equality to nu_value by congruence and ground calculations. Transport true
or false ground equality/order comparisons through these equalities. Report the
existence of internal refutation terms separately from external nontriviality.

## Distinguish three claims

1. Target closed inhabitant of a translated axiom: required here.
2. Rocq/external theorem that Bottom has no closed inhabitant: derivable by
   normalization/preservation/normal forms, optional separate corollary.
3. PTS-rk proving its own arithmetized Hilbert consistency: separate historical
   project, NOT part of this proof and not a premise allowed here.
