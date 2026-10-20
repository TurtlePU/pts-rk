\documentclass[preamble=doc/preamble.tex]{markdown}
title: Good Church numerals as an ordered commutative rig
date: October 20, 2026

:::Abstract
This directory gives a Rocq-checked relational
interpretation of a commutative unital semiring
with cancellative addition, a compatible strict
partial order, and every standard finite-downset
axiom. The construction uses Church numerals
carrying fixed-rank induction certificates in the
original pure type system %PTSrk{}. Equality is a
state-indexed diagonal-observer relation, and order
is a negative existential over certified
differences. All source axioms and an independently
defined classical first-order deduction system
translate to inhabitants of the original typing
judgment. The proof includes strict multiplication
compatibility and a uniform construction for every
cutoff, not merely successful finite examples.
This note describes the definitions, proof terms,
verification boundary, and the distinction between
comparison with numerals and arbitrary linearity.
:::

# Statement and verification boundary {#statement}

A *rig* is a semiring with a multiplicative unit;
commutative refers to both operations. Here an
ordered rig has a compatible **partial** order.
Its strict part is preserved by addition and by
multiplication with a strictly positive factor.
Totality of the order is not part of the claim.

:::Theorem[Formal interpretation] {#main}
There is a relational interpretation in %PTSrk{}
of a nontrivial commutative unital semiring with
cancellative addition, zero least, monotone
operations, strict addition and multiplication
compatibility, and, for every external $n ∈ ℕ$,
%mathpar
  ∀ x.\; x < \bar n
  ⟺ \bigvee_{i < n} x = \bar i.
It also interprets all five schemes of relational
Tarski–Mostowski–Robinson arithmetic $R$ and
preserves an independent classical first-order
deduction system. All these claims use one domain,
one equality, one order, and the original falsity
type.
:::

The public declaration in
[TheoremOrderedSemiring.v](TheoremOrderedSemiring.v)
has the following unconditional Rocq type:

```coq
theorem_ordered_semiring :
  (forall A, Source.axiom A ->
    exists p,
      @typ nat RankSorts 0 ε p (sentence A)) /\
  (forall A, Source.derives [] A ->
    exists p,
      @typ nat RankSorts 0 ε p (sentence A)).
```

Here `sentence` is the structural translation of a
closed source formula. `Source.axiom` and
`Source.derives` are independently defined source
predicates, not aliases for target inhabitation.
The quantified proof term `p` belongs to the
original annotated syntax `PTSrk.Syntax.Term nat 0`;
`typ` and `RankSorts` are the original PTS rules.

The development neither adds PTS rules nor uses
eta conversion, cumulativity, new primitives,
axioms, admitted proofs, or annotation erasure.
The reflective checker used for finite proof-term
certificates returns proofs of the original
typing judgment. The final theorem does not
replace that judgment by a checker acceptance
relation. Numerical facts proved in Rocq select
and justify actual PTS inhabitants; they do not
stand in for those inhabitants.

Fresh compilation and recursive kernel checking
on 20 October 2026 succeeded. The final
`Print Assumptions` reports are closed under the
global context. No external assertion that falsity
is uninhabited is an assumption of these theorems.
The precise internal proof/refutation statement
is discussed in <#ground>.

# The unchanged calculus and arithmetic terms {#calculus}

The sorts are $\rk{i}$, for external natural
numbers $i$, with $\rk{i} : \rk{0}$. Product
formation uses the rank rule
%mathpar
  \dfrac{Γ ⊢ A : \rk{a} \quad
         Γ, x : A ⊢ B : \rk{b}}
        {Γ ⊢ (x : A) → B : \rk{\max(a + 1, b)}}.
Conversion is beta conversion of the original
annotated terms. In particular, a type of rank
$a$ is not automatically a type of rank $a + 1$.

Put $U := \rk{1}$, so that $U : \rk{0}$, and
define
%mathpar
  \Void := (Z : \rk{0}) → Z : \rk{1},
  \qquad
  \top := \rk{0} → \rk{0} : \rk{1}.
The closed term $λ (Z : \rk{0}).Z$ inhabits
$\top$. The implementation calls these types
`Bottom` and `Top`.

The Church carrier is seed-first:
%mathpar
  D := (X : U) → X → (X → X) → X : \rk{3}.
With the lambda annotations determined by this
type, the arithmetic operations are
%align*
  0 &:= λ X\, a\, f.a, \\
  s\, n &:= λ X\, a\, f.f(n\, X\, a\, f), \\
  \Add\, x\, y &:= λ X\, a\, f.x\, X\, (y\, X\, a\, f)\, f, \\
  \Mul\, x\, y &:= λ X\, a\, f.
    x\, X\, a\, (λ u : X.y\, X\, u\, f).
Write $1 := s\, 0$ and $\nu_n := s^n 0$.
The source-oriented operations are deliberately
reversed:
%mathpar
  x ⊕ y := \Add\, y\, x,
  \qquad
  x ⊗ y := \Mul\, y\, x.
This convention matches the source arithmetic
graphs and recursion equations. Commutativity is
proved below; it is not silently used to change
the definitions.

For proof types, use negative classical encodings:
%align*
  \neg_c P &:= P → \Void, \\
  P ∧_c Q &:= (P → Q → \Void) → \Void, \\
  \bigvee_{c, i < k} P_i
    &:= (P_0 → \Void) → \cdots →
      (P_{k-1} → \Void) → \Void, \\
  ∃_c x : A.\, P(x)
    &:= ((x : A) → P(x) → \Void) → \Void.
The empty disjunction is $\Void$. A proof type
$P$ is *stable* when there is a term of type
$\neg_c\neg_c P → P$. The equalities, order
predicates, and translated source formulas used
below are stable. Negative existential witnesses
are consumed inside continuations; the proof
does not extract positive witness pairs.

# Certified numerals and rank budgets {#guards}

:::Definition[Goodness certificate] {#good}
For the motive rank $r$, define
%mathpar
  \Good{r}(n) :=
  (P : D → \rk{r}) → P(0) →
  ((u : D) → P(u) → P(s\, u)) → P(n).
The certificate type has rank $r + 2$ for the
budgets used here. Thus the subscript is the rank
of the induction motive, not the rank of the
certificate itself.
:::

The zero and successor certificates are the
ordinary Church induction constructors:
%mathpar
  g_{r, 0} := λ P\, p_0\, p_s.p_0,
  \qquad
  g_{r, s}\, n\, g :=
    λ P\, p_0\, p_s.p_s\, n\, (g\, P\, p_0\, p_s).
[RigCodes.v](RigCodes.v) proves their native
typing at the three fixed budgets $7$, $11$, and
$15$. These budgets are sufficient for the
whole construction; no rank optimality is claimed.

Lowering a certificate requires an explicit lift
of a lower-rank motive. Define
%mathpar
  J_0 := \rk{0},
  \qquad J_{k+1} := J_k → \rk{0},
  \qquad
  j_0 := \rk{0},
  \qquad j_{k+1} := λ (v : J_k).\rk{0}.
Then $J_k : \rk{k}$ and $j_k : J_k$.
A motive value $P$ of rank at most $t$ can be
lifted to exact rank $t$ as $J_{t-1} → P$.
Induction into that lifted motive followed by
evaluation at $j_{t-1}$ gives the checked maps
$\Good{15} → \Good{11}$,
$\Good{11} → \Good{7}$, and
$\Good{15} → \Good{7}$. There is no converse
promotion rule.

:::Lemma[Closure] {#closure}
At each of the three budgets, the admitted
objects are closed under zero, successor,
explicit eta expansion, addition, and
multiplication.
:::

:::Proof
Open the desired output certificate at an
arbitrary predicate $P$ and its zero/step proofs.
For addition, apply the first input certificate
to $u ↦ P(\Add\, u\, y)$. Its zero case is
$P$ of the explicit eta expansion of $y$, obtained
from the second input certificate. Its successor
case uses the supplied step of $P$.

For multiplication, use $u ↦ P(\Mul\, u\, y)$.
At successor, the equation
$\Mul(s\, u)y =_β \Add\, y\, (\Mul\, u\, y)$
lets a second induction on $y$ supply the needed
iteration of the step. The implementation in
[DomainClosure.v](DomainClosure.v) never inducts
into $\Good{r}$ itself and never transports a
positive goodness certificate through the
observational equality defined next.
:::

# A single observer equality {#equality}

For $A, B : U$, put
%mathpar
  T(A, B) :=
    (\neg_c A → \neg_c B) ∧_c
    (\neg_c B → \neg_c A) : \rk{5}.
An observer consists of data
%mathpar
  X : U,
  \quad r : X → X → \rk{5},
  \quad a : X,
  \quad k : U → X,
  \quad f : X → X,
  \quad d : X → (U → X) → X,
  \quad p : X → U,
together with the following nine certificates.
All displayed object variables are universally
bound at their indicated types; write
$d_w h := d\, w\, h$.
%align*
  &r(v, v), \\
  &r(v, w) → r(w, v), \\
  &r(u, v) → r(v, w) → r(u, w), \\
  &r(v, w) → r(fv, fw), \\
  &((z : U) → r(hz, h'z)) → r(d_w h, d_w h'), \\
  &r(f(kz), kz), \\
  &r(d_w k, w), \\
  &r(d_w(λ z : U.v), v), \\
  &r(v, w) → T(pv, pw).
Here $u, v, w : X$, $z : U$, and $h, h' : U → X$.
These certificates are **bound fields of each
observer**, not global axioms.

:::Definition[Diagonal-observer equality] {#observer-equality}
Let $\mathcal A$ denote the entire dependent
telescope of observer data and certificates.
Define
%mathpar
  \Eq(x, y) :=
    \mathcal A →
    T\bigl(p(x\, X\, a\, f), p(y\, X\, a\, f)\bigr)
    : \rk{7}.
The notation $\mathcal A → B$ expands dependent
arrows; it does not add a record or quotient type.
:::

[ObservationEquality.v](ObservationEquality.v)
proves stability, reflexivity, symmetry,
transitivity, successor congruence, and
observational eta equality. For example,
successor congruence reuses the observer with
$p$ replaced by $p ∘ f$. Eta expansion is
observationally equal because its applications
to $X, a, f$ beta-reduce to the same expressions;
eta conversion is not used.

[ArithmeticCongruence.v](ArithmeticCongruence.v)
proves the guarded addition and multiplication
congruences. They are specific to these
operations and their certified arguments.
The development does not assume that every raw
function $D → D$ respects $\Eq$.

## Successor separation {#successor}

:::Lemma[Successor facts]
There are closed terms realizing
%mathpar
  \Good{7}(x) → \Eq(s\, x, 0) → \Void,
  \qquad
  \Good{7}(x) → \Good{7}(y) →
    \Eq(s\, x, s\, y) → \Eq(x, y).

:::

:::Proof
[SuccessorSeparation.v](SuccessorSeparation.v)
constructs two actual observers and supplies all
nine certificates for each.

For nonzeroness, take $X := U → U → U$ and
%align*
  r(v, w) &:= (A, B : U) → T(v\, A\, B, w\, A\, B), \\
  a\, A\, B &:= A, & k\, C\, A\, B &:= C, \\
  f\, v\, A\, B &:= v\, B\, B, \\
  d\, w\, h\, A\, B &:= h(w\, A\, B)\, A\, B, \\
  p\, v &:= v\, \top\, \Void.
Its zero observation is $\top$. Induction using
$\Good{7}(x)$ identifies the successor observation
with $\Void$ in the sense of $T$. An assumed
$\Eq(s\, x, 0)$ then gives a term of $\Void$ by
applying the two negative implications to the
closed inhabitant of $\top$.

For injectivity, start with an arbitrary observer
and form a delayed one. Its carrier is
$X' := U → X$, with pointwise relation
$r'(v, w) := (z : U) → r(vz, wz)$, and data
%align*
  a' &:= k, & k'\, z &:= λ u : U.k\, z, \\
  f'\, v &:= λ u : U.d\, a\, (λ z : U.f(vz)), \\
  d'\, w\, h &:= λ u : U.d(wu)(λ z : U.h\, z\, u), \\
  p'\, v &:= p(v\, \top).
The original nine certificates prove the nine
delayed certificates. In particular, the
state-indexed argument of $d$ is retained.
The type $U → X$ still has rank one because
$U : \rk{0}$.

Write $F_n := n\, X\, a\, f$ and
$F'_n := n\, X'\, a'\, f'$. A rank-five simulation
motive, lifted to rank seven, proves
%mathpar
  \Good{7}(n) → (z : U) → r(F'_{s\, n}z, F_n).
At zero use $f(kz) ∼ kz$ and $d_a k ∼ a$;
at successor use pointwise congruence of $d_a$
and its law on constant functions. Apply the
assumed successor equality to the delayed
observer, then compose the two simulations via
the $p$ bridge. This recovers the result of every
original observer and hence $\Eq(x, y)$.
:::

This equality is not the rank-five predicate
equality of the older relational $R$ library.
Only the common carrier, arithmetic beta
computations, syntax, and proof infrastructure
are reused. Facts about the old equality or
order are not renamed into facts about the new
$\Eq$ and $\Ord$.

# Retained induction and the rig laws {#algebra}

:::Lemma[Induction retaining a lower certificate] {#retained}
Let $P(u)$ be stable, of rank seven, eight, or
nine. Given closed realizers of
%mathpar
  P(0),
  \qquad
  (u : D) → \Good{7}(u) → P(u) → P(s\, u),
one obtains a realizer of
$(x : D) → \Good{11}(x) → P(x)$.
:::

:::Proof
Use the rank-eleven invariant
$I(u) := \Good{7}(u) ∧_c P(u)$.
The base pairs the zero certificate with the
base proof. To make the successor pair, open the
previous negative pair inside a continuation,
apply the goodness successor constructor and
the supplied step, and feed both outputs to the
new continuation. Induction using
$\Good{11}(x)$ gives $I(x)$.
Project $P(x)$ negatively and use its stability.
The proof never extracts a positive
$\Good{7}$ certificate outside its continuation.
The three native instances are checked in
[RetainedInduction.v](RetainedInduction.v).
:::

It is useful to distinguish the larger domain
$W = (D, \Good{11})/\Eq$ from the main domain
$V = (D, \Good{15})/\Eq$. These are descriptions
of a guarded first-order interpretation, not
internal quotient constructions.

Associativity of $\Add$ and $\Mul$, and
%mathpar
  \Mul(\Add\, x\, y)z =_β
    \Add(\Mul\, x\, z)(\Mul\, y\, z),
are raw beta identities. Some unit equations
return an explicit eta expansion, handled by
observational eta equality.

Rank-seven induction first proves the
successor-shift law for addition and then
addition commutativity. It also supplies the
remaining multiplication-zero and unit laws.
Retained induction proves
%mathpar
  \Good{11}(x) → \Good{7}(y) →
    \Eq(\Mul\, x\, (s\, y),
        \Add\, x\, (\Mul\, x\, y)).
The successor step needs addition congruence,
associativity and commutativity; the retained
$\Good{7}$ certificate justifies these uses.
A second retained induction proves
multiplication commutativity on $W$.
The other distributive law follows.
[SemiringLaws.v](SemiringLaws.v) supplies the
closed inhabitants of these generic equations.

:::Lemma[Cancellation, zero sums and zero products] {#cancel}
On $W$, addition is cancellative, and
%mathpar
  \Eq(x ⊕ y, 0) →
    \Eq(x, 0) ∧_c \Eq(y, 0),
  \qquad
  \Eq(x ⊗ y, 0) →
    \Eq(x, 0) ∨_c \Eq(y, 0).

:::

:::Proof
For cancellation, use <#retained> with the
rank-eight motive
%mathpar
  P(u) :=
    \Eq(\Add\, u\, x, \Add\, u\, y) → \Eq(x, y).
The successor step applies successor injectivity
to the two sums and then the induction
hypothesis. The sums have the lower goodness
certificates needed for injectivity.

For zero sums use
$P(u) := \Eq(\Add\, u\, y, 0) → \Eq(u, 0)$.
The zero case is reflexivity; the successor case
contradicts successor nonzeroness. Commutativity
supplies the other summand.

For zero products fix $y$ and use the rank-nine
stable motive
%mathpar
  P(u) := \Eq(\Mul\, u\, y, 0) →
    (\Eq(u, 0) ∨_c \Eq(y, 0)).
At zero choose the first disjunct. At successor,
the equation for $\Mul(s\, u)y$ and zero-sum
reflection give $\Eq(y, 0)$. This step needs the
retained certificate for $u$ but not the
induction hypothesis itself.
All three constructions are checked in
[Cancellation.v](Cancellation.v).
:::

# Natural difference order and strictness {#order}

:::Definition[Order] {#difference-order}
For arbitrary $x, y : D$, let
%mathpar
  \Ord(x, y) :=
    ((c : D) → \Good{11}(c) →
      \Eq(\Add\, c\, x, y) → \Void) → \Void
    : \rk{15}.
Write $x ≤ y$ for $\Ord(x, y)$ and define
$x < y := \Ord(x, y) ∧_c \neg_c\Eq(x, y)$.
The strict predicate has rank seventeen.
:::

The order asserts a negative existential
difference $c$ satisfying $x ⊕ c =_E y$.
Crucially, this witness has a $\Good{11}$
certificate even when the endpoints belong to
$V$. The order on $V$ is inherited from $W$.

:::Lemma[Compatible strict partial order] {#order-laws}
On $W$, the relation $≤$ is reflexive,
transitive and antisymmetric modulo $\Eq$.
Zero is least, both operations are monotone,
and their strict laws include
%mathpar
  x < y → x ⊕ z < y ⊕ z,
  \qquad
  x < y → 0 < z → x ⊗ z < y ⊗ z.
The corresponding left-argument laws hold too.
All these laws restrict to $V$.
:::

:::Proof
Reflexivity chooses difference zero; zero
leastness chooses the object itself.
Transitivity adds the two differences, using
closure. If $x ⊕ c =_E y$ and
$y ⊕ d =_E x$, cancellation gives
$c ⊕ d =_E 0$, and zero-sum reflection gives
$c =_E 0$. Hence $x =_E y$.

Additive monotonicity keeps the same difference.
Multiplicative monotonicity uses $c ⊗ z$ and
distributivity. Closure supplies the witness
certificate in each case. Strict additive
monotonicity follows from cancellation.

For strict multiplication, suppose the products
were equal. Distributivity and cancellation
would give $c ⊗ z =_E 0$. The zero-product
disjunction gives $c =_E 0$ or $z =_E 0$.
The first contradicts $x < y$ using the
difference equation; the second contradicts
$0 < z$. This additional argument is needed:
ordinary monotonicity alone does not imply
strict multiplication compatibility.

Every witness is consumed within the negative
existential continuation. The final conclusions
are stable. The definitions and native proof
terms are in [NaturalOrder.v](NaturalOrder.v)
and [OrderLaws.v](OrderLaws.v).
:::

# Every finite cut at one fixed rank {#cuts}

For an external cutoff $n$, put
%align*
  K_n(x) &:= (t : D) → \Good{11}(t) →
    \Eq(x, s^{n+1}t) → \Void, \\
  \Cut_n(x) &:=
    (\Eq(x, \nu_0) → \Void) → \cdots →
    (\Eq(x, \nu_n) → \Void) → K_n(x) → \Void.
The rank of $K_n(x)$ is fourteen and that of
$\Cut_n(x)$ is fifteen, independently of $n$.
The large case is flattened into the branch
telescope. Nesting ordinary binary disjunctions
instead would waste rank as the cutoff grows.

:::Lemma[Uniform finite cut] {#finite-cut}
For every external natural number $n$, there
is a closed original PTS inhabitant of
%mathpar
  (x : D) → \Good{15}(x) → \Cut_n(x).

:::

:::Proof
Induct directly into $u ↦ \Cut_n(u)$ with
the supplied $\Good{15}$ certificate.
After opening the branch continuations, the
zero case selects the branch $u =_E \nu_0$.
For successor, a finite branch $u =_E \nu_i$
with $i < n$ goes to the next finite branch.
The last finite branch goes to the large branch
with witness zero. A large branch
$u =_E s^{n+1}t$ goes to the large branch with
witness $s\, t$ and its successor certificate.
Successor congruence supplies all equality
steps. The case $n = 0$ has no first group of
finite successor branches.

[FiniteCuts.v](FiniteCuts.v) constructs the
telescope and its inhabitant recursively in
the external parameter $n$. Its theorem
`finite_cut_realized` is quantified over every
$n$; it is not a finite test suite.
:::

A finite branch $x =_E \nu_i$, $i ≤ n$, gives
$x ≤ \nu_n$ with difference $\nu_{n-i}$.
In a large branch, $x =_E s^{n+1}t$ gives
$\nu_n ≤ x$ with difference $s\, t$.
If it also satisfied $x ≤ \nu_n$, combining
the difference equations and cancelling $n$
successors would give a successor equal to zero.
The intermediate sums carry the necessary
$\Good{7}$ certificates by closure and lowering.

Consequently, for every $n$, the main domain
realizes
%mathpar
  x ≤ \nu_n ⟺ \bigvee_{c, i ≤ n} \Eq(x, \nu_i),
  \qquad
  x ≤ \nu_n ∨_c \nu_n ≤ x.
These are [BoundedCases.v](BoundedCases.v)'s
all-index results. Numeral separation removes
the endpoint from the first equivalence to give

%mathpar
  x < \nu_n ⟺ \bigvee_{c, i < n} \Eq(x, \nu_i).

[StrictBounded.v](StrictBounded.v) also proves
the bridge to the *literal* source sentence,
including the empty downset at $n = 0$.
The bridge uses beta conversion where the source
expands strict order but the target applies the
closed strict-order constructor.

For reference, the main fixed ranks are
%mathpar
  \begin{array}{c|rrrrrrrr}
    \text{type} & D & \Eq(x, y) & \Good{7}(x) &
      \Good{11}(x) & \Good{15}(x) & \Ord(x, y) &
      x < y & \Cut_n(x) \\
    \hline
    \text{rank} & 3 & 7 & 9 & 13 & 17 & 15 & 17 & 15
  \end{array}

# The source theory and preservation of deductions {#source}

[Source.v](Source.v) uses an independent
first-order syntax whose term symbols are zero
and successor. Addition and multiplication are
ternary relation symbols $A(x, y, z)$ and
$M(x, y, z)$, not target-language functions
smuggled into source terms. Equality, $≤$,
falsity, implication and universal quantification
are primitive formula constructors. Other
connectives are the negative abbreviations
already displayed.

The finite list `Source.rig_laws` contains
exactly 23 universally closed relational axioms:

1. For each of $A$ and $M$: totality, uniqueness,
   commutativity and associativity (eight axioms).
2. Additive zero, multiplicative zero and unit,
   distributivity, and additive cancellation
   (five axioms).
3. Order reflexivity, transitivity, antisymmetry,
   zero leastness and $0 ≠ 1$ (five axioms).
4. Monotonicity of $A$ and $M$, strict additive
   monotonicity and strict multiplicative
   monotonicity with a positive factor
   (four axioms).
5. Successor as addition of one:
   $A(x, 1, s\, x)$ (one axiom).

For example, relational associativity of $A$ is
the universal closure of
%mathpar
  A(x, y, u) → A(u, z, w) → A(y, z, v) → A(x, v, w).
Totality and uniqueness make this the familiar
associative operation law without changing the
relational source signature. Commutativity
supplies the omitted opposite-side unit and
monotonicity equations.

The other source axiom constructors contain the
strict finite-cut schema and the five relational
$R$ schemes, for all external $m, n$:
%align*
  &∀ z.\; A(\bar m, \bar n, z) ⟺ \overline{m+n} = z, \\
  &∀ z.\; M(\bar m, \bar n, z) ⟺ \overline{mn} = z, \\
  &\bar m ≠ \bar n \quad (m ≠ n), \\
  &∀ x.\; x ≤ \bar n ⟺ \bigvee_{i ≤ n} x = \bar i, \\
  &∀ x.\; x ≤ \bar n ∨ \bar n ≤ x.
All formula connectives here denote the
declared source abbreviations. The source
theory contains no target-typing premise and
no assumption of its own interpretation.

The structural translation sends the atomic
formulas to
%align*
  (x = y)^* &:= \Eq(x^*, y^*), \\
  (x ≤ y)^* &:= \Ord(x^*, y^*), \\
  A(x, y, z)^* &:= \Eq(x^* ⊕ y^*, z^*), \\
  M(x, y, z)^* &:= \Eq(x^* ⊗ y^*, z^*).
Falsity goes to $\Void$, implication to the
ordinary arrow, and universal quantification
is guarded:
%mathpar
  (∀ x.\, B)^* :=
    (x : D) → \Good{15}(x) → B^*.
[FirstOrderTranslation.v](FirstOrderTranslation.v)
proves typing, stability, and compatibility
with renaming and substitution. Its formula
rank is computed recursively: equality and
arithmetic atoms have rank seven, order atoms
rank fifteen, falsity rank one, implication has
rank $\max(a + 1, b)$, and universal quantification
has rank $\max(18, b)$.

The source deduction rules are assumptions,
theory axioms, implication introduction and
elimination, universal introduction and
elimination, double-negation elimination,
equality reflexivity and equality replacement.
[FirstOrderEquality.v](FirstOrderEquality.v)
proves the replacement operation by structural
induction on formulas, using the guarded
arithmetic congruences. It does not identify
observer equality with definitional equality.

:::Proof[Proof of Theorem \ref{main}]
[RigAxiomRealization.v](RigAxiomRealization.v)
realizes the actual translations of all 23
relational rig axioms, including their
$\Good{15}$ quantifier guards.
[RAxiomRealization.v](RAxiomRealization.v)
realizes every instance of the five $R$ schemes.
[StrictBounded.v](StrictBounded.v) supplies
every strict finite-cut sentence.

Induction on the independent source derivation
now constructs the target inhabitant.
Implication uses native abstraction/application;
quantification uses the guarded translation and
its substitution theorem; the classical rule
uses proved stability. Equality replacement
uses its separately proved structural theorem.
The general lemma in
[FirstOrderDeduction.v](FirstOrderDeduction.v)
takes an axiom-realization parameter.
The public theorem supplies the actual realizers
above, so no such parameter remains in its type.
:::

The public all-cutoff and comparison declarations
make the quantification explicit:

```coq
bounded_cases cutoff :
  exists p, @typ nat RankSorts 0 ε p
    (sentence (Source.strict_bounded cutoff)).

numeral_comparison cutoff :
  exists p, @typ nat RankSorts 0 ε p
    (sentence (comparison_sentence cutoff)).
```

## Ground truth and internal refutation {#ground}

[GroundFaithfulness.v](GroundFaithfulness.v)
proves the correct ground arithmetic beta
computations and constructs proof or refutation
inhabitants according to each numerical test.
For example, $m + n = k$ gives a proof of
$\Eq(\nu_m ⊕ \nu_n, \nu_k)$, whereas
$m + n ≠ k$ gives a proof of its negation.
Likewise $i ≤ j$ gives $\Ord(\nu_i, \nu_j)$,
and $j < i$ gives its negation.
The results cover all closed source terms and
all equality, order, addition and multiplication
atoms, not just hand-selected numerals.

These are **internal refutations**: a false atom
has a term mapping any claimed proof of that
atom to $\Void$. They do not, by themselves,
assert externally that $\Void$ has no
inhabitants. Turning internal refutation into
an external non-inhabitation statement would
require that distinct metatheoretic result.
Neither the interpretation nor its preservation
proof assumes such a result or uses a set model.

# What is not claimed: predecessors and linearity {#limits}

At cutoff zero, the finite-cut theorem gives
zero or a successor of an object carrying
$\Good{11}$. It does **not** provide a
predecessor with $\Good{15}$, and it supplies
no promotion from the weaker to the stronger
certificate. Thus the order on $V$ is not
claimed to be the natural difference order
formed using differences inside $V$ itself.

[Graphs.v](Graphs.v) additionally checks native
translations of Robinson's Q1, Q2, Q4, Q5, Q6
and Q7 using the same equality and main guard.
It does not prove Q3, the same-domain predecessor
axiom, or an interpretation of full Robinson
arithmetic $Q$. Those six equations are not
silently inserted as additional constructors
of the public `Source.axiom` predicate.

Comparison with each fixed standard numeral is
a genuine weak comparison principle. Arbitrary
totality, trichotomy, or strict cotransitivity
remain unproved for this particular PTS
interpretation. They also do not follow merely
from the stated source algebra and order laws.

:::Remark[A nonlinear source model] {#countermodel}
Let $C$ consist of zero and those polynomials
in $ℤ[t]$ that are eventually positive as $t$
tends both to $+∞$ and to $-∞$. Equivalently,
its nonzero elements are positive integer
constants and positive-leading-coefficient
polynomials of positive even degree. Use the
ordinary polynomial operations and define
%mathpar
  p ≤ q \quad ⟺ \quad q - p ∈ C.
Then $C$ is a cancellative commutative unital
semiring with no zero divisors. This is its
natural difference order: zero is least,
addition preserves strict inequality, and
multiplication by a nonzero element does too.

Every nonconstant member exceeds every standard
integer. The elements below a fixed numeral $n$
are exactly $0, \ldots, n$, so all the finite
downset and numeral-comparison schemes hold.
Successor is $p ↦ p + 1$. This model even has
same-domain predecessors: subtracting one from
a nonconstant member leaves it in $C$.

Nevertheless $t^2 + t$ and $t^2 - t$ are
incomparable, since their nonzero differences
have odd degree. Thus totality, trichotomy,
and the principle that mutual absence of
strict inequality implies equality all fail.
Strict cotransitivity fails as well: for
$x = t^2$, $y = t^2 + t$, and $z = t^2 + 1$,
one has $x < z$ but neither $x < y$ nor $y < z$.

This is a mathematical source-theory
counterexample, not a Rocq-verified set model
and not a model of every PTS type. It does not
show that stronger comparison is impossible
in the specific Church/observer interpretation.
Any such improvement would need additional
properties of that interpretation, beyond the
source laws proved here.
:::

# Files and reproduction {#reproduction}

The public library name is `OrderedSemiring`.
Its proof layers are arranged as follows:

- [RigCodes.v](RigCodes.v),
  [DomainClosure.v](DomainClosure.v): the three
  goodness budgets, lowering, and native closure.
- [ObservationEquality.v](ObservationEquality.v),
  [ArithmeticCongruence.v](ArithmeticCongruence.v),
  [SuccessorSeparation.v](SuccessorSeparation.v):
  the new observer equality and successor facts.
- [RetainedInduction.v](RetainedInduction.v),
  [SemiringLaws.v](SemiringLaws.v),
  [Cancellation.v](Cancellation.v): generic
  algebra, cancellation and zero-product cases.
- [NaturalOrder.v](NaturalOrder.v),
  [OrderLaws.v](OrderLaws.v): the difference
  order and strict compatibility.
- [FiniteCuts.v](FiniteCuts.v),
  [OrderNumerals.v](OrderNumerals.v),
  [OrderCuts.v](OrderCuts.v),
  [BoundedCases.v](BoundedCases.v),
  [StrictBounded.v](StrictBounded.v): uniform
  finite cuts and their source-level bridges.
- [ModelInterface.v](ModelInterface.v),
  [Source.v](Source.v),
  [FirstOrderTranslation.v](FirstOrderTranslation.v),
  [FirstOrderEquality.v](FirstOrderEquality.v):
  the independent source and structural translation.
- [RigAxiomRealization.v](RigAxiomRealization.v),
  [RAxiomRealization.v](RAxiomRealization.v),
  [FirstOrderDeduction.v](FirstOrderDeduction.v),
  [TheoremOrderedSemiring.v](TheoremOrderedSemiring.v):
  all-index axiom realization and deduction preservation.
- [GroundFaithfulness.v](GroundFaithfulness.v),
  [Graphs.v](Graphs.v): ground proofs/refutations,
  total functional graphs and the six additional
  native Robinson translations.

Dependencies are the unchanged `PTSrk` kernel,
the common `Interpretation_of_R` infrastructure,
and its independent `Interpretation_of_R.relational`
library. There is no dependency on the functional
interpretation, the set-theoretic model, or a new
normalization assumption. Only the required
common and relational infrastructure accompanies
this development.

From the repository root, run

```sh
bash theories/OrderedSemiring/check.sh
```

The checker records tool versions and exact logs,
builds in a fresh absolute Dune directory so that
assumption reports are regenerated, then
recursively kernel-checks the final theorem and
its dependencies. The verified environment used
Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2 and Dune 3.23.1. Consult
[check.sh](check.sh) for toolchain selection and
log-directory overrides; no package installation
is performed by the check.

This note is itself LaTeX–Markdown source, using
the same document dialect as the main paper.
To regenerate its PDF, run

```sh
bash theories/OrderedSemiring/doc/build.sh
```

The bundled [preamble.tex](https://github.com/akuklev/pts-rk/blob/ordered-semiring-interpretation/theories/OrderedSemiring/doc/preamble.tex) and
document runtime make this a local documentation
build. Neither a hosted prose service nor an
external bibliography or proof badge is needed.
The result is [README.pdf](https://github.com/akuklev/pts-rk/blob/ordered-semiring-interpretation/theories/OrderedSemiring/README.pdf).

The mathematical starting point was the supplied
note *Good Church numerals as an ordered
commutative rig* of 14 October 2026.
The Rocq development goes beyond its experimental
checks: it supplies the uniform all-cutoff proof,
strict multiplication compatibility, independent
deduction preservation, and fresh kernel evidence.
Its source revision is
[5530d1e](https://github.com/akuklev/pts-rk/tree/5530d1e4130c28a741b48efbd902dd1127ac45c5/theories/OrderedSemiring).
