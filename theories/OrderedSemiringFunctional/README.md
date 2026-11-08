\documentclass[preamble=doc/preamble.tex]{markdown}
title: A functional interpretation of an ordered commutative rig
date: October 20, 2026

:::Abstract
This development interprets an ordered
commutative unital semiring with genuine
addition and multiplication function symbols
in the original pure type system %PTSrk{}.
Its domain, equality and difference order are
the same certified Church construction used
by the accompanying relational interpretation.
The additional work concerns arbitrary nested
source terms: their translations are typed,
remain in the admitted domain, and respect
observational equality. A separately defined
functional first-order theory includes the
semiring laws, strict order compatibility and
all standard bounded-case axioms. Its classical
deduction rules are translated directly, not
by assuming a graph-elimination theorem.
This note describes the mathematical model,
the functional proof interface and the exact
verification boundary.
:::

# Scope and the functional signature {#scope}

The distinction from the relational development
is in the source language, not in the target
arithmetic. Source terms now have the grammar

%mathpar
  t ::= x \mid 0 \mid S(t)
    \mid t + t \mid t ⋅ t.

Thus $(x + 1) ⋅ (y + z)$ is a source term.
Addition and multiplication are not ternary
graph predicates. They are translated to the
actual closed Church addition and
multiplication terms.

The primitive formulas are

%mathpar
  A ::= t = t \mid t ≤ t \mid ⊥
    \mid A → A \mid ∀ x.\,A.

Conjunction, disjunction and existential
quantification are negative abbreviations,
specified in Section <#logic>. There is no source
predicate that asserts target typing or
inhabitation.

The verified interpretation result covers 19
functional rig laws, all five functional $R$
schemes, the strict bounded-case schema

%mathpar
  ∀ x.\; x < \bar n
    ⟺ \bigvee_{i < n} x = \bar i
  \qquad (n ∈ ℕ),

and an independent classical deduction system.
The order is a strictly compatible **partial**
order; arbitrary totality is not asserted.
The all-cutoff quantification ranges over
external natural numbers and does not mean
that finitely many examples are tested.

# The unchanged target construction {#target}

The PTS has sorts $\rk{i}$ with
$\rk{i} : \rk{0}$ and product rule

%mathpar
  \dfrac{Γ ⊢ A : \rk{a} \quad
         Γ, x : A ⊢ B : \rk{b}}
        {Γ ⊢ (x : A) → B : \rk{\max(a + 1, b)}}.

All terms retain their lambda annotations.
Conversion is beta conversion, without eta,
cumulativity, additional primitives or changed
PTS rules. The syntax and judgment are the
original `PTSrk.Syntax.Term` and `Typing.typ`
with `Ranks.RankSorts`.

Put $U := \rk{1}$, so $U : \rk{0}$, and

%mathpar
  \Void := (Z : \rk{0}) → Z : \rk{1},
  \qquad
  \top := \rk{0} → \rk{0} : \rk{1}.

The term $λ(Z : \rk{0}).Z$ inhabits $\top$.
The fixed target falsity is $\Void$, called
`Bottom` in the code. No external assumption
that this type is uninhabited is needed to
construct the interpretation's proof terms.

## Carrier and operations {#operations}

The seed-first Church carrier and operations
are

%align*
  D &:= (X : U) → X → (X → X) → X : \rk{3}, \\
  0 &:= λ X\,a\,f.a, \\
  s\,n &:= λ X\,a\,f.f(n\,X\,a\,f), \\
  \Add\,x\,y &:= λ X\,a\,f.x\,X\,(y\,X\,a\,f)\,f, \\
  \Mul\,x\,y &:= λ X\,a\,f.
    x\,X\,a\,(λ u : X.y\,X\,u\,f).

Write $1 := s\,0$ and $\nu_n := s^n 0$.
The source orientation is

%mathpar
  x ⊕ y := \Add\,y\,x,
  \qquad
  x ⊗ y := \Mul\,y\,x.

The translation of a source sum is literally
the closed term `Model.addition` applied to
the two translated arguments. Likewise a
source product applies `Model.multiplication`.
The reversal above is part of their definitions;
commutativity is proved and is not used to
silently alter the source translation.

## Goodness and fixed rank budgets {#goodness}

For a motive rank $r$, let

%mathpar
  \Good{r}(n) :=
    (P : D → \rk{r}) → P(0) →
    ((u : D) → P(u) → P(s\,u)) → P(n).

At the three budgets used here, $r = 7, 11, 15$,
the certificate type has rank $r + 2$.
Its zero and successor proofs are

%mathpar
  g_{r, 0} := λ P\,p_0\,p_s.p_0,
  \qquad
  g_{r, s}\,n\,g :=
    λ P\,p_0\,p_s.p_s\,n\,(g\,P\,p_0\,p_s).

The main domain is $D$ guarded by
$\Good{15}$. The verified certificate-lowering
maps give $\Good{15} → \Good{11}$ and
$\Good{11} → \Good{7}$, not converses.
Lowering explicitly raises the motive's rank
using inhabited types $J_0 := \rk{0}$ and
$J_{k+1} := J_k → \rk{0}$; it does not invoke
cumulativity.

The same three budgets are closed under zero,
successor, addition and multiplication.
To prove closure, open the output certificate
at an arbitrary predicate, then induct into
that predicate composed with the arithmetic
operation. This is not induction into the
goodness predicate itself. Explicit eta
expansion is handled by a separate native
closure proof, without eta conversion or
positive certificate transport through
observational equality.

These native constructions are reused from
[RigCodes.v](https://github.com/akuklev/pts-rk/blob/5530d1e4130c28a741b48efbd902dd1127ac45c5/theories/OrderedSemiring/RigCodes.v)
and
[DomainClosure.v](https://github.com/akuklev/pts-rk/blob/5530d1e4130c28a741b48efbd902dd1127ac45c5/theories/OrderedSemiring/DomainClosure.v).
No rank budget grows with the nesting depth
of a source term.

## Negative logic and observer equality {#logic}

Use the proof-type encodings

%align*
  \neg_c P &:= P → \Void, \\
  P ∧_c Q &:= (P → Q → \Void) → \Void, \\
  \bigvee_{c, i < k} P_i
    &:= (P_0 → \Void) → \cdots →
      (P_{k-1} → \Void) → \Void, \\
  ∃_c x : A.\,P(x)
    &:= ((x : A) → P(x) → \Void) → \Void.

The empty disjunction is $\Void$.
A proof type $P$ is stable if
$\neg_c\neg_c P → P$ has a PTS inhabitant.
All translated formulas are stable, but this
does not assert stability of every PTS type.

For $A, B : U$, set

%mathpar
  T(A, B) :=
    (\neg_c A → \neg_c B) ∧_c
    (\neg_c B → \neg_c A) : \rk{5}.

An observer has data

%align*
  &X : U,
  \quad r : X → X → \rk{5},
  \quad a : X,
  \quad k : U → X, \\
  &f : X → X,
  \quad d : X → (U → X) → X,
  \quad p : X → U,

and nine certificates:

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

Here $d_w h := d\,w\,h$; the variables
$u, v, w : X$, $z : U$, $h, h' : U → X$ are
universally bound in their respective laws.
All nine proofs are fields of the observer
telescope, not assumptions added to the PTS.

If $\mathcal A$ denotes this complete dependent
telescope, define

%mathpar
  \Eq(x, y) := \mathcal A →
    T\bigl(p(x\,X\,a\,f), p(y\,X\,a\,f)\bigr)
    : \rk{7}.

The telescope notation expands dependent
arrows and introduces no quotient or record
primitive. This equality is stable and an
equivalence. It respects successor, explicit
eta expansion, and addition/multiplication
on appropriately certified arguments.
It is not identified with beta conversion,
nor is every raw function $D → D$ assumed to
preserve it.

## Successor separation {#successor}

The two successor facts require actual
observers, not an assumption that the
observer telescope separates Church terms.
For nonzeroness, take the concrete data

%align*
  X_0 &:= U → U → U, \\
  r_0(v, w) &:= (A, B : U) → T(v\,A\,B, w\,A\,B), \\
  a_0\,A\,B &:= A, & k_0\,C\,A\,B &:= C, \\
  f_0\,v\,A\,B &:= v\,B\,B, \\
  d_0\,w\,h\,A\,B &:= h(w\,A\,B)\,A\,B, \\
  p_0\,v &:= v\,\top\,\Void.

Pointwise reflexivity, symmetry and composition
of $T$ supply its nine certificates.
Zero is observed as $\top$; induction with
$\Good{7}(x)$ gives $T$ between the successor
observation and $\Void$.
An assumed $\Eq(s\,x, 0)$ would therefore
relate $\Void$ and $\top$ via $T$.
Its negative implications, the identity
on $\Void$ and the closed inhabitant of
$\top$ yield a term of $\Void$.

For injectivity, start with any observer
and build its delayed version:

%align*
  X' &:= U → X, \\
  r'(v, w) &:= (z : U) → r(vz, wz), \\
  a' &:= k, & k'\,z &:= λ u : U.k\,z, \\
  f'\,v &:= λ u : U.d\,a\,(λ z : U.f(vz)), \\
  d'\,w\,h &:= λ u : U.d(wu)(λ z : U.h\,z\,u), \\
  p'\,v &:= p(v\,\top).

The original certificates prove all the new
ones. In particular, the state parameter of
$d$ is retained; eta-expanded functions are
compared by its pointwise-congruence law,
not converted by an eta rule.
The delayed carrier still has rank one.

Write $F_n := n\,X\,a\,f$ and
$F'_n := n\,X'\,a'\,f'$.
Induction with $\Good{7}(n)$, using an
explicit lift of the rank-five simulation
motive, proves

%mathpar
  (z : U) → r(F'_{s\,n}z, F_n).

At zero, use $f(kz) ∼ kz$ and $d_a k ∼ a$;
at successor, use pointwise congruence and
the constant-function law for $d_a$.
Apply an assumed $\Eq(s\,x, s\,y)$ to this
delayed observer, and compose its result
with the two simulations through the $p$
bridge. For $\Good{7}(x)$ and $\Good{7}(y)$,
this recovers the result of every original
observer, hence $\Eq(x, y)$.
Both constructions are native terms in
[SuccessorSeparation.v](https://github.com/akuklev/pts-rk/blob/5530d1e4130c28a741b48efbd902dd1127ac45c5/theories/OrderedSemiring/SuccessorSeparation.v).

## Order and the reused arithmetic theorems {#order}

The difference order is

%mathpar
  \Ord(x, y) :=
    ((c : D) → \Good{11}(c) →
      \Eq(\Add\,c\,x, y) → \Void) → \Void
    : \rk{15}.

Its witnesses satisfy $x ⊕ c =_E y$.
They carry $\Good{11}$ even when the endpoints
carry $\Good{15}$. Define
$x < y := \Ord(x, y) ∧_c \neg_c\Eq(x, y)$,
of rank seventeen.

The accompanying relational construction
already supplies the following native proof
terms for this same carrier and equality:

- Successor injectivity and nonzeroness with
  $\Good{7}$ guards, using concrete separating
  and delayed observers with all nine
  certificates explicitly constructed.
- Commutative unital semiring equations,
  additive cancellation, zero-sum reflection
  and the negative zero-product disjunction.
- Reflexivity, transitivity, antisymmetry,
  zero leastness, and operation monotonicity
  for the difference order.
- Strict addition and multiplication laws,
  the latter requiring a positive factor.

The algebraic inductions use a continuation
invariant retaining lower goodness evidence:
for stable $P$ of rank seven, eight or nine,
$I(u) := \Good{7}(u) ∧_c P(u)$ has rank eleven.
Induction with $\Good{11}$ proves $I(x)$,
from which stability yields $P(x)$.
The lower certificate is used only inside
the continuation, not extracted positively.

For strict multiplication, a hypothetical
equality of products would make the product
of a difference and the positive factor zero.
The zero-product disjunction then contradicts
either the original strict inequality or
positivity of the factor. This argument is
stronger than merely proving monotonicity.

Every cutoff is handled by the same rank-fifteen
flattened finite-case invariant

%align*
  K_n(x) &:= (t : D) → \Good{11}(t) →
    \Eq(x, s^{n+1}t) → \Void, \\
  \Cut_n(x) &:=
    (\Eq(x, \nu_0) → \Void) → \cdots →
    (\Eq(x, \nu_n) → \Void) → K_n(x) → \Void.

The finite telescope grows with $n$, not its
rank. Induction on a $\Good{15}$ input shifts
finite branches, sends the last finite branch
to the large branch with witness zero, and
increments the witness in the large branch.
Successor separation rules out the large case
under a contrary finite bound. This proves
the inclusive finite-downset equivalence,
comparison with each numeral, and the strict
finite-downset equivalence, including zero.
No same-domain predecessor or promotion of
$\Good{11}$ to $\Good{15}$ is used.

An expanded account of the common arithmetic
proof terms is available in the
[relational note](https://github.com/akuklev/pts-rk/blob/ordered-semiring-interpretation/theories/OrderedSemiring/README.pdf)
as optional further reading. The functional
proof obligations are described next.

# Arbitrarily nested source terms {#terms}

Let $ρ$ assign target objects to source variables.
The translation is defined structurally:

%align*
  x^*_ρ &:= ρ(x), & 0^*_ρ &:= 0, \\
  S(t)^*_ρ &:= s(t^*_ρ), \\
  (t + u)^*_ρ &:= t^*_ρ ⊕ u^*_ρ, \\
  (t ⋅ u)^*_ρ &:= t^*_ρ ⊗ u^*_ρ.

There is no existentially chosen output for
an arithmetic subterm. Its translation is an
actual application of the target operation.

:::Lemma[Term typing and domain closure] {#term-closure}
If every $ρ(x)$ has type $D$, then every
$t^*_ρ$ has type $D$. If, in addition, every
$ρ(x)$ carries a $\Good{15}$ certificate,
then every $t^*_ρ$ carries such a certificate.
:::

The proof follows the five source-term
constructors. The two new binary cases apply
native operation typing and the concrete
goodness-closure proofs to the induction
hypotheses. They do not require a larger
goodness index or arbitrary induction on
the target carrier.

:::Lemma[Term congruence] {#term-congruence}
Suppose two source environments consist of
typed $\Good{15}$ objects and satisfy
$\Eq(ρ(x), σ(x))$ at every variable.
Then $\Eq(t^*_ρ, t^*_σ)$ for every source term.
:::

At a sum or product, first obtain the translated
subterms' certificates by Lemma <#term-closure>.
Lower them to the budgets needed by the
specific arithmetic congruence lemmas.
Then use the induction hypotheses for both
arguments. The new term-congruence induction
is essential: the relational signature had
no addition or multiplication constructors
inside its source terms.

[Translation.v](Translation.v) also proves
compatibility with renaming and substitution,
including the source-variable lifting under
binders. [Equality.v](Equality.v) uses the
term-congruence theorem to prove formula
transport and equality replacement for
arbitrary functional formulas.

# The independent functional theory {#source}

[Source.v](Source.v) defines `FunctionalSource`.
Its 19 universally closed rig axioms are the
functional forms of the relational model's
23 laws, with the four graph totality and
uniqueness axioms removed:

1. Addition and multiplication commutativity
   and associativity (four laws).
2. Additive zero, multiplicative zero and unit,
   distributivity and additive cancellation
   (five laws).
3. Order reflexivity, transitivity and
   antisymmetry, zero leastness and $0 ≠ 1$
   (five laws).
4. Monotonicity of both operations, strict
   additive monotonicity and strict
   multiplicative monotonicity with a positive
   factor (four laws).
5. The successor equation $x + 1 = S(x)$.

For instance, associativity is the direct
equation $(x + y) + z = x + (y + z)$.
The target's closed operation terms, their
typing and Lemma <#term-closure> supply the total
functional interpretation; graph witnesses
are neither source axioms nor hidden premises.

The original five functional $R$ schemes are

%align*
  &\bar m + \bar n = \overline{m + n}, \\
  &\bar m ⋅ \bar n = \overline{mn}, \\
  &\bar m ≠ \bar n \quad (m ≠ n), \\
  &∀ x.\; x ≤ \bar n → \bigvee_{i ≤ n} x = \bar i, \\
  &∀ x.\; x ≤ \bar n ∨ \bar n ≤ x.

Here $m, n$ are arbitrary external natural
numbers. The fourth original scheme is an
implication. The model additionally proves
the stronger inclusive equivalence and the
strict equivalence from Section <#scope>.
The strict schema is a separate source axiom
constructor for every $n$, including $n = 0$.

Negation means implication to falsity;
conjunction and finite disjunction are the
negative abbreviations of Section <#logic>; the source
existential abbreviation is $¬∀x¬A$.
The independently defined deduction predicate
has exactly nine constructors:

1. An assumption from the source context.
2. An instance of a source theory axiom.
3. Implication introduction.
4. Implication elimination.
5. Universal introduction with renamed context.
6. Universal elimination by a source term.
7. Classical double-negation elimination.
8. Equality reflexivity.
9. Equality replacement in any source formula.

The source syntax shares finite indices with
the native library, but no derivability rule
mentions target typing, semantic validity or
the theorem to be proved.

# Translation of formulas and derivations {#deduction}

The atomic and logical clauses are

%align*
  (t = u)^*_ρ &:= \Eq(t^*_ρ, u^*_ρ), \\
  (t ≤ u)^*_ρ &:= \Ord(t^*_ρ, u^*_ρ), \\
  ⊥^*_ρ &:= \Void, \\
  (A → B)^*_ρ &:= A^*_ρ → B^*_ρ, \\
  (∀ x.\,A)^*_ρ &:=
    (x : D) → \Good{15}(x) → A^*_{ρ[x]}.

Formula typing computes a finite rank
structurally: equality has rank seven, order
fifteen, falsity one, implication has rank
$\max(a + 1, b)$, and universal quantification
has rank $\max(18, b)$.
Arbitrary formulas are not all bounded by
rank eighteen: implication nesting can raise
the result. This does not change the fixed
carrier, equality, goodness or finite-cut
budgets used in the model.

Stability of the translated atoms and closure
of stability under the logical clauses give
double-negation elimination for every translated
source formula. Equality replacement follows
by structural formula transport, using
Lemma <#term-congruence> for both kinds of atom.
Neither step identifies observational equality
with target conversion.

The generic theorem in
[Deduction.v](Deduction.v) takes an explicit
axiom-realization argument and performs
induction on the nine source rules.
Universal elimination is the important
functional case: the instantiated term may
contain arbitrary nested addition and
multiplication. Its actual target term and
goodness certificate are supplied by the
structural term theorems, and the substitution
lemma identifies the resulting formula.

[AxiomRealization.v](AxiomRealization.v) supplies
the actual translated rig and $R$ axioms
from the already proved native arithmetic,
order and bounded-case inhabitants.
The public theorem in
[TheoremFunctionalSemiring.v](TheoremFunctionalSemiring.v)
discharges the generic axiom-realization
argument. Its unconditional type is

```coq
theorem_functional_semiring :
  (forall A, FunctionalSource.axiom A ->
    exists p, @typ nat RankSorts 0 ε p
      (FunctionalTranslation.sentence A)) /\
  (forall A, FunctionalSource.derives [] A ->
    exists p, @typ nat RankSorts 0 ε p
      (FunctionalTranslation.sentence A)).
```

The first premise is membership in an
independent source axiom schema; the second
is an independent source derivation.
Neither assumes a target inhabitant.
All conclusions use the original native
typing judgment, not checker acceptance.

## Ground evaluation and internal refutation {#ground}

A closed functional source term now evaluates
recursively through both arithmetic constructors:

%mathpar
  |t + u| = |t| + |u|,
  \qquad
  |t ⋅ u| = |t| ⋅ |u|.

[GroundFaithfulness.v](GroundFaithfulness.v)
relates the literal target
translation to $\nu_{|t|}$ by beta conversion.
For a true numerical equality or order test,
it constructs the corresponding target proof;
for a false test, it constructs an internal
refutation mapping that atom to $\Void$.
Thus the test applies to all closed nested
terms, not merely displayed numerals.
The four uniform clauses are combined in
`FunctionalGround.ground_faithfulness`.

These internal refutations do not alone prove
external non-inhabitation of $\Void$.
No set model or external consistency theorem
is assumed in the construction, and Rocq's
native arithmetic is used only to justify
side conditions and select the actual target
proof or refutation inhabitants.

# Boundaries and reproduction {#reproduction}

Nothing in the functional signature promotes
$\Good{11}$ differences to $\Good{15}$.
The cutoff-zero case therefore does not give
a predecessor inside the main domain, and
no interpretation of full Robinson $Q$ is
claimed here. Likewise comparison with each
standard numeral is not arbitrary totality,
trichotomy or strict cotransitivity.

The source algebra and all finite-downset
schemes themselves do not force linearity.
For example, let $C$ be zero together with
the integer polynomials eventually positive
at both $+∞$ and $-∞$, with
$p ≤ q$ iff $q - p ∈ C$.
It is a cancellative ordered commutative rig
with strict multiplication and the correct
downset of every standard numeral.
Yet $t^2 + t$ and $t^2 - t$ are incomparable.
Taking $x = t^2$, $y = t^2 + t$ and $z = t^2 + 1$
also refutes strict cotransitivity.
This source counterexample is mathematical
analysis, not a new Rocq theorem or a proof
that the particular PTS interpretation cannot
satisfy a stronger comparison principle.

The library `OrderedSemiringFunctional` is
separate from `OrderedSemiring` and reuses its
native mathematical infrastructure.
There is no dependency on the repository's
other functional $R$ interpretation, set
model, or additional PTS primitives.

The code map is compact:

- [Source.v](Source.v): functional syntax,
  substitution, independent axioms and rules.
- [Translation.v](Translation.v): literal term
  translation, typing, goodness, formula
  translation, stability and substitution.
- [Equality.v](Equality.v): nested-term
  congruence, formula transport and replacement.
- [AxiomRealization.v](AxiomRealization.v):
  actual source-axiom realizers.
- [Deduction.v](Deduction.v): induction on
  independent source deductions.
- [GroundFaithfulness.v](GroundFaithfulness.v):
  nested-term evaluation and ground internal
  proofs and refutations.
- [TheoremFunctionalSemiring.v](TheoremFunctionalSemiring.v):
  the unconditional public interpretation.

On 20 October 2026, a clean Git archive of
proof revision
[9cf6a19](https://github.com/akuklev/pts-rk/tree/9cf6a1987ce8be33be8f3a178cbe84257788ace1/theories/OrderedSemiringFunctional)
was built in a fresh absolute Dune directory.
Compilation and the subsequent recursive
`rocq check` both exited successfully.
The audit includes both ordered-semiring
interpretations and their shared dependencies,
without relying on loose working-tree files.

The final interpretation, strict bounded-case,
numeral-comparison and ground-faithfulness
theorems all have closed `Print Assumptions`
reports. The complete fresh build emitted 137
closed reports and no axiom dependencies.
There are no admitted proofs, new axioms,
disabled safety checks or target-theorem
hypotheses. The environment was Rocq 9.2.0,
Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2 and Dune 3.23.1.

From the repository root, the native audit is

```sh
bash theories/OrderedSemiringFunctional/check.sh
```

The driver records versions, exact commands
and exit codes, regenerates assumption output
in a fresh build, and recursively kernel-checks
the public theorems and dependencies. Set
`ORDERED_FUNCTIONAL_LOG_DIR` to choose the
evidence directory. It performs no package
installation or network access.

To build this documentation from the repository
root, run

```sh
bash theories/OrderedSemiringFunctional/doc/build.sh
```

The build uses the same bundled Markdown class,
plugin, fonts and mathematical typography as
the relational note. It checks the shared
runtime's hashes, snapshots all inputs into
a fresh temporary directory, disables shell
escape and performs three LuaLaTeX passes.
The rendered-source audit rejects literal
environment fences, escaped mathematics and
empty display blocks; final-pass diagnostics
reject missing glyphs and unresolved references.
No second copy of the Markdown runtime is
vendored, and no network, bibliography tool
or external syntax highlighter is required.
The resulting local document is
[README.pdf](https://github.com/akuklev/pts-rk/blob/ordered-semiring-interpretation/theories/OrderedSemiringFunctional/README.pdf).
