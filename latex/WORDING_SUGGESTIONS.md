# Wording suggestions

For discussion; no edits applied from this report. Comma/article-only edits are recorded as implemented in MINOR_CORRECTIONS.md.

[CriticMarkup](https://fletcher.github.io/MultiMarkdown-6/syntax/critic.html).

## paper-markdown.tex:45-51 · G-L43 · Suggested by Grazie

- [x] Pure type systems (PTS [@berardi1988towards; @terlouw1989gstt])
are minimalistic typed $λ$-calculi that
include only abstraction $λ(x : T).u$,
application $u\,t$, dependent function types
$Π(x : T).U$ (where $U$ might depend on $x$) and
*sorts* $s ∈ \mathcal{S}$ that act as “types of
types”.`{>>Consider splitting this long sentence.<<}`

## paper-markdown.tex:202-203 · D04-L204 · Suggested by DeepL Write

- [ ] `{~~Observing~>Upon observing~~}` this, we `{~~took interest~>became interested~~}` in the following
two questions:

## paper-markdown.tex:209-213 · D04-L211 · Suggested by DeepL Write

- [ ] - `{~~Is~>Secondly, is~~}` there a consistent pure type system with
  total relations $\mathsf{Ax}$ and
  $\mathsf{Rule}$ whose natural set-theoretical
  semantics do not involve the assumption of
  inaccessible cardinals?

## paper-markdown.tex:291-292 · D07-L293 · Suggested by DeepL Write

- [ ] `{~~Also, we~>We also~~}` chatted with Claude Fable 5.1 [@claude_fable]
to `{~~find better~>identify more suitable~~}` points of reference.

## paper-markdown.tex:362-363 · L367-S1-P1 · Suggested by Grazie

- [ ] %textsc{Beta}; other rules simply state `{~~the~>that~~}` we can
freely reduce any subterm.

## paper-markdown.tex:399-400 · D08-L401 · Suggested by DeepL Write

- [ ] Then, any `{~~“mountains”~>'mountains'~~}` in the path $t =_β u$ can be
switched into `{~~“valleys”.~>'valleys'.~~}`

## paper-markdown.tex:465-468 · D09-L467 · Suggested by DeepL Write

- [ ] `{~~Again, they surely~>These properties~~}` have `{++certainly ++}`been proven before for PTS [@barendregt1992lambda; @geuvers1991modular],
but `{~~we slightly differ in the~>our~~}` formulation of
the typing rules `{++differs slightly ++}`in important places, so it is better
to recheck that these `{++properties ++}`hold.

## paper-markdown.tex:506-512 · G-L508 · Suggested by Grazie

- [ ] In addition, a family of so-called *inversion
lemmas* [@barendregt1992lambda; @vanbenthemjutting1993typing]
stating that a type of well-typed term is largely
determined by the shape of a term are also proven by
straightforward induction on typing derivation
(each one is proven separately,
no mutual induction involved):`{>>Consider splitting this long sentence.<<}`

## paper-markdown.tex:506-512 · L511-S1-P1 · Suggested by Grazie

- [ ] In addition, a family of so-called *inversion
lemmas* [@barendregt1992lambda; @vanbenthemjutting1993typing]
stating that a type of well-typed term is largely
determined by the shape of a term `{~~are~>is~~}` also proven by
straightforward induction on typing derivation
(each one is proven separately,
no mutual induction involved):

## paper-markdown.tex:541-542 · D10-L543 · Suggested by DeepL Write

- [ ] To progress further, we need to make certain
assumptions `{~~on~>about~~}` the PTS `{--we have--}` in question.

## paper-markdown.tex:593-593 · D11-L595 · Suggested by DeepL Write

- [ ] - The case for $t = x ∈ \mathsf{Var}$ `{~~holds trivially.~>is trivial.~~}`

## paper-markdown.tex:607-615 · L612-S2-P1 · Suggested by Grazie

- [ ] In our proof of normalization, we are going to
rely on yet another property: if there is a
derivation for $t : T$, then $T$ is itself
typeable with some sort.
However, it does not hold in our current
formulation of typing rules: in $Γ ⊢ x : T$,
nothing prevents a context $Γ$ `{~~to contain~>from containing~~}` an entry
$(x : T')$ where $T'$ is not typeable.
Thus, we need an additional assumption.

## paper-markdown.tex:628-628 · D11-L630 · Suggested by DeepL Write

- [ ] (where $⋅$ denotes an empty `{~~context.)~>context).~~}`

## paper-markdown.tex:651-651 · D12-L653 · Suggested by DeepL Write

- [ ] `{~~By~>This is proven by~~}` structural induction on the typing derivation.

## paper-markdown.tex:700-703 · L705-S1-P1 · Suggested by Grazie

- [ ] The only tricky case `{~~are~>is~~}` reductions of a domain
type in $Π (x : T).U$ and $λ (x : T).t$.
Let us consider the case of the following
reduction:

## paper-markdown.tex:708-713 · L713-S1-P1 · Suggested by Grazie

- [ ] `{~~In order to~>To~~}` complete this case, we have to prove
that $Γ, x : T' ⊢ t : U$ given that
$Γ, x : T ⊢ t : U$.
By appropriately strengthening the statement,
we get that it is enough to prove admissibility of
the following rule called *context reduction*:

## paper-markdown.tex:811-820 · L816-S2-P1 · Suggested by Grazie

- [ ] Application, of course, is the only nontrivial
case.
In the case of $β$-reduction, strong normalization of
both $(λ (x : T).t)$ and $u$ does not imply
anything about normalization behaviour of
$t[u/x]$: consider a classical example from
untyped lambda calculus [@barendregt1984lambda],
$ω = (λ (x : T).x\,x)$ and $Ω = ω \,ω$;
while `{--obviously--}` not typable, $ω$ is strongly
normalizing, while $Ω$ decidedly is not.

## paper-markdown.tex:822-825 · D15-L824 · Suggested by DeepL Write

- [ ] The situation changes when the head of the application is
not an abstraction at all.
`{~~Thus, we arrive at~>This leads us to~~}` the definition of an *atomic
term*.

## paper-markdown.tex:828-829 · D15-L830 · Suggested by DeepL Write

- [ ] The set of atomic terms is the smallest set `{~~satisfying~>that satisfies~~}`
the following conditions:

## paper-markdown.tex:887-889 · D16-L889 · Suggested by DeepL Write

- [ ] - $n → (n + 1)$.
  By the induction hypothesis, it is `{~~enough~>sufficient~~}` to show
  the following:

## paper-markdown.tex:962-965 · D17-L964 · Suggested by DeepL Write

- [ ] A proof of $\mathrm{AL}_r$ for all $r$ (which is
what we are after) is `{~~done by~>achieved through~~}` complete mutual
induction with $\mathrm{SL}_r$.
Thus, there are two main parts:

## paper-markdown.tex:999-999 · D18-L1001 · Suggested by DeepL Write

- [ ]   - $u_1[t/x]$ is atomic `{~~—~>and is~~}` handled by Lemma <#sn-props>.

## paper-markdown.tex:1025-1027 · D18-L1027 · Suggested by DeepL Write

- [ ] This is a retelling of a proof that our friend
Aleksandr Levin got after half-jokingly `{~~inputting~>entering~~}`
the following prompt into GPT-6 Pro:

## paper-markdown.tex:1062-1088 · L1067-S1-P1 · Suggested by Grazie

- [ ] `{~~In view of~>Given~~}` the high technicality of the proof for
strong normalization which involves wrangling of
unusual definition for strong normalization and
complex induction patterns (and `{~~in view of the
fact~>given~~}` that proof was supplied by the probabilistic
machine), we decided to formalize it so that a
sound simple algorithm would check it for us.
One of the natural choices for formalization of
programming languages is Rocq [@rocq2025manual; @bertot2004interactive],
an interactive theorem prover based on
Polymorphic, Cumulative Calculus of Inductive
Constructions [@sozeau2014universe; @timany2018cumulative].
As is the case with similar typed calculi,
it is both a programming language and a
higher-order logic, and correctness of a proof is
checked by the type checker; in addition to that,
Rocq features powerful metaprogramming facilities
which allow writing custom *tactics* — programs
written in a meta-language which generate terms of
the target language, greatly simplifying the
proofs.
While set-theoretical semantics of Rocq assume the
existence of countable hierarchy of inaccessible
cardinals [@werner1997sets; @timany2017consistency],
our formalization never delves into the hierarchy
and can be formalized in a much more restricted
theory.

## paper-markdown.tex:1090-1097 · L1095-S1-P1 · Suggested by Grazie

- [ ] `{~~In order to~>To~~}` formalize our strong normalization
proof, we first need to provide a general
metatheory of PTS as laid out in Section <#pts-metatheory>.
We could reuse existing projects on PTS
formalizations such as [@siles2012pure; @adams2006pure; @barras1997coqencoq; @felicissimo2024generic]
but we wanted to explore the topic ourselves, which
led to a few minor differences discussed
`{~~previously,~>previously;~~}` thus we started from scratch.

## paper-markdown.tex:1128-1144 · IDE-style-L1130 · Suggested by Grazie

- [ ] What is convenient in this representation is that
it makes it harder to make mistakes when wrangling
with context, defining substitution etc. — all `{--of--}`
the technical details which make working with
syntax with binders so hard (authors of the first
implementation of such calculi, AUTOMATH [@debruijn1972lambda; @debruijn1970automath],
remarked it being notoriously hard to get right).
Also, it has a certain category-theoretical feel to
it: sufficiently generalized operations of
renaming and substitution give the typal
representation of syntax a structure of a
*relative monad* [@altenkirch2015monads; @altenkirch1999monadic].
It is really hard to go wrong when implementing
these operations (and the natural implementation
turns variables into de Bruijn indices [@debruijn1972lambda]);
on top of them, the usual substitution is easily
definable.

## paper-markdown.tex:1146-1158 · L1151-S2-P1 · Suggested by Grazie

- [ ] Most of the proof development in Rocq mirrors what
is written in Section <#pts-metatheory>; in fact,
we first wrote a proof in Rocq and then retold it
in written English here, omitting tedious
technicalities.
The only considerable difference is in the handling of
the set of strongly normalizing terms `{~~since,
obviously,~>since~~}` the proof of Substitution lemma given
above does not follow the structure of inductive
definition <#sn-definition>.
Instead, we use a syntax-directed characterization
of the set of strongly normalizing terms
introduced in [@Joachimski2003Short]:

## paper-markdown.tex:1258-1259 · D24-L1260 · Suggested by DeepL Write

- [ ] The proof then follows `{~~as written in a~>the~~}` non-formal
treatment `{++written ++}`above.

## paper-markdown.tex:1523-1526 · D29-L1525 · Suggested by DeepL Write

- [ ] `{~~Then,~>Therefore,~~}` we only `{~~have~>need~~}` to prove that type checking for
%PTSrk{} is in %textsc{TOWER}.
`{~~Take a look at~>Consider~~}` the following syntax-directed type
synthesis rules:

## paper-markdown.tex:1551-1559 · L1556-S2-P1 · Suggested by Grazie

- [ ] %textsc{TOWER}: this algorithm recurses on the
term $t$, matches on the inferred types as needed
and collects equalities on types it has to check.
Then, it can naïvely check all equalities in bulk:
there `{~~is~>are~~}` at most $\mathcal{O}(|t|)$ such
equalities `{~~on~>in~~}` terms of size
$\mathcal{O}(2^{\mathrm{poly}(|t|)})$,
so this runs in %textsc{TOWER} by Theorem <#tower-convertibility>.
To finish the proof, it is enough to notice that

## paper-markdown.tex:1584-1593 · G-L1586 · Suggested by Grazie

- [ ] A family of functions on natural numbers
$\mathcal{F}$ is *uniformly* representable in
%PTSrk{} if there is an *input natural number
type* $N_I : \rk{r}$ and an *output natural number
type* $N_O : \rk{s}$ together with *encodings*
$∀ n ∈ ℕ.[n]^I : N_I$ and $∀ n.[n]^O : N_O$ such
that all of them are in normal form and for each
$(f : ℕ^k → ℕ) ∈ \mathcal{F}$ there is a
*representation* $F : N_I → … → N_I → N_O$ which
is also in normal form and such that`{>>Consider splitting this long sentence.<<}`

## paper-markdown.tex:1600-1602 · D30-L1602 · Suggested by DeepL Write

- [ ] Note that the requirement for terms to be in normal
form is not `{~~restrictive:~>restrictive;~~}` we can always normalize a
non-normal term.

## paper-markdown.tex:1615-1618 · D30-L1617 · Suggested by DeepL Write

- [ ] By Theorem <#bounded-sn>, the normalization of
$(r + 1)$-bounded terms $\mathcal{SN}_{r + 1}$ is
elementary `{~~recursive, so~>recursive. Therefore,~~}` the following function is
`{++also ++}`elementary `{~~recursive as well:~>recursive:~~}`

## paper-markdown.tex:1643-1647 · D30-L1645 · Suggested by DeepL Write

- [ ] `{~~A~>The next~~}` logical `{--next--}` question `{~~is then:~>is:~~}`
which functions are computable?
Elementary recursive!
Though, of course, not in the same sense as
before.

## paper-markdown.tex:1795-1799 · L1800-S1-P1 · Suggested by Grazie

- [ ] Now, `{--in order--}` to model $m\,\mathrm{mod}\,n$ in
this vein, we need to *generate* $V_n$
dynamically.
Lucky for us, %PTSrk{} is dependently typed so
there is hope.

## paper-markdown.tex:1801-1802 · D33-L1803 · Suggested by DeepL Write

- [ ] `{~~And indeed,~>Indeed,~~}` the following construction was
produced in a discussion with GPT-6 Astra.

## paper-markdown.tex:1817-1825 · G-L1819 · Suggested by Grazie

- [ ] Intention is that $S$ is simply-typed $V_q$ for
$X$, $z$ is its “zero”, $K$ is a “zero” for
$V_{q + 1}$, $c$ is a cyclic shift for $V_q$,
$L$ is a cyclic shift for $V_{q + 1}$,
$ρ$ converts a selector into a numeral,
and $r$ is the result of modulus computed using
structure from the previous step (this is similar
to the trick used to define a predecessor
function).`{>>Consider splitting this long sentence.<<}`

## paper-markdown.tex:1858-1859 · D34-L1860 · Suggested by DeepL Write

- [ ] Then, given a structure for $q$,
the structure for $q + 1$ `{~~is:~>is as follows:~~}`

## paper-markdown.tex:1879-1880 · D34-L1881 · Suggested by DeepL Write

- [ ] Therefore, the following term computes the modulus
with the expected `{~~behaviour:~>behaviour.~~}`

## paper-markdown.tex:1932-1939 · L1937-S1-P1 · Suggested by Grazie

- [ ] While our system appears to be restricted to
elementary recursive functions,
`{++it ++}`turns out that there is another dependently typed
system in which functions on natural numbers are
*primitive* recursive [@buchholtz2024primitive].
Interestingly enough, part of their solution is in
forbidding function types from appearing in the
lowest universe, just like in %PTSrk{}.

## paper-markdown.tex:1942-1943 · D35-L1944 · Suggested by DeepL Write

- [ ] There is also a boundary result `{~~which stems~>stemming~~}` from
information-theoretical considerations.

## paper-markdown.tex:1946-1949 · D35-L1948 · Suggested by DeepL Write

- [ ] If a function $f : ℕ^k → ℕ$ is representable in
%PTSrk{}, `{++then ++}`it is asymptotically bounded above by an
elementary recursive function of the size of the input
encoding.

## paper-markdown.tex:2024-2025 · D37-L2026 · Suggested by DeepL Write

- [ ] `{~~We~>However, we~~}` are going to need an unusual `{~~assumption
however:~>assumption:~~}`

## paper-markdown.tex:2064-2066 · D37-L2066 · Suggested by DeepL Write

- [ ] - Interpret $\rk{i}$ `{~~by~>as~~}` $s_i$.
  The sort axiom holds `{~~since~>for~~}`
  $s_i ∈ U_0 = \operatorname{El}(s_0)$.

## paper-markdown.tex:2103-2105 · D37-L2105 · Suggested by DeepL Write

- [ ] It is easy to check that the typing rules are
respected by `{~~such~>this~~}` interpretation,
making it a sound model.

## paper-markdown.tex:2135-2146 · IDE-style-L2137 · Suggested by Grazie

- [ ] To demonstrate the ability of %PTSrk{} to embed
nontrivial logical theories, we construct a fixed
interpretation of Tarski–Mostowski–Robinson
arithmetic $\R$ in %PTSrk{}: Church numerals and
certified finite observations first interpret its
relational form $\Rt$; definable graphs yield
$\R$.
We do so because interpretation of $\Rt$ is much
simpler than direct interpretation of $\R$ and
already exposes all `{--of--}` the main ideas.
Direct translation is available in supplementary
formalized materials %formalized{rocq-ai:Interpretation_of_R/functional/DirectRTheorem7.v\#L75}.

## paper-markdown.tex:2179-2183 · D39-L2181 · Suggested by DeepL Write

- [ ] `{~~Let us start~>We will begin by~~}` constructing the model inside
%PTSrk{} and proving that the axioms hold in our
model.
First, `{++here are ++}`some preliminaries on the interpretation of
first-order logic formulas: `{--put--}`

## paper-markdown.tex:2227-2229 · D40-L2229 · Suggested by DeepL Write

- [ ] `{~~For lifting~>To lift~~}` propositions $P : \rk{a}$ `{~~into~>to~~}`
arbitrary higher ranks $k ≥ 2$,
`{--let--}`

## paper-markdown.tex:2318-2320 · D41-L2320 · Suggested by DeepL Write

- [ ] `{~~Meaning that,~>This means that~~}` for `{~~“good”~>'good'~~}` values in the new domain $X$,
a negation of $P$ is upwards closed.
Define

## paper-markdown.tex:2328-2329 · D41-L2330 · Suggested by DeepL Write

- [ ] With `{~~such~>this~~}` definition, preorder laws and equality
compatibility `{~~are derivable.~>can be derived.~~}`

## paper-markdown.tex:2346-2349 · L2351-S1-P1 · Suggested by Grazie

- [ ] Proof terms for most propositions are constructed
`{~~in an obvious way.~>obviously.~~}`
The last proposition holds because $O$ is
transitive and $E$ is symmetric.

## paper-markdown.tex:2419-2420 · D42-L2421 · Suggested by DeepL Write

- [ ] Specialising $H : O(\overline{c}, \overline{n})$
`{~~to~>with~~}` these data yields $(⊥ → ⊥) → (⊤ → ⊥)$.

## paper-markdown.tex:2462-2463 · D43-L2464 · Suggested by DeepL Write

- [ ] We are going to use the following positive
invariant `{~~as a~>for~~}` $Q$:

## paper-markdown.tex:2521-2529 · D44-L2523 · Suggested by DeepL Write

- [ ] For bounded order ($\widetilde R4$),
apply Lemma <#case>.
Under $O(d, \overline{n})$, a case `{~~with~>involving~~}`
$O(\overline{n + 1}, d)$ contradicts
$\nc O(\overline{n + 1}, \overline{n})$ by
transitivity.
Conversely, a $E(d, \overline{i})$ branch with
$i ≤ n$ `{~~gives~>yields~~}` $O(d, \overline{n})$ `{~~using~>via~~}` $E ⇒ O$
and ground comparison.

## paper-markdown.tex:2557-2557 · D45-L2559 · Suggested by DeepL Write

- [ ] The interpretation of $\Rt$ is `{++also ++}`not faithful.

## paper-markdown.tex:2676-2677 · D47-L2678 · Suggested by DeepL Write

- [ ] %PTSrk{} interprets $\R$ `{~~by~>using~~}` definable arithmetic
graphs.

## paper-markdown.tex:2702-2729 · L2707-S3-P1 · Suggested by Grazie

- [ ] After noticing that normalization proof yields a
primitive recursive normalization procedure,
we found tighter bounds and found out that it has
the same complexity as normalization of STLC,
which was previously unheard of for a dependently
typed system (Section <#complexity>).
In contrast with existing pure type systems,
our system is able to represent elementary
recursive functions (both in the sense that it is
stronger than STLC and weaker than more classical
dependently typed systems) and seems intimately
connected to it (Section <#computational>).
To check if constructions inside %PTSrk{} even
make sense, we constructed a set-theoretical model
for it which assumes a Generalized Continuum
Hypothesis `{--in order--}` to strictify the hierarchy of
$ℵ$-s which act as interpretations of our function
types (Section <#rk-model>).
Finally, we provide a lower bound on
proof-theoretical strength of %PTSrk{} by
providing a full interpretation of a relational
version of Tarski–Mostowski–Robinson arithmetic
$R$ inside it (Section <#proof-system>);
we did it partly because we suspect our system to
be able to prove its own consistency in the sense
Pakhomov finitistic set theory does [@Pakhomov2019AWeakSet],
therefore, interpretation of $R$ is the natural
first step.
