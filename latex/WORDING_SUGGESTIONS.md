# Wording suggestions

Checked entries are implemented in the coauthor’s last two upstream commits
(`a3fbee5`, `f06c6f2`) and synchronized into PTS-rk.tex.
Author variants and partial implementations are noted. Unchecked entries
remain pending. Line ranges point to the current passage; CriticMarkup
preserves the original proposal. Comma/article-only edits are recorded
in MINOR_CORRECTIONS.md.

[CriticMarkup](https://fletcher.github.io/MultiMarkdown-6/syntax/critic.html).

## PTS-rk.tex:45-53 · G-L43 · Suggested by Grazie

- [x] Pure type systems (PTS [@berardi1988towards; @terlouw1989gstt])
are minimalistic typed $λ$-calculi that
include only abstraction $λ(x : T).u$,
application $u\,t$, dependent function types
$Π(x : T).U$ (where $U$ might depend on $x$) and
*sorts* $s ∈ \mathcal{S}$ that act as “types of
types”.`{>>Consider splitting this long sentence.<<}`

Implemented by the author’s two-sentence introduction.

## PTS-rk.tex:208-209 · D04-L204 · Suggested by DeepL Write

- [ ] `{~~Observing~>Upon observing~~}` this, we `{~~took interest~>became interested~~}` in the following
two questions:

Author instead added “an” before “interest”; this rewrite remains pending.

## PTS-rk.tex:215-219 · D04-L211 · Suggested by DeepL Write

- [ ] - `{~~Is~>Secondly, is~~}` there a consistent pure type system with
  total relations $\mathsf{Ax}$ and
  $\mathsf{Rule}$ whose natural set-theoretical
  semantics do not involve the assumption of
  inaccessible cardinals?

## PTS-rk.tex:297-298 · D07-L293 · Suggested by DeepL Write

- [x] `{~~Also, we~>We also~~}` chatted with Claude Fable 5.1 [@claude_fable]
to `{~~find better~>identify more suitable~~}` points of reference.

## PTS-rk.tex:368-369 · L367-S1-P1 · Suggested by Grazie

- [x] %textsc{Beta}; other rules simply state `{~~the~>that~~}` we can
freely reduce any subterm.

## PTS-rk.tex:405-406 · D08-L401 · Suggested by DeepL Write

- [x] Then, any `{~~“mountains”~>'mountains'~~}` in the path $t =_β u$ can be
switched into `{~~“valleys”.~>'valleys'.~~}`

## PTS-rk.tex:471-475 · D09-L467 · Suggested by DeepL Write

- [x] `{~~Again, they surely~>These properties~~}` have `{++certainly ++}`been proven before for PTS [@barendregt1992lambda; @geuvers1991modular],
but `{~~we slightly differ in the~>our~~}` formulation of
the typing rules `{++differs slightly ++}`in important places, so it is better
to recheck that these `{++properties ++}`hold.

Author variant: “slightly differs”.

## PTS-rk.tex:513-520 · G-L508 · Suggested by Grazie

- [x] In addition, a family of so-called *inversion
lemmas* [@barendregt1992lambda; @vanbenthemjutting1993typing]
stating that a type of well-typed term is largely
determined by the shape of a term are also proven by
straightforward induction on typing derivation
(each one is proven separately,
no mutual induction involved):`{>>Consider splitting this long sentence.<<}`

## PTS-rk.tex:513-520 · L511-S1-P1 · Suggested by Grazie

- [x] In addition, a family of so-called *inversion
lemmas* [@barendregt1992lambda; @vanbenthemjutting1993typing]
stating that a type of well-typed term is largely
determined by the shape of a term `{~~are~>is~~}` also proven by
straightforward induction on typing derivation
(each one is proven separately,
no mutual induction involved):

Resolved by the two-sentence rewrite: “there is a family … They are …”.

## PTS-rk.tex:549-550 · D10-L543 · Suggested by DeepL Write

- [x] To progress further, we need to make certain
assumptions `{~~on~>about~~}` the PTS `{--we have--}` in question.

## PTS-rk.tex:601-601 · D11-L595 · Suggested by DeepL Write

- [x] - The case for $t = x ∈ \mathsf{Var}$ `{~~holds trivially.~>is trivial.~~}`

## PTS-rk.tex:615-624 · L612-S2-P1 · Suggested by Grazie

- [x] In our proof of normalization, we are going to
rely on yet another property: if there is a
derivation for $t : T$, then $T$ is itself
typeable with some sort.
However, it does not hold in our current
formulation of typing rules: in $Γ ⊢ x : T$,
nothing prevents a context $Γ$ `{~~to contain~>from containing~~}` an entry
$(x : T')$ where $T'$ is not typeable.
Thus, we need an additional assumption.

## PTS-rk.tex:637-637 · D11-L630 · Suggested by DeepL Write

- [x] (where $⋅$ denotes an empty `{~~context.)~>context).~~}`

## PTS-rk.tex:660-660 · D12-L653 · Suggested by DeepL Write

- [ ] `{~~By~>This is proven by~~}` structural induction on the typing derivation.

## PTS-rk.tex:709-712 · L705-S1-P1 · Suggested by Grazie

- [x] The only tricky case `{~~are~>is~~}` reductions of a domain
type in $Π (x : T).U$ and $λ (x : T).t$.
Let us consider the case of the following
reduction:

Author variant: “cases are”.

## PTS-rk.tex:717-722 · L713-S1-P1 · Suggested by Grazie

- [x] `{~~In order to~>To~~}` complete this case, we have to prove
that $Γ, x : T' ⊢ t : U$ given that
$Γ, x : T ⊢ t : U$.
By appropriately strengthening the statement,
we get that it is enough to prove admissibility of
the following rule called *context reduction*:

## PTS-rk.tex:820-829 · L816-S2-P1 · Suggested by Grazie

- [x] Application, of course, is the only nontrivial
case.
In the case of $β$-reduction, strong normalization of
both $(λ (x : T).t)$ and $u$ does not imply
anything about normalization behaviour of
$t[u/x]$: consider a classical example from
untyped lambda calculus [@barendregt1984lambda],
$ω = (λ (x : T).x\,x)$ and $Ω = ω \,ω$;
while `{--obviously--}` not typable, $ω$ is strongly
normalizing, while $Ω$ decidedly is not.

## PTS-rk.tex:831-834 · D15-L824 · Suggested by DeepL Write

- [x] The situation changes when the head of the application is
not an abstraction at all.
`{~~Thus, we arrive at~>This leads us to~~}` the definition of an *atomic
term*.

## PTS-rk.tex:837-838 · D15-L830 · Suggested by DeepL Write

- [x] The set of atomic terms is the smallest set `{~~satisfying~>that satisfies~~}`
the following conditions:

## PTS-rk.tex:896-898 · D16-L889 · Suggested by DeepL Write

- [x] - $n → (n + 1)$.
  By the induction hypothesis, it is `{~~enough~>sufficient~~}` to show
  the following:

## PTS-rk.tex:971-974 · D17-L964 · Suggested by DeepL Write

- [x] A proof of $\mathrm{AL}_r$ for all $r$ (which is
what we are after) is `{~~done by~>achieved through~~}` complete mutual
induction with $\mathrm{SL}_r$.
Thus, there are two main parts:

## PTS-rk.tex:1008-1008 · D18-L1001 · Suggested by DeepL Write

- [ ]   - $u_1[t/x]$ is atomic `{~~—~>and is~~}` handled by Lemma <#sn-props>.

## PTS-rk.tex:1034-1036 · D18-L1027 · Suggested by DeepL Write

- [x] This is a retelling of a proof that our friend
Aleksandr Levin got after half-jokingly `{~~inputting~>entering~~}`
the following prompt into GPT-6 Pro:

## PTS-rk.tex:1069-1097 · L1067-S1-P1 · Suggested by Grazie

- [x] `{~~In view of~>Given~~}` the high technicality of the proof for
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

## PTS-rk.tex:1099-1106 · L1095-S1-P1 · Suggested by Grazie

- [x] `{~~In order to~>To~~}` formalize our strong normalization
proof, we first need to provide a general
metatheory of PTS as laid out in Section <#pts-metatheory>.
We could reuse existing projects on PTS
formalizations such as [@siles2012pure; @adams2006pure; @barras1997coqencoq; @felicissimo2024generic]
but we wanted to explore the topic ourselves, which
led to a few minor differences discussed
`{~~previously,~>previously;~~}` thus we started from scratch.

## PTS-rk.tex:1137-1153 · IDE-style-L1130 · Suggested by Grazie

- [x] What is convenient in this representation is that
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

## PTS-rk.tex:1155-1167 · L1151-S2-P1 · Suggested by Grazie

- [x] Most of the proof development in Rocq mirrors what
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

## PTS-rk.tex:1267-1268 · D24-L1260 · Suggested by DeepL Write

- [x] The proof then follows `{~~as written in a~>the~~}` non-formal
treatment `{++written ++}`above.

Author variant: “given above”.

## PTS-rk.tex:1530-1533 · D29-L1525 · Suggested by DeepL Write

- [x] `{~~Then,~>Therefore,~~}` we only `{~~have~>need~~}` to prove that type checking for
%PTSrk{} is in %textsc{TOWER}.
`{~~Take a look at~>Consider~~}` the following syntax-directed type
synthesis rules:

## PTS-rk.tex:1558-1566 · L1556-S2-P1 · Suggested by Grazie

- [ ] %textsc{TOWER}: this algorithm recurses on the
term $t$, matches on the inferred types as needed
and collects equalities on types it has to check.
Then, it can naïvely check all equalities in bulk:
there `{~~is~>are~~}` at most $\mathcal{O}(|t|)$ such
equalities `{~~on~>in~~}` terms of size
$\mathcal{O}(2^{\mathrm{poly}(|t|)})$,
so this runs in %textsc{TOWER} by Theorem <#tower-convertibility>.
To finish the proof, it is enough to notice that

Partly implemented: “is” → “are”; “on” → “in” remains pending.

## PTS-rk.tex:1591-1600 · G-L1586 · Suggested by Grazie

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

## PTS-rk.tex:1607-1609 · D30-L1602 · Suggested by DeepL Write

- [ ] Note that the requirement for terms to be in normal
form is not `{~~restrictive:~>restrictive;~~}` we can always normalize a
non-normal term.

## PTS-rk.tex:1622-1626 · D30-L1617 · Suggested by DeepL Write

- [x] By Theorem <#bounded-sn>, the normalization of
$(r + 1)$-bounded terms $\mathcal{SN}_{r + 1}$ is
elementary `{~~recursive, so~>recursive. Therefore,~~}` the following function is
`{++also ++}`elementary `{~~recursive as well:~>recursive:~~}`

## PTS-rk.tex:1651-1655 · D30-L1645 · Suggested by DeepL Write

- [x] `{~~A~>The next~~}` logical `{--next--}` question `{~~is then:~>is:~~}`
which functions are computable?
Elementary recursive!
Though, of course, not in the same sense as
before.

## PTS-rk.tex:1803-1807 · L1800-S1-P1 · Suggested by Grazie

- [x] Now, `{--in order--}` to model $m\,\mathrm{mod}\,n$ in
this vein, we need to *generate* $V_n$
dynamically.
Lucky for us, %PTSrk{} is dependently typed so
there is hope.

## PTS-rk.tex:1809-1810 · D33-L1803 · Suggested by DeepL Write

- [x] `{~~And indeed,~>Indeed,~~}` the following construction was
produced in a discussion with GPT-6 Astra.

## PTS-rk.tex:1825-1833 · G-L1819 · Suggested by Grazie

- [ ] Intention is that $S$ is simply-typed $V_q$ for
$X$, $z$ is its “zero”, $K$ is a “zero” for
$V_{q + 1}$, $c$ is a cyclic shift for $V_q$,
$L$ is a cyclic shift for $V_{q + 1}$,
$ρ$ converts a selector into a numeral,
and $r$ is the result of modulus computed using
structure from the previous step (this is similar
to the trick used to define a predecessor
function).`{>>Consider splitting this long sentence.<<}`

## PTS-rk.tex:1866-1867 · D34-L1860 · Suggested by DeepL Write

- [x] Then, given a structure for $q$,
the structure for $q + 1$ `{~~is:~>is as follows:~~}`

## PTS-rk.tex:1887-1888 · D34-L1881 · Suggested by DeepL Write

- [x] Therefore, the following term computes the modulus
with the expected `{~~behaviour:~>behaviour.~~}`

## PTS-rk.tex:1940-1947 · L1937-S1-P1 · Suggested by Grazie

- [x] While our system appears to be restricted to
elementary recursive functions,
`{++it ++}`turns out that there is another dependently typed
system in which functions on natural numbers are
*primitive* recursive [@buchholtz2024primitive].
Interestingly enough, part of their solution is in
forbidding function types from appearing in the
lowest universe, just like in %PTSrk{}.

## PTS-rk.tex:1950-1951 · D35-L1944 · Suggested by DeepL Write

- [x] There is also a boundary result `{~~which stems~>stemming~~}` from
information-theoretical considerations.

## PTS-rk.tex:1954-1957 · D35-L1948 · Suggested by DeepL Write

- [ ] If a function $f : ℕ^k → ℕ$ is representable in
%PTSrk{}, `{++then ++}`it is asymptotically bounded above by an
elementary recursive function of the size of the input
encoding.

## PTS-rk.tex:2032-2032 · D37-L2026 · Suggested by DeepL Write

- [x] `{~~We~>However, we~~}` are going to need an unusual `{~~assumption
however:~>assumption:~~}`

## PTS-rk.tex:2071-2073 · D37-L2066 · Suggested by DeepL Write

- [x] - Interpret $\rk{i}$ `{~~by~>as~~}` $s_i$.
  The sort axiom holds `{~~since~>for~~}`
  $s_i ∈ U_0 = \operatorname{El}(s_0)$.

Author variant: “because”.

## PTS-rk.tex:2110-2112 · D37-L2105 · Suggested by DeepL Write

- [x] It is easy to check that the typing rules are
respected by `{~~such~>this~~}` interpretation,
making it a sound model.

## PTS-rk.tex:2142-2153 · IDE-style-L2137 · Suggested by Grazie

- [x] To demonstrate the ability of %PTSrk{} to embed
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

## PTS-rk.tex:2186-2192 · D39-L2181 · Suggested by DeepL Write

- [x] `{~~Let us start~>We will begin by~~}` constructing the model inside
%PTSrk{} and proving that the axioms hold in our
model.
First, `{++here are ++}`some preliminaries on the interpretation of
first-order logic formulas: `{--put--}`

Author variant: “We now begin”.

## PTS-rk.tex:2234-2236 · D40-L2229 · Suggested by DeepL Write

- [ ] `{~~For lifting~>To lift~~}` propositions $P : \rk{a}$ `{~~into~>to~~}`
arbitrary higher ranks $k ≥ 2$,
`{--let--}`

Partly implemented: “To lift … to”; deletion of “let” remains pending.

## PTS-rk.tex:2325-2327 · D41-L2320 · Suggested by DeepL Write

- [x] `{~~Meaning that,~>This means that~~}` for `{~~“good”~>'good'~~}` values in the new domain $X$,
a negation of $P$ is upwards closed.
Define

Author variant: “This proposition asserts …”, with single quotation marks.

## PTS-rk.tex:2335-2336 · D41-L2330 · Suggested by DeepL Write

- [x] With `{~~such~>this~~}` definition, preorder laws and equality
compatibility `{~~are derivable.~>can be derived.~~}`

## PTS-rk.tex:2353-2356 · L2351-S1-P1 · Suggested by Grazie

- [ ] Proof terms for most propositions are constructed
`{~~in an obvious way.~>obviously.~~}`
The last proposition holds because $O$ is
transitive and $E$ is symmetric.

## PTS-rk.tex:2426-2427 · D42-L2421 · Suggested by DeepL Write

- [x] Specialising $H : O(\overline{c}, \overline{n})$
`{~~to~>with~~}` these data yields $(⊥ → ⊥) → (⊤ → ⊥)$.

## PTS-rk.tex:2469-2470 · D43-L2464 · Suggested by DeepL Write

- [x] We are going to use the following positive
invariant `{~~as a~>for~~}` $Q$:

## PTS-rk.tex:2528-2536 · D44-L2523 · Suggested by DeepL Write

- [x] For bounded order ($\widetilde R4$),
apply Lemma <#case>.
Under $O(d, \overline{n})$, a case `{~~with~>involving~~}`
$O(\overline{n + 1}, d)$ contradicts
$\nc O(\overline{n + 1}, \overline{n})$ by
transitivity.
Conversely, a $E(d, \overline{i})$ branch with
$i ≤ n$ `{~~gives~>yields~~}` $O(d, \overline{n})$ `{~~using~>via~~}` $E ⇒ O$
and ground comparison.

## PTS-rk.tex:2564-2564 · D45-L2559 · Suggested by DeepL Write

- [ ] The interpretation of $\Rt$ is `{++also ++}`not faithful.

## PTS-rk.tex:2683-2684 · D47-L2678 · Suggested by DeepL Write

- [ ] %PTSrk{} interprets $\R$ `{~~by~>using~~}` definable arithmetic
graphs.

## PTS-rk.tex:2709-2736 · L2707-S3-P1 · Suggested by Grazie

- [x] After noticing that normalization proof yields a
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
