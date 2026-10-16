# Minor corrections

Comma and article corrections implemented in the Markdown paper. Broader wording remains pending.

Where services disagreed, the definite article is retained for the previously identified assumption and closure.
The earlier comma/article edits at paper-markdown.tex:1450-1453 were superseded by the author's concise rewrite.

## paper-markdown.tex:171-181 · IDE-grammar-L173 · Suggested by Grazie

- [x] This result is dubbed “Girard's paradox” since it
renders System U inconsistent with respect to its
intended logical semantics: inhabitedness of
$Π (P : ∗).P$ would mean that every proposition is
provable.
`{~~Thus~>Thus,~~}` any system where System U embeds is
inconsistent, too; in particular,
an original version [@martinlof1971theory] of
Martin-Löf's Intuitionistic Type Theory [@martinlof1984intuitionistic]
embeds the following PTS known as “Type-in-Type”
which is inconsistent due to Girard's paradox:

## paper-markdown.tex:209-213 · D04-L211 · Suggested by DeepL Write

- [x] - Is there a consistent pure type system with
  total relations $\mathsf{Ax}$ and
  $\mathsf{Rule}$ whose natural set-theoretical
  semantics do not involve `{++the ++}`assumption of
  inaccessible cardinals?

## paper-markdown.tex:215-218 · L220-S1-P1 · Suggested by Grazie

- [x] Turns out that, for both questions,
`{++the ++}`answer is “yes”.
Furthermore, both yes-s are witnessed by a single
PTS, which we dub %PTSrk{}:

## paper-markdown.tex:296-302 · L301-S2-P1 · Suggested by Grazie

- [x] Every result up to the proof of strong
normalization for %PTSrk{} was formally verified
in Rocq using handwritten proofs.
Such proofs are marked with a %proof{rocq-ai:https://github.com/TurtlePU/pts-rk};
each icon is a hyperlink to the statement and
proof in Rocq with `{++the ++}`version pinned at the moment of
submission.

## paper-markdown.tex:304-312 · L309-S2-P1 · Suggested by Grazie

- [x] Results after that were formalized in Rocq as
well, albeit not by us but rather by GPT-6 Astra.
Such results are marked with %formalized{rocq-ai:https://github.com/TurtlePU/pts-rk/pull/1};
just as with handwritten results, each icon is a
hyperlink to the statement and proof in Rocq with
`{++the ++}`version pinned at the moment of submission.
Where only a component of a paper claim is
checked, a note explaining what exactly is
formalized accompanies the badge.

## paper-markdown.tex:374-374 · D08-L376 · Suggested by DeepL Write

- [x] In `{++an ++}`arbitrary PTS,

## paper-markdown.tex:380-381 · D08-L382 · Suggested by DeepL Write

- [x] where $( →_β^∗ )$ is `{++the ++}`reflexive transitive closure
of $( →_β )$.

## paper-markdown.tex:402-405 · L407-S1-P1 · Suggested by Grazie

- [x] Now, diamond property is proven by `{++the ++}`standard
technique of parallel reduction [@martinlof1971theory]
which is defined as the smallest relation
satisfying:

## paper-markdown.tex:426-440 · IDE-grammar-L428 · Suggested by Grazie

- [x] Intuitively, while $( →_β )$ is a single
$β$-reduction somewhere in the term and
$( →_β )^∗$ is a sequence of reductions,
$( ⇉ )$ is several simultaneous reductions
immediately available in the term.
Notice, then, that $( →_β ) ⊆ ( ⇉ ) ⊆ ( →_β^∗ )$;
by monotonicity of reflexive transitive closure,
$( →_β^∗ ) ⊆ ( ⇉^∗ ) ⊆ ( →_β^∗ )^∗ = ( →_β^∗ )$,
so $( ⇉^∗ ) = ( →_β^∗ )$.
`{~~Thus~>Thus,~~}` it is enough to prove `{++the ++}`diamond property of
$( ⇉^∗ )$.
Diamond property is preserved under reflexive
transitive closure, so it is enough to prove
diamond property of $( ⇉ )$, which holds by
tedious case analysis.

## paper-markdown.tex:443-449 · L448-S1-P1 · Suggested by Grazie

- [x] Setting aside practical applications of this
theorem (to algorithmically check equivalence of
terms, we can now search for `{++a ++}`common reduction
result), it will prove useful already in our proof
development.
For example, the following “equality inversion”
lemmas are direct corollaries:

## paper-markdown.tex:465-468 · D09-L467 · Suggested by DeepL Write

- [x] Again, they surely have been proven before for PTS [@barendregt1992lambda; @geuvers1991modular],
but we slightly differ in the formulation of
`{++the ++}`typing rules in important `{~~places~>places,~~}` so it is better
to recheck that these hold.

## paper-markdown.tex:496-503 · L501-S1-P1 · Suggested by Grazie

- [x] %textsc{Var} is still applicable;
for places in $t$ where $x$ used to `{~~be~>be,~~}` we need to
apply `{++a ++}`weakening lemma to the typing derivation for
$u$ exactly $|Δ|$ times.
In the case of %textsc{Conv} it is important that
definitional equality of types is preserved by
substitution (thanks to characterization of
$( =_β )$).

## paper-markdown.tex:506-512 · G-L508 · Suggested by Grazie

- [x] In addition, a family of so-called *inversion
lemmas* [@barendregt1992lambda; @vanbenthemjutting1993typing]
stating that `{++a ++}`type of well-typed term is largely
determined by `{++the ++}`shape of a term are also proven by
straightforward induction on typing derivation
(each one is proven separately,
no mutual induction involved):

## paper-markdown.tex:578-579 · D10-L580 · Suggested by DeepL Write

- [x] By structural induction on $t$ and inversion of
`{++the ++}`given typing derivations.

## paper-markdown.tex:584-591 · L589-S3-P1 · Suggested by Grazie

- [x] - $t = Π (x : T).U$: inversion of typing gives a
  pair of (possibly different) sorts for $T$ and
  another pair for $U$.
  By induction we get that ranks inside pairs are
  definitionally equal, which by equality
  inversion gives strictly equal sorts.
  Then what is needed holds by `{++the ++}`functionality of
  $\mathsf{Rule}$.

## paper-markdown.tex:593-593 · D11-L595 · Suggested by DeepL Write

- [x] - `{~~Case~>The case~~}` for $t = x ∈ \mathsf{Var}$ holds trivially.

## paper-markdown.tex:607-615 · IDE-grammar-L609 · Suggested by Grazie

- [x] In our proof of normalization, we are going to
rely on yet another property: if there is a
derivation for $t : T$, then $T$ is itself
typeable with some sort.
However, it does not hold in our current
formulation of typing rules: in $Γ ⊢ x : T$,
nothing prevents a context $Γ$ to contain an entry
$(x : T')$ where $T'$ is not typeable.
`{~~Thus~>Thus,~~}` we need an additional assumption.

## paper-markdown.tex:618-621 · L623-S2-P1 · Suggested by Grazie

- [x] Context $Γ$ is *well-formed* (written $⊢ Γ$) if
every type in it is typed by some sort.
Formally, `{++a ++}`set of well-formed contexts is the least
set closed by the following rules:

## paper-markdown.tex:651-651 · D12-L653 · Suggested by DeepL Write

- [x] By structural induction on `{++the ++}`typing derivation.

## paper-markdown.tex:660-666 · L665-S3-P1 · Suggested by Grazie

- [x] - %textsc{App}: $Γ ⊢ t\,u : T[u/x]$.
  From induction hypothesis for $t$ we know that
  $Γ ⊢ t : Π (x : U).T : s$ for some $s$,
  then by typing inversion for $Π (x : U).T$ we
  get that $T$ is typable with some sort.
  Then what is needed follows from `{++a ++}`substitution
  lemma.

## paper-markdown.tex:672-678 · L677-S1-P1 · Suggested by Grazie

- [x] Totality is not a strictly necessary requirement —
similar true propositions can be stated for
non-total PTS, for `{~~example~>example,~~}` in CoC typing yields
type which is either itself typable or equal to
$□$ [@barendregt1992lambda; @luo1994computation].
But %PTSrk{} is indeed total so the theorem above
is enough for our purposes.

## paper-markdown.tex:690-698 · L695-S2-P1 · Suggested by Grazie

- [x] By structural induction over derivation of
$t →_β t'$.
Inversion of a typing judgement yields all
necessary info, albeit because of it types are now
given only up to definitional `{~~equality~>equality,~~}` so we have
to apply `{++the ++}`conversion rule in each case.
Crucially, it requires the type we convert into to
be typable by a sort, so that is where we use
Theorem <#type-is-correct>.

## paper-markdown.tex:721-729 · L726-S2-P1 · Suggested by Grazie

- [x] The proof is, again, by induction on the typing
derivation.
The only non-trivial case is with %textsc{Var}
rule used on $x$; it is taken care of by
`{++the ++}`appropriate use of %textsc{Conv} rule to convert
$x : U'$ to $x : U$.
To use conversion, we have to prove that $U$ is
well-typed; thankfully, it follows from
$⊢ Γ, x : U, Δ$.

## paper-markdown.tex:811-820 · L816-S2-P1 · Suggested by Grazie

- [x] Application, of course, is the only nontrivial
case.
In `{++the ++}`case of $β$-reduction, strong normalization of
both $(λ (x : T).t)$ and $u$ does not imply
anything about normalization behaviour of
$t[u/x]$: consider a classical example from
untyped lambda calculus [@barendregt1984lambda],
$ω = (λ (x : T).x\,x)$ and $Ω = ω \,ω$;
while obviously not typable, $ω$ is strongly
normalizing, while $Ω$ decidedly is not.

## paper-markdown.tex:822-825 · D15-L824 · Suggested by DeepL Write

- [x] `{~~Situation~>The situation~~}` changes when `{~~a~>the~~}` head of `{++the ++}`application is
not an abstraction at all.
`{~~Thus~>Thus,~~}` we arrive at the definition of an *atomic
term*.

## paper-markdown.tex:828-829 · D15-L830 · Suggested by DeepL Write

- [x] `{~~Set~>The set~~}` of atomic terms is the smallest set satisfying
the following conditions:

## paper-markdown.tex:887-889 · D16-L889 · Suggested by DeepL Write

- [x] - $n → (n + 1)$.
  By `{++the ++}`induction hypothesis, it is enough to show
  the following:

## paper-markdown.tex:925-931 · L930-S2-P1 · Suggested by Grazie

- [x] Now, here is the part where stratification
according to ranks comes in useful.
As typing yields `{++the ++}`correct type, there is some $r$
such that $Γ ⊢ Π (x : T).U : \rk{r}$.
Let us explicitly add this to the list of
premises; we will call the following proposition
*Application Lemma*:

## paper-markdown.tex:943-950 · L948-S2-P1 · Suggested by Grazie

- [x] What indexing by $r$ bought us is that now we can
try proving this lemma by induction on $r$.
Again, as it always is with strong normalization
of application, the problem is in case where
`{++the ++}`application head is a lambda and a $β$-reduction
takes place.
This calls for another lemma,
*Substitution Lemma*:

## paper-markdown.tex:962-965 · D17-L964 · Suggested by DeepL Write

- [x] A proof of $\mathrm{AL}_r$ for all $r$ (which is
what we are after) is done by complete mutual
induction with $\mathrm{SL}_r$.
`{~~Thus~>Thus,~~}` there are two main parts:

## paper-markdown.tex:967-983 · L972-S5-P1 · Suggested by Grazie

- [x] - $(∀ s < r.\;\mathrm{SL}_s) ⇒ \mathrm{AL}_r$:
  by induction on derivations of
  $u, t ∈ \mathsf{sn}$.
  Consider possible reductions of $u\,t$:
  most of them happen either in $u$ or in $t$,
  so that results of reductions from $u\,t$ are
  strongly normalizing by inductive hypotheses.
  The only problematic case is when
  $u = λ (x : T').v$ and the reduction is
  $β$-reduction.
  By inversion of typing for $u$, it should be the
  case that $T' =_β T$; and by inversion of typing
  for $Π (x : T).U$, we get that $T : \rk{s}$ and
  $U : \rk{t}$ such that $r = \max(s + 1, t)$.
  Then, by type stability, $T' : \rk{s}$,
  and furthermore, $s < r$, so we can apply
  `{++a ++}`substitution lemma.

## paper-markdown.tex:1025-1027 · D18-L1027 · Suggested by DeepL Write

- [x] This is a retelling of a proof that our `{~~friend,~>friend~~}`
Aleksandr `{~~Levin,~>Levin~~}` got after half-jokingly inputting
the following prompt into GPT-6 Pro:

## paper-markdown.tex:1039-1058 · L1044-S3-P1 · Suggested by Grazie

- [x] After approximately 20 minutes,
LLM outputted the proof which we retold above.
Looking at it in retrospect, it seems as if we
stratified functions by ranks with intent for such
a direct proof to go through; honestly,
we did not think of that and were eagerly trying
to adapt well-known approaches for proving
normalization of pure type systems employing
either saturated sets or candidates of
reducibility [@tait1967intensional; @girard1972interpretation; @girard1989proofs; @geuvers1991modular],
which did not work because our “hierarchy” of
ranks is not well-founded enough because of axioms
$\rk{n} : \rk{0}$.
This proof, however, does not even bother with `{~~it~>it,~~}`
which means that we could pick *any* relation as
$\mathsf{Ax}$.
Nevertheless, putting all sorts into $\rk{0}$
seems the most sensible approach to us since,
informally, sort is kind of a constant which can
not be converted into a function.

## paper-markdown.tex:1062-1088 · L1067-S1-P1 · Suggested by Grazie

- [x] In view of `{++the ++}`high technicality of the proof for
strong normalization which involves wrangling of
unusual definition for strong normalization and
complex induction patterns (and in view of the
fact that proof was supplied by the probabilistic
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
While set-theoretical semantics of Rocq assume `{~~an~>the~~}`
existence of countable hierarchy of inaccessible
cardinals [@werner1997sets; @timany2017consistency],
our formalization never delves into the hierarchy
and can be formalized in a much more restricted
theory.

## paper-markdown.tex:1090-1097 · L1095-S1-P1 · Suggested by Grazie

- [x] In order to formalize our strong normalization
proof, we first need to provide a general
metatheory of PTS as laid out in Section <#pts-metatheory>.
We could reuse existing projects on PTS
formalizations such as [@siles2012pure; @adams2006pure; @barras1997coqencoq; @felicissimo2024generic]
but we wanted to explore the topic `{~~ourselves~>ourselves,~~}` which
led to a few minor differences discussed
previously, thus we started from scratch.

## paper-markdown.tex:1118-1126 · L1123-S2-P1 · Suggested by Grazie

- [x] Here, $L$ is a type of sorts ($L$ comes from
*level* which is a name used for it in universe
hierarchies), and $n$ is a number of free
variables.
Entering `{++a ++}`new scope (such as in $Π$ and in
$\mathtt{lam}$) adds one new free variable;
variables, then, have to be numbers in range
$[0;n)$, which are usually represented by a
$\mathtt{Fin}$ type.

## paper-markdown.tex:1128-1144 · IDE-grammar-L1130 · Suggested by Grazie

- [x] What is convenient in this representation is that
it makes it harder to make mistakes when wrangling
with context, defining substitution etc. — all of
the technical details which make working with
syntax with binders so hard (authors of `{++the ++}`first
implementation of such calculi, AUTOMATH [@debruijn1972lambda; @debruijn1970automath],
remarked it being notoriously hard to get right).
`{~~Also~>Also,~~}` it has a certain category-theoretical feel to
it: sufficiently generalized operations of
renaming and substitution give the typal
representation of syntax a structure of a
*relative monad* [@altenkirch2015monads; @altenkirch1999monadic].
It is really hard to go wrong when implementing
these operations (and the natural implementation
turns variables into de Bruijn indices [@debruijn1972lambda]);
on top of them, `{++the ++}`usual substitution is easily
definable.

## paper-markdown.tex:1146-1158 · L1151-S2-P1 · Suggested by Grazie

- [x] Most of the proof development in Rocq mirrors what
is written in Section <#pts-metatheory>; in fact,
we first wrote a proof in Rocq and then retold it
in written English here, omitting tedious
technicalities.
The only considerable difference is in `{++the ++}`handling of
the set of strongly normalizing terms since,
obviously, the proof of Substitution lemma given
above does not follow the structure of inductive
definition <#sn-definition>.
Instead, we use a syntax-directed characterization
of the set of strongly normalizing terms
introduced in [@Joachimski2003Short]:

## paper-markdown.tex:1229-1233 · L1234-S2-P1 · Suggested by Grazie

- [x] Proof is extremely simple: by Lemmas <#sn-props>,<#sn-atomic>,<#sn-whe>.
We just have to notice that if `{++the ++}`term is
$\mathsf{SNx}$, it is atomic,
so lemma <#sn-atomic> applies in the relevant
case.

## paper-markdown.tex:1236-1240 · L1241-S1-P1 · Suggested by Grazie

- [x] Then, to prove strong normalization,
it is enough to prove that if `{++a ++}`term is typable,
it is $\mathsf{SN}$; we only have to state
Application Lemma and Substitution Lemma in terms
of $\mathsf{SN}$, and the proof goes through.

## paper-markdown.tex:1264-1266 · D24-L1266 · Suggested by DeepL Write

- [x] In this `{~~section~>section,~~}` we prove that `{++the ++}`convertibility of
`{~~closed~>closed,~~}` well-typed %PTSrk{} terms is
%textsc{TOWER}-complete.

## paper-markdown.tex:1268-1274 · L1273-S1-P1 · Suggested by Grazie

- [x] (Proofs in this and following sections were not
verified in Rocq by any of the authors,
but there is a formalization of some results by
GPT-6 Astra. Informal proofs, however,
are relatively simple, `{~~non-technical~>non-technical,~~}` and their
formalization requires many times more preliminary
work than seems reasonable.)

## paper-markdown.tex:1276-1284 · L1281-S1-P1 · Suggested by Grazie

- [x] As requested further, LLM confessed that it was
largely inspired by studies on `{++the ++}`complexity of
normalization for STLC [@statman1979typed; @schwichtenberg1991upper; @beckmann2001exact; @nguyen2024simply].
And indeed, upon taking a closer look at the proof
of Theorem <#normalisation>, one cannot help but
notice it actually being a primitive recursive
algorithm [@skolem1923; @kleene1952introduction; @peter1951rekursive]
for term normalization in disguise.
Or something a tad faster:

## paper-markdown.tex:1287-1289 · L1292-S1-P1 · Suggested by Grazie

- [x] A %PTSrk{} term is $d$-bounded if it is well-typed
in some well-formed `{~~context~>context,~~}` and `{++the ++}`heads of all
redexes in it have rank equal to or below $d$.

## paper-markdown.tex:1317-1323 · L1322-S1-P1 · Suggested by Grazie

- [x] It differs from `{++the ++}`usual parallel reduction since it
greedily applies every “many-argument” redex
available in a term.
For example,
$(λ (x : X).λ (y : Y).λ (z : Z).t)\,a\,b\,c$ gets
reduced to $t'[a/x][b/y][c/z]$ in a single step.
This relation has the following properties:

## paper-markdown.tex:1330-1335 · L1335-S1-P1 · Suggested by Grazie

- [x] - This relation can be realized with an elementary
  recursive algorithm $\mathcal{A}$:
  traverse the term bottom-up, immediately
  applying every $β$-redex which is formed when
  `{++the ++}`result of a recursive run of `{++the ++}`algorithm on
  `{++the ++}`application head is a lambda.

## paper-markdown.tex:1355-1357 · L1360-S1-P1 · Suggested by Grazie

- [x] To make sure that the corresponding function is
total, output $0$ if `{++the ++}`result of an algorithm
contains a $β$-redex.

## paper-markdown.tex:1375-1385 · L1380-S2-P1 · Suggested by Grazie

- [x] By Theorem <#bounded-sn>, it is enough to compute
some upper bound $B$ on the rank of types
appearing in abstractions of a term,
then run a normalizer for $(B + 1)$-bounded terms
and compare the results; $B$ has to be bound by an
elementary recursive function on the size of
input.
Consider, then, the following elementary recursive
functions to compute such `{++an ++}`upper bound,
written in pseudocode and using a suitable
encoding of terms, tuples and lists:

## paper-markdown.tex:1418-1447 · L1423-S1-P1 · Suggested by Grazie

- [x] Function $\mathtt{maxRankLiteral}\;t$ computes
maximal rank which is contained as a subterm in
`{++the ++}`term $t$.
The workhorse of this algorithm,
$\mathtt{traversal}\;Γ \;t\;d$,
accepts the list $Γ$ of ranks in context of a term
$t$ and a “default rank” $d$,
and outputs the triple $(v, r, a)$,
where $v$ is value of $t$ as a rank (if supplied
with enough arguments), $r$ is its rank if $t$ is
a type (if supplied with enough arguments) and $a$
is an upper bound on rank of types appearing in
abstractions which we are trying to compute.
The only suspicious case is
$\mathtt{traversal}\,Γ \,x\,d$ where we output $d$
(the “default” rank) as a value of $x$:
could we compute `{++the ++}`value of $x$ instead,
if present?
Regrettably, this would require normalization of a
term corresponding to $x$, which is too long;
instead we notice that $\rk{r}$ can be reduced
only from terms which already contain it as a
subterm, so `{++the ++}`value of $x$ as a rank can only be
$\rk{r}$ which is already present somewhere in
`{++the ++}`original term.
And our result is monotone with respect to the
value we output `{~~here~>here,~~}` so it is enough to provide
some upper bound on it; thus it is enough to
output a maximal rank which occurs in `{++the ++}`original
term as a subterm.

## paper-markdown.tex:1500-1503 · L1505-S1-P1 · Suggested by Grazie

- [x] Assigning all type variables rank $\rk{0}$
preserves well-typedness since values of such
types were never treated as functions in `{++the ++}`original
term.

## paper-markdown.tex:1547-1550 · L1552-S1-P1 · Suggested by Grazie

- [x] This relation is functional (in the sense that if
$Γ ⊢ t : T$ and $Γ ⊢ t : T'$,
then $T = T'$ as `{~~words)~>words),~~}` and the corresponding
partial function is realized by an algorithm in

## paper-markdown.tex:1600-1602 · D30-L1602 · Suggested by DeepL Write

- [x] Note that `{++the ++}`requirement for terms to be in normal
form is not restrictive: we can always normalize a
non-normal term.

## paper-markdown.tex:1611-1613 · D30-L1613 · Suggested by DeepL Write

- [x] By `{++a ++}`direct diagonalization argument.
Suppose we could encode all elementary recursive
functions with $N_I : \rk{r}$ and $N_O : \rk{s}$.

## paper-markdown.tex:1615-1618 · D30-L1617 · Suggested by DeepL Write

- [x] By Theorem <#bounded-sn>, `{++the ++}`normalization of
$(r + 1)$-bounded terms $\mathcal{SN}_{r + 1}$ is
elementary recursive, so the following function is
elementary recursive as well:

## paper-markdown.tex:1636-1640 · L1641-S1-P1 · Suggested by Grazie

- [x] `{~~First~>The first~~}` equivalence is by definition of $h$;
`{++the ++}`second is by virtue of expression under
$\mathcal{SN}$ being $(r + 1)$-bounded;
the last is by definition of $h$ being encoded by
$H$.

## paper-markdown.tex:1739-1746 · L1744-S2-P1 · Suggested by Grazie

- [x] As the name implies, the goal of such combinators
is to lower the rank of a numeral,
but preserve its “value”.
It is achieved in the following way:
given an $f$ and $x$ for lower-ranked type,
an original combinator for $n$ is used to build an
$n$-fold composition of $f$ with `{~~itself~>itself,~~}` which is
then applied to $x$.

## paper-markdown.tex:1748-1758 · IDE-grammar-L1750 · Suggested by Grazie

- [x] `{~~Thus~>Thus,~~}` we can lower ranks arbitrarily:
$δ_{b, a} ≜ δ_a ∘ … ∘ δ_{b - 1} : ℕ_b → ℕ_a$.
This restores substitution and allows gluing
representation of elementary recursive functions
together; cost $c_f$ of a function can be computed
from any expression that represents it — addition
and multiplication cost $0$, exponentiation costs
$1$, operands are merged by taking the maximum of
their costs.
(Of course, cost is not unique and depends on the
way `{++the ++}`function is represented with an expression.)

## paper-markdown.tex:1760-1770 · L1765-S2-P1 · Suggested by Grazie

- [x] All that is left, then, is to represent modulus.
`{~~General~>The general~~}` idea is as follows: first,
suppose that we are dealing with a simpler problem
of taking modulus by a constant modulo,
e.g. $\mathrm{mod}\,5$.
Notice that there are only $5$ possible answers:
$0$,$1$,$2$,$3$,$4$.
As such, they can be represented by the type which
contains exactly $5$ elements;
Church encoding [@bohm1985automatic] yields a type
of *selectors*:

## paper-markdown.tex:1801-1802 · D33-L1803 · Suggested by DeepL Write

- [x] And indeed, the following construction was
produced in `{++a ++}`discussion with GPT-6 Astra.

## paper-markdown.tex:1827-1828 · D34-L1829 · Suggested by DeepL Write

- [x] A callback accepting such `{++a ++}`structure and returning
$X$ has the following type:

## paper-markdown.tex:1858-1859 · D34-L1860 · Suggested by DeepL Write

- [x] Then, given a structure for $q$,
`{~~a~>the~~}` structure for $q + 1$ is:

## paper-markdown.tex:1879-1880 · D34-L1881 · Suggested by DeepL Write

- [x] Therefore, the following term computes `{++the ++}`modulus
with `{++the ++}`expected behaviour:

## paper-markdown.tex:1946-1949 · D35-L1948 · Suggested by DeepL Write

- [x] If a function $f : ℕ^k → ℕ$ is representable in
%PTSrk{}, it is asymptotically bounded above by an
elementary recursive function of the size of `{++the ++}`input
encoding.

## paper-markdown.tex:1963-1973 · L1968-S2-P1 · Suggested by Grazie

- [x] Since terms are definitionally equal,
they must have the same normal form which is then
equal to $[f(n_1, …, n_k)]^O$ as a word.
Looking at the proof of Theorem <#bounded-sn>,
its length is then bounded above by
$\mathcal{O}(c ↑ … ↑ c ↑ i(n_1, …, n_k))$ where
$i(n_1, …, n_k)$ is `{++the ++}`length of
$F\,[n_1]^I\,…\,[n_k]^I$ as a word.
`{~~Height~>The height~~}` of the tower of exponents depends not on
the $n_i$-s, but on the $d$-bound which is equal
to $r + 1$ so this bound is %textsc{ELEMENTARY}.

## paper-markdown.tex:1988-1989 · L1993-S1-P1 · Suggested by Grazie

- [x] In `{++a ++}`particular case where elementary recursive
encoding is used, function representable in

## paper-markdown.tex:2015-2022 · L2020-S1-P1 · Suggested by Grazie

- [x] Now, studying computational properties of a
calculus is great, but`{-- a--}` logic is only useful when
it can tell right from wrong.
In this section, we are going to provide`{-- a--}`
nontrivial set-theoretical semantics for %PTSrk{}
with respect to which it is sound,
and where $⟦Π (X : \rk{j}).X⟧$ is going to be an
empty set, as expected.

## paper-markdown.tex:2103-2105 · D37-L2105 · Suggested by DeepL Write

- [x] It is easy to check that `{++the ++}`typing rules are
respected by such interpretation,
making it a sound model.

## paper-markdown.tex:2121-2131 · L2126-S3-P1 · Suggested by Grazie

- [x] Note that usage of GCH is unavoidable in this
model to validate the rules.
We could try building a model in ZFC using
$\beth$-s instead of $ℵ$-s, but that would break
an assumption that $U_i$ are countable,
which would falsify axioms $\rk{n} : \rk{0}$.
That is not a huge `{~~problem however~>problem, however,~~}` since ZF+GCH is
interpretable in ZF [@godel1938consistency; @godel1940consistency]
(in contrast to ZFC + inaccessible cardinals which
is not [@kanamori2003higher; @kunen1980set; @godel1931formal]
).

## paper-markdown.tex:2135-2146 · IDE-style-L2137 · Suggested by Grazie

- [x] To demonstrate `{++the ++}`ability of %PTSrk{} to embed
nontrivial logical theories, we construct a fixed
interpretation of Tarski–Mostowski–Robinson
arithmetic $\R$ in %PTSrk{}: Church numerals and
certified finite observations first interpret its
relational form $\Rt$; definable graphs yield
$\R$.
We do so because interpretation of $\Rt$ is much
simpler than direct interpretation of $\R$ and
already exposes all of the main ideas.
Direct translation is available in supplementary
formalized materials %formalized{rocq-ai:Interpretation_of_R/functional/DirectRTheorem7.v\#L75}.

## paper-markdown.tex:2148-2149 · D38-L2150 · Suggested by DeepL Write

- [x] The following proof was obtained in `{++a ++}`discussion
with GPT-6 Astra.

## paper-markdown.tex:2179-2183 · D39-L2181 · Suggested by DeepL Write

- [x] Let us start constructing the model inside
%PTSrk{} and proving that `{++the ++}`axioms hold in our
model.
First, some preliminaries on `{++the ++}`interpretation of
first-order logic formulas: put

## paper-markdown.tex:2234-2236 · L2239-S1-P1 · Suggested by Grazie

- [x] Abstraction gives a map from $P$ to $L_k(P)$;
application on `{++the ++}`term $(λ \,T\,x.x)$ gives a map in
the opposite direction.

## paper-markdown.tex:2318-2320 · D41-L2320 · Suggested by DeepL Write

- [x] Meaning that, for “good” values in `{++the ++}`new domain $X$,
a negation of $P$ is upwards closed.
Define

## paper-markdown.tex:2367-2368 · D41-L2369 · Suggested by DeepL Write

- [x] In this `{~~section~>section,~~}` we prove that $\widetilde R3$ also
holds in our interpretation of $\Rt$.

## paper-markdown.tex:2394-2395 · D42-L2396 · Suggested by Grazie & DeepL Write

- [x] `{~~Thus~>Thus,~~}` $s(e_i) =_β e_{\min(i + 1, c)}$.
Define the domain predicate as

## paper-markdown.tex:2521-2529 · D44-L2523 · Suggested by DeepL Write

- [x] For bounded order ($\widetilde R4$),
apply Lemma <#case>.
Under $O(d, \overline{n})$, a case with
$O(\overline{n + 1}, d)$ contradicts
$\nc O(\overline{n + 1}, \overline{n})$ by
transitivity.
Conversely, `{~~an~>a~~}` $E(d, \overline{i})$ branch with
$i ≤ n$ gives $O(d, \overline{n})$ using $E ⇒ O$
and`{-- the--}` ground comparison.

## paper-markdown.tex:2588-2595 · IDE-grammar-L2590 · Suggested by Grazie

- [x] The ground graph schemes hold for every third
argument, and distinct numerals are unequal.
For every standard $n$, the downset of $n$ is
exactly $\{0, …, n\}$, proving both directions of
(<#rtilde:bound>).
Every standard number is comparable with $n$,
and $n ≤^+ ω$, proving (<#rtilde:compare>).
`{~~Hence~>Hence,~~}` this is a model of $\Rt$.

## paper-markdown.tex:2634-2646 · IDE-grammar-L2636 · Suggested by Grazie

- [x] In $\R$, interpret $A(x, y, z)$ by $x + y = z$ and
$M(x, y, z)$ by $xy = z$.
The ground arithmetic equations give the two graph
schemes.
For $i < j$, an assumption $\bar j ≤ \bar i$
contradicts (<#r:bound>) and numeral separation;
(<#r:compare>) therefore yields $\bar i ≤ \bar j$.
The case $i = j$ follows from (<#r:compare>)
directly.
`{~~Thus~>Thus,~~}` $\R$ proves all true ground comparisons,
and equality substitution supplies the reverse
implication in (<#rtilde:bound>).
The remaining relational schemes are immediate.

## paper-markdown.tex:2654-2665 · IDE-grammar-L2656 · Suggested by Grazie

- [x] For fixed $x, y$, either a unique $A$-output
exists or it does not.
In the first case $F_A$ selects that output;
in the second it selects zero.
`{~~Hence~>Hence,~~}` $F_A$ is provably total and single-valued.
At standard inputs, (<#rtilde:add>) forces its
value to be $\overline{m + n}$.
Define $F_M$ identically with $M$ in place of $A$;
its standard value is $\overline{mn}$.
These graphs interpret $+, ⋅$;
keep $0, S, =, ≤$ unchanged.
All five schemes of $\R$ follow.

## paper-markdown.tex:2702-2729 · L2707-S3-P1 · Suggested by Grazie

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
Hypothesis in order to strictify the hierarchy of
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
`{~~therefore~>therefore,~~}` interpretation of $R$ is the natural
first step.
