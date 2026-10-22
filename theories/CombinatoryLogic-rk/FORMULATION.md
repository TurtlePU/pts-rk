# An indexed combinatory formulation of PTS-rk

This is the initial, more detailed research proposal. The current concise
presentation is [CombinatoryPTS-rk.tex](CombinatoryPTS-rk.tex), with its
[compiled PDF](CombinatoryPTS-rk.pdf). Subsequent proofs in
[ProductCatalogue.v](ProductCatalogue.v) check all eleven product schemes and
compile P4/P5 into the four-core grammar; [Hilbert.v](Hilbert.v) checks
independent Hilbert derivations and typed applicative recovery. The
[README](README.md) and [evidence](EVIDENCE.md) record current scope and checks.
The later I/K/S catalogues and [CatalogueEconomy.v](CatalogueEconomy.v) now
provide an explicit sound 65-shape Hilbert system, equivalent to the checked
66-shape closure catalogue. The current note gives the external mathematical
completeness argument and ranked IIR/setoid and Cubical QIIRT specifications.
The source-completeness ROCQ theorem and the stronger independent algebraic
equality comparison remain open. Contextual H+, its substitution theorem,
exact I/K/S/P abstraction assemblies, syntactic product exposure and shared
local S shortening are now checked. Arbitrary-chain shortness with sharing
is the first missing formal lemma; the note's specifications add no Rocq axioms.
The remaining-work descriptions below describe the original proposal, not a
claim that these later product and Hilbert results are still absent.

## Result and status

A finite basis of fixed, closed, originally typed PTS-rk terms is impossible,
even if every universe symbol remains available separately. This is proved
in [FiniteBasis.v](FiniteBasis.v), for representation up to the original beta
conversion, not merely literal recovery.

The economical starting point is four numerical families **I, K, S, P**,
with ordinary explicit type arguments. [Core.v](Core.v) proves their original
typings, exact type ranks, and beta computation for **all** numerical indices.
[Presentation.v](Presentation.v) gives binder-free applicative subjects and
an independent typing relation, and proves its soundness in original PTS-rk.
Types in this first presentation still use original annotated PTS syntax.

There is an externally established, complete finite-scheme Hilbert
presentation, described below. Completeness of just the four core families,
or of the alternative four telescope families proposed below, is **not yet
proved**. The remaining issue is constructing the dependent type families
needed during abstraction, together with an adequate equality presentation.
The verified core is a sound fragment, not a claimed completed equivalence.

## 1. Why numerical indexing is necessary

Recall the actual rules:

\[
 U_i:U_0,\qquad
 \frac{\Gamma\vdash A:U_a\quad\Gamma,x:A\vdash B:U_b}
      {\Gamma\vdash\Pi x:A.B:U_{\max(a+1,b)}}.
\]

Write \(\rho(t)=r\) when \(t:T\) and \(T:U_r\). This is the rank of
the **type**, not the index of a universe occurring in the term. In a
well-formed context it is unique and invariant under beta conversion.
Original typing also gives

\[
 \rho(fu)\leq\rho(f).
\]

Suppose the available non-universe atoms expand to a finite list of closed
typed terms \(b_1,\ldots,b_m\). Let
\(R=\max(0,\rho(b_1),\ldots,\rho(b_m))\).
Every universe atom has rank zero, since \(U_i:U_0:U_0\).
Induction on an application tree therefore bounds its rank by \(R\),
whenever the entire expanded tree is originally typable. Allowing arbitrary
partial applications or beta-convertible output does not evade this bound.

But define

\[
 A_0=U_0,\quad A_{r+1}=\Pi x:A_r.U_0,\qquad
 v_0=U_0,\quad v_{r+1}=\lambda x:A_r.U_0.
\]

Then \(A_r:U_r\) and \(v_r:A_r\). In particular \(v_{R+1}\) cannot
be represented by the proposed basis. The exact Rocq endpoint is
`FiniteBasis.no_finite_typed_basis` (the module is the file's library module).

This rules out a fixed typed SK basis, a fixed typed single combinator, and
any other finite fixed typed applicative basis. It does not rule out indexed
families, an untyped encoding with an external type discipline, or a decoder
interface that changes the representation theorem. An infinite family whose
type ranks stay uniformly bounded has the same obstruction, by the same
argument; that generalization is an observation, not a separate Rocq theorem
in this directory.

## 2. Four core families, with annotations intact

In the following displays, arrows abbreviate nondependent products. All
parameters displayed after a combinator are ordinary arguments; only
\(a,b,c\in\mathbb N\) belong to its external index.

\[
\begin{aligned}
 I_a &:= \lambda A:U_a.\lambda x:A.x,\\
 K_{a,b} &:= \lambda A:U_a.\lambda B:U_b.
                  \lambda x:A.\lambda y:B.x,\\
 P_{a,b} &:= \lambda A:U_a.\lambda B:(\Pi x:A.U_b).
                  \Pi x:A.Bx.
\end{aligned}
\]

Their types are

\[
\begin{aligned}
 I_a &: \Pi A:U_a.\,A\to A,\\
 K_{a,b} &: \Pi A:U_a.\Pi B:U_b.\,A\to B\to A,\\
 P_{a,b} &: \Pi A:U_a.\Pi B:(\Pi x:A.U_b).
                  U_{\max(a+1,b)}.
\end{aligned}
\]

Dependent substitution needs both a domain family and a result family:

\[
\begin{aligned}
S_{a,b,c}:={}&\lambda A:U_a.
 \lambda B:(\Pi x:A.U_b).
 \lambda C:(\Pi x:A.\Pi y:Bx.U_c).\\
 &\lambda f:(\Pi x:A.\Pi y:Bx.Cxy).
  \lambda g:(\Pi x:A.Bx).
  \lambda x:A.fx(gx).
\end{aligned}
\]

Its type has the same first five product binders, followed by
\(\Pi x:A.Cx(gx)\). Thus the result type depends on the supplied \(g\),
as required by dependent application.

The full beta laws are

\[
\begin{aligned}
 I_a\,A\,x&\longrightarrow_\beta^* x,\\
 K_{a,b}\,A\,B\,x\,y&\longrightarrow_\beta^* x,\\
 S_{a,b,c}\,A\,B\,C\,f\,g\,x
   &\longrightarrow_\beta^* fx(gx),\\
 P_{a,b}\,A\,B&\longrightarrow_\beta^*\Pi x:A.Bx.
\end{aligned}
\]

Every lambda annotation in these definitions is retained. In particular,
\(I_0\,U_i\) reduces to the distinct annotated term
\(\lambda x:U_i.x\); none of the universe information is erased.

The exact ranks of the combinators' **types** are:

| Family | Type rank |
| --- | --- |
| \(I_a\) | \(a+1\) |
| \(K_{a,b}\) | \(\max(a+1,b+1)\) |
| \(S_{a,b,c}\) | \(\max(a+2,b+2,c+1)\) |
| \(P_{a,b}\) | \(a+2\) |

The last row is independent of \(b\): the result is a universe symbol,
whose own type is always \(U_0\). These are exact sorts, not cumulative
upper bounds. The proofs are symbolic in all indices.

Core also provides optional dependent constant formation
\(K^d_{a,b}=\lambda A:U_a.\lambda B:(\Pi x:A.U_b).
\lambda x:A.\lambda y:Bx.x\), with type rank \(\max(a+2,b+1)\).
It is not an additional primitive of the four-family presentation.

## 3. A checked combinatory core

The subject grammar implemented in Presentation is

\[
 p ::= U_i\mid I_a\mid K_{a,b}\mid S_{a,b,c}\mid P_{a,b}\mid p\,p.
\]

Let \(E\) expand the atoms to the annotated terms above and commute with
application. There are no variables or binders in this grammar, and none of
the atom indices contains a source term or typing derivation.

The judgment \(\vdash_C p:A\) has the five families of atom rules above,
application

\[
 \frac{\vdash_C p:\Pi x:A.B\quad\vdash_C q:A}
      {\vdash_C pq:B[E(q)/x]},
\]

and conversion

\[
 \frac{\vdash_C p:A\quad\vdash_C q:U_r\quad A=_\beta E(q)}
      {\vdash_C p:E(q)}.
\]

The conversion premise uses another derivation of the combinatory relation;
it does not assume original typing of the desired conclusion. Rocq proves

\[
 \vdash_C p:A\quad\Longrightarrow\quad\vdash_{\rm rk}E(p):A.
\]

This is an independently inductive **mixed** presentation: subjects are
combinatory, while the type expression \(A\), substitution into it, and
conversion use the original annotated type language. It is not yet a
completely binder-free language of both terms and types.

Define code equality by \(p\simeq q\) iff \(E(p)=_\beta E(q)\).
This specifies exactly which original equality is intended, without eta.
The usual saturated I/K/S contractions and application congruence are proved
sound for it. The product law expands to an original product; it is not
misrepresented as a rewrite to a binder-free subject constructor.

Weak saturated rewriting alone should not be identified with this equality.
For example, reductions underneath a represented lambda may occur before
its last argument is supplied. Compiling
\(\lambda x:A.(\lambda y:A.y)x\) and \(\lambda x:A.x\) can leave
different unsaturated weak normal forms. An independent strong combinatory
equational presentation requires additional beta-valid laws, not functional
extensionality or eta conversion.

## 4. A complete Hilbert formulation, and the remaining economy question

PTS-rk is supersorted: every sort has a sort, and every pair of sorts admits
a product. Bunder--Dekkers, [Definition 7.3 and Theorem 9.4](https://lmcs.episciences.org/839/pdf),
therefore provide a theorem-equivalent Hilbert presentation. Its finite
catalogue has 11 product, 7 identity, 17 constant and 30 substitution scheme
shapes. It includes type-formation and product-exposure auxiliaries, and
retains annotated beta reduction. Their later erased SKI presentation allows
eta reduction and is not used here. This completeness result is external;
it is not formalized or assumed as a Rocq axiom.

One exact specification is to specialize that finite catalogue to
\(U_i:U_0\) and \(r(a,b)=\max(a+1,b)\). A catalogue atom is indexed by
its finite shape tag and numerical sort parameters. Its declared expansion
is the corresponding original annotated term. All guards concern these
fixed schemes, not the theorem being represented. Application, conversion,
subject reduction and type reduction give the Hilbert rules. This already
answers the existence question with a finite number of indexed schemes.

An HPTS derivation additionally gives an applicative representation of its
subject: axioms supply atoms, application combines representations, and
subject reduction keeps the previous representation, whose expansion reduces
to the new subject. Conversion and type reduction keep that code and update
its original typing. This observation does not eliminate the original type
syntax, prove completeness of the implemented HasType relation, or supply a
standalone weak rewrite calculus.

The four core schemas alone should not be declared complete on the strength
of their familiar equations. When abstracting an application, S requires
representations of its dependent domain and codomain families. Those are not
necessarily smaller subterms of the input. A recursive call on each such
family needs a well-foundedness proof. Likewise, putting a whole source type
or derivation into a combinator index would conceal the problem and would
not be the intended economy.

## 5. A four-family telescope candidate

There is a promising way to package the required closure operations more
uniformly. This section is a mathematical design, not an implemented
completeness theorem.

For a finite numerical rank vector \(\mathbf r=(r_1,\ldots,r_n)\), take
ordinary family arguments

\[
 T_i:\Pi x_1:T_1.\cdots\Pi x_{i-1}:T_{i-1}(x_{<i-1}).U_{r_i}.
\]

For \(i=1\), the empty product means \(T_1:U_{r_1}\). Write
\(\Delta_T=(x_i:T_i(x_{<i}))_{i=1}^n\). The following macros bind all
these family parameters first, with precisely the displayed types.

\[
\begin{aligned}
 Z_{\mathbf r,j}&:=\lambda\mathbf T.\lambda\Delta_T.U_j,\\
 V_{\mathbf r,i}&:=\lambda\mathbf T.\lambda\Delta_T.x_i,\\
 \mathsf{Ap}_{\mathbf r,a,b}&:=\lambda\mathbf T.\lambda D\,F\,f\,u.
          \lambda\Delta_T.f(\mathbf x)(u(\mathbf x)),\\
 \mathsf{Pr}_{\mathbf r,a,b}&:=\lambda\mathbf T.\lambda D\,F.
          \lambda\Delta_T.\Pi y:D(\mathbf x).F(\mathbf x,y).
\end{aligned}
\]

Here the ordinary parameters suppressed in the last two lines have types

\[
\begin{aligned}
 D&:\Pi\Delta_T.U_a,&
 F&:\Pi\Delta_T.\Pi y:D(\mathbf x).U_b,\\
 f&:\Pi\Delta_T.\Pi y:D(\mathbf x).F(\mathbf x,y),&
 u&:\Pi\Delta_T.D(\mathbf x).
\end{aligned}
\]

Only Ap takes \(f,u\). All four schemas are closed original annotated
terms. Their formation follows by repeated original rules; the reusable
rank calculation is

\[
 h(\mathbf r,b)=\max(b,r_1+1,\ldots,r_n+1).
\]

A closure type \(\Pi\Delta_T.B\), for \(B:U_b\), has rank
\(h(\mathbf r,b)\). The parameter type of \(T_i\) has rank
\(h((r_1,\ldots,r_{i-1}),0)\). This keeps the schema generation entirely
numerical, while actual domain syntax travels in ordinary arguments.

The intended translation represents an open term by its annotated closure:

\[
 E(C_\Gamma(t))=_\beta\lambda\Gamma.t.
\]

Z handles universes, V handles variables, Ap handles application and Pr
handles products. A lambda needs no fifth operation:

\[
 C_\Gamma(\lambda x:A.t)=C_{\Gamma,x:A}(t).
\]

The right-hand closure already has exactly the required binder. For example,
\(V_{(a),1}\) is literally \(I_a\). The telescope parameters must still
be supplied as combinatory expressions; they are not opaque source fragments.

The same domain/codomain recursion gap prevents declaring these clauses a
total compiler today. A concrete route around it is to compile the finitely
many Hilbert catalogue shapes and their required types into these four
families, uniformly in the numerical indices, and then translate Hilbert
derivations. Such a finite symbolic compilation would be substantive evidence;
merely numbering the catalogue or writing the above clauses is not its proof.

## 6. Next proof obligation

Fix the auxiliary catalogue and construct its first product-exposure and
dependent-substitution type-family codes in the proposed telescope grammar.
Prove their original typings and annotated beta recovery for all rank
parameters. Then either finish the finite catalogue compilation and apply
the external Hilbert completeness argument, or formalize that argument.

Separately decide whether the final presentation keeps expansion-defined
beta equality or replaces it with a proved complete strong combinatory
equality. No eta law or annotation erasure is needed for the current results.
