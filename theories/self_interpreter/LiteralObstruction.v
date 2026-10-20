From Stdlib Require Import Arith.PeanoNat Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Ranks DefEq
  Reduction AbstractRewriting.
From PTSrk.NormalizationComplexity Require Import Rank Literals Greedy RedexRanks.
From PTSrk.SelfInterpreter Require Import ChurchSyntax.
Import Context RankEstimate.

Module LiteralObstruction.
Module CS := ChurchSyntax.ChurchSyntax.

(** This obstruction is specific to the current raw HOAS code: a source
    sort label is Church numeral DATA, not an original target sort literal.
    It is independent of evaluator typing and already applies to normal
    sources of the single original type U_0.  It does not exclude indexed
    evaluators carrying the source literal information in their syntax. *)

Lemma nat_fold_literals n (z s : Term nat n) k ceiling :
  maxRankLiteral z <= ceiling -> maxRankLiteral s <= ceiling ->
  maxRankLiteral (CS.nat_fold z s k) <= ceiling.
Proof.
  intros Hz Hs; induction k; cbn [CS.nat_fold maxRankLiteral];
    [exact Hz | apply Nat.max_lub; assumption].
Qed.

Lemma ast_fold_literals m (t : Term nat m) :
  forall n (X z s u p l a : Term nat n) rho ceiling,
  maxRankLiteral X <= ceiling -> maxRankLiteral z <= ceiling ->
  maxRankLiteral s <= ceiling -> maxRankLiteral u <= ceiling ->
  maxRankLiteral p <= ceiling -> maxRankLiteral l <= ceiling ->
  maxRankLiteral a <= ceiling ->
  (forall i, maxRankLiteral (rho i) <= ceiling) ->
  maxRankLiteral (CS.ast_fold X z s u p l a rho t) <= ceiling.
Proof.
  induction t; intros q X z s u p h a rho ceiling HX Hz Hs Hu Hp Hh Ha Hr;
    cbn [CS.ast_fold maxRankLiteral].
  - apply Nat.max_lub; [exact Hu | apply nat_fold_literals; assumption].
  - repeat apply Nat.max_lub; try assumption.
    + apply IHt1; assumption.
    + apply IHt2; try (unfold shift; rewrite literal_rename; assumption).
      intro i; dependent elimination i; cbn [transpose fin_match maxRankLiteral]; [lia |].
      unfold shift; rewrite literal_rename; apply Hr.
  - apply Hr.
  - repeat apply Nat.max_lub; try assumption.
    + apply IHt1; assumption.
    + apply IHt2; try (unfold shift; rewrite literal_rename; assumption).
      intro i; dependent elimination i; cbn [transpose fin_match maxRankLiteral]; [lia |].
      unfold shift; rewrite literal_rename; apply Hr.
  - repeat apply Nat.max_lub; try assumption; [apply IHt1 | apply IHt2]; assumption.
Qed.

Lemma body_literals m (t : Term nat m) : maxRankLiteral (CS.body t) = 0.
Proof.
  assert (H : maxRankLiteral (CS.body t) <= 0).
  { unfold CS.body. apply ast_fold_literals; cbn [maxRankLiteral rename]; intros; lia. }
  lia.
Qed.

Lemma bind_vars_literals count : forall n (X : Term nat n) q ceiling,
  maxRankLiteral X <= ceiling -> maxRankLiteral q <= ceiling ->
  maxRankLiteral (CS.bind_vars count X q) <= ceiling.
Proof.
  induction count; intros n X q ceiling HX Hq; cbn [CS.bind_vars]; [exact Hq |].
  apply IHcount; [exact HX |]. cbn [maxRankLiteral].
  rewrite literal_rename. apply Nat.max_lub; assumption.
Qed.

Theorem quote_literal_exact r m (t : Term nat m) :
  maxRankLiteral (CS.quote r t) = r.
Proof.
  assert (Hbody : maxRankLiteral (CS.bind_vars m
    (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))) (CS.body t)) = 0).
  { apply Nat.le_antisymm; [|lia]. apply bind_vars_literals; [cbn; lia |].
    rewrite body_literals; lia. }
  unfold CS.quote. cbn [maxRankLiteral CS.unary CS.binary CS.binding CS.arrow].
  rewrite Hbody, Nat.max_0_r. reflexivity.
Qed.

Lemma conversion_to_sort_reduces n (t : Term nat n) k :
  def_equiv nat n t (𝓤 k) -> reduces_to nat n t (𝓤 k).
Proof.
  intro HE. apply def_equiv_prop in HE. destruct HE as [u [Ht Hu]].
  inversion Hu; subst; [exact Ht |]. inversion H.
Qed.

(** The head may include any FIXED original type argument and any other
    fixed parameters.  Conversion does not evade the literal bound because
    U_k is normal and hence a common reduct must be U_k itself. *)
Theorem encoded_sort_conversion_bound (head : Term nat 0) r k :
  def_equiv nat 0 (app head (@CS.quote r 0 (𝓤 k))) (𝓤 k) ->
  k <= Nat.max (maxRankLiteral head) r.
Proof.
  intro HE. apply conversion_to_sort_reduces in HE.
  pose proof (reachable_sort_literal _ k HE) as HL.
  cbn [maxRankLiteral] in HL. rewrite quote_literal_exact in HL. exact HL.
Qed.

Lemma sort_typed k : @typ nat RankSorts 0 ε (𝓤 k) (𝓤 0).
Proof. constructor; reflexivity. Qed.

Lemma sort_redex_bound_zero k : RedexBound ε (𝓤 k) 0.
Proof. intros r HR; inversion HR. Qed.

Lemma sort_type_rank_zero k : TypeRank ε (𝓤 k) 0.
Proof. exists (𝓤 0); split; apply sort_typed. Qed.

(** The counterexamples are closed, originally typed, beta-normal, have
    semantic redex bound zero and TYPE rank zero.  Thus a budget consisting
    only of redex rank and output type rank cannot repair this particular
    fixed-index, numeral-label input interface. *)
Theorem normal_sort_counterexample (head : Term nat 0) r :
  exists k,
    @typ nat RankSorts 0 ε (𝓤 k) (𝓤 0) /\
    TypeRank ε (𝓤 k) 0 /\ normalb (@𝓤 nat 0 k) = true /\
    RedexBound ε (𝓤 k) 0 /\
    @typ nat RankSorts 0 ε (@CS.quote r 0 (𝓤 k)) (CS.code_type r 0) /\
    ~ def_equiv nat 0 (app head (@CS.quote r 0 (𝓤 k))) (𝓤 k).
Proof.
  exists (S (Nat.max (maxRankLiteral head) r)). repeat split.
  - apply sort_typed.
  - apply sort_type_rank_zero.
  - apply sort_redex_bound_zero.
  - apply CS.quote_typing.
  - intro HE. apply encoded_sort_conversion_bound in HE. lia.
Qed.

Definition UniformSortUnquoter r (head : Term nat 0) : Prop :=
  @typ nat RankSorts 0 ε head (CS.arrow (CS.code_type r 0) (𝓤 0)) /\
  forall k, def_equiv nat 0 (app head (@CS.quote r 0 (𝓤 k))) (𝓤 k).

Theorem no_uniform_sort_unquoter r head : ~ UniformSortUnquoter r head.
Proof.
  intros [Htype Hall].
  specialize (Hall (S (Nat.max (maxRankLiteral head) r))).
  apply encoded_sort_conversion_bound in Hall. lia.
Qed.

(** In particular this excludes a fixed term E given the unchanged source
    type U_0 and a fixed-rank raw HOAS code.  A source-dependent literal bank
    or an external index containing a literal ceiling is outside this
    statement.  The existing conservativeRank already includes that ceiling.
    No sufficiency of such a repair is asserted by this negative theorem. *)
Corollary no_fixed_type_argument_unquoter (E : Term nat 0) r :
  exists k, @typ nat RankSorts 0 ε (𝓤 k) (𝓤 0) /\
    RedexBound ε (𝓤 k) 0 /\
    ~ def_equiv nat 0 (app (app E (𝓤 0)) (@CS.quote r 0 (𝓤 k))) (𝓤 k).
Proof.
  exists (S (Nat.max (maxRankLiteral (app E (𝓤 0))) r)).
  split; [apply sort_typed |]. split; [apply sort_redex_bound_zero |].
  intro HE. apply encoded_sort_conversion_bound in HE. lia.
Qed.

Print Assumptions quote_literal_exact.
Print Assumptions encoded_sort_conversion_bound.
Print Assumptions normal_sort_counterexample.
Print Assumptions no_uniform_sort_unquoter.
Print Assumptions no_fixed_type_argument_unquoter.

End LiteralObstruction.
