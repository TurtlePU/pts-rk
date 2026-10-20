From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia.
From PTSrk Require Import Syntax Context Typing Preservation Ranks DefEq Reduction
  AbstractRewriting.
From PTSrk.NormalizationComplexity Require Import Rank Greedy Bounds Runtime
  RedexRanks Descent BoundedNormalization Literals AutomaticBound Normalization.
From PTSrk.SelfInterpreter Require Import ChurchSyntax ChurchSyntaxFaithful.
Import Context RankEstimate.

Module RankedNormalization.
Module CS := ChurchSyntax.ChurchSyntax.

(** An executable METALEVEL syntax transformer for the full original PTS.
    Neither this function nor its rank argument is an internal PTS evaluator.
    It quotes the normal form, not the unreduced source. *)
Definition normalized_quote r d {n} (t : Term nat n) : Term nat 0 :=
  CS.quote r (rounds d t).

Definition automatic_quote r (t : Term nat 0) : Term nat 0 :=
  normalized_quote r (conservativeRank t) t.

(** These quantities charge ONLY the existing normalization stage, including
    its normal-form test, and (in the automatic case) rank discovery.
    They do not charge construction or serialization of the HOAS output. *)
Definition normalization_charge d {n} (t : Term nat n) :=
  snd (normalizeCosted d t).
Definition automatic_normalization_charge (t : Term nat 0) :=
  snd (automaticNormalizer t).

Theorem normalized_source_correct n d (G : Ctx nat n) (t T : Term nat n) :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T -> RedexBound G t d ->
  normalb (rounds d t) = true /\ reduces_to nat n t (rounds d t) /\
  @typ nat RankSorts n G (rounds d t) T /\
  fst (normalizeCosted d t) = Some (rounds d t) /\
  normalization_charge d t <= tower (2*d+1) (nodes t+5*d+2).
Proof.
  intros HG Ht HB. split; [eapply bounded_rounds_normal; eassumption |].
  split; [apply rounds_sound |].
  split; [eapply subject_reduction'; [exact Ht | exact HG | apply rounds_sound] |].
  split; [eapply bounded_normalizer_succeeds; eassumption |].
  unfold normalization_charge; rewrite Nat.add_1_r; apply normalizeCosted_elementary.
Qed.

Theorem normalized_quote_typed_normal r d n (t : Term nat n) :
  normalb (normalized_quote r d t) = true /\
  @typ nat RankSorts 0 ε (normalized_quote r d t) (CS.code_type r n) /\
  @typ nat RankSorts 0 ε (CS.code_type r n) (𝓤 (r+3)).
Proof.
  unfold normalized_quote; repeat split;
    [apply CS.quote_normal | apply CS.quote_typing |].
  replace (r+3) with (S (S (S r))) by lia; apply CS.code_type_sort.
Qed.

Lemma reduction_conversion n (t u : Term nat n) :
  reduces_to nat n t u -> def_equiv nat n t u.
Proof. intro H; apply def_equiv_prop; exists u; split; [exact H | reflexivity]. Qed.

Theorem bounded_normal_forms_equal_iff n d e (G : Ctx nat n) (t u T U : Term nat n) :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T -> @typ nat RankSorts n G u U ->
  RedexBound G t d -> RedexBound G u e ->
  (rounds d t = rounds e u <-> def_equiv nat n t u).
Proof.
  intros HG Ht Hu HBt HBu. split.
  - intro H. apply def_equiv_prop; exists (rounds d t); split;
      [apply rounds_sound | rewrite H; apply rounds_sound].
  - intro H. apply normal_conversion_identity.
    + eapply bounded_rounds_normal; eassumption.
    + eapply bounded_rounds_normal; eassumption.
    + transitivity t; [symmetry; apply reduction_conversion, rounds_sound |].
      transitivity u; [exact H | apply reduction_conversion, rounds_sound].
Qed.

(** Canonical codes identify EXACTLY original beta conversion, including
    reductions inside annotations. Budgets and source types may differ. *)
Theorem normalized_quote_conversion_iff r s n d e (G : Ctx nat n) (t u T U : Term nat n) :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T -> @typ nat RankSorts n G u U ->
  RedexBound G t d -> RedexBound G u e ->
  (def_equiv nat 0 (normalized_quote r d t) (normalized_quote s e u) <->
    r = s /\ def_equiv nat n t u).
Proof.
  intros HG Ht Hu HBt HBu. unfold normalized_quote.
  rewrite quote_conversion_iff.
  rewrite (bounded_normal_forms_equal_iff n d e G t u T U HG Ht Hu HBt HBu).
  reflexivity.
Qed.

Theorem normalized_quote_equal_iff r n d e (G : Ctx nat n) (t u T U : Term nat n) :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T -> @typ nat RankSorts n G u U ->
  RedexBound G t d -> RedexBound G u e ->
  (normalized_quote r d t = normalized_quote r e u <-> def_equiv nat n t u).
Proof.
  intros HG Ht Hu HBt HBu. split.
  - intro H. apply (proj1 (bounded_normal_forms_equal_iff n d e G t u T U HG Ht Hu HBt HBu)).
    apply (quote_injective r n); exact H.
  - intro H. unfold normalized_quote. f_equal.
    apply (proj2 (bounded_normal_forms_equal_iff n d e G t u T U HG Ht Hu HBt HBu)); exact H.
Qed.

(** Exact constructor count of the raw HOAS representation. Source sort
    labels are represented by unary numeral data; original annotations are
    counted recursively. This is an output-size measure, NOT a runtime. *)
Fixpoint hoas_mass {n} (t : Term nat n) : nat :=
  match t with
  | 𝓤 k => 2*k+3
  | var _ => 1
  | Π A B | lam A B => 5 + hoas_mass A + hoas_mass B
  | app f u => 3 + hoas_mass f + hoas_mass u
  end.

Lemma nat_fold_nodes n (z s : Fin n) k :
  nodes (CS.nat_fold (var z) (var s) k) = 2*k+1.
Proof. induction k; cbn [CS.nat_fold nodes]; lia. Qed.

Lemma ast_fold_nodes m (t : Term nat m) :
  forall n (x z s u p l a : Fin n) (rho : Fin m -> Fin n),
  nodes (CS.ast_fold (var x) (var z) (var s) (var u) (var p)
    (var l) (var a) (fun i => var (rho i)) t) = hoas_mass t.
Proof.
  induction t; intros k x z s u p h a rho; cbn [CS.ast_fold nodes hoas_mass].
  - rewrite nat_fold_nodes; lia.
  - rewrite IHt1, CS.ast_fold_variables_transpose.
    cbn [shift rename]. rewrite IHt2; lia.
  - reflexivity.
  - rewrite IHt1, CS.ast_fold_variables_transpose.
    cbn [shift rename]. rewrite IHt2; lia.
  - rewrite IHt1, IHt2; lia.
Qed.

Lemma body_nodes m (t : Term nat m) : nodes (CS.body t) = hoas_mass t.
Proof. unfold CS.body; cbn [rename]; apply ast_fold_nodes. Qed.

Lemma bind_vars_nodes count : forall n (x : Fin n) q,
  nodes (CS.bind_vars count (var x) q) = 2*count + nodes q.
Proof.
  induction count; intros n x q; cbn [CS.bind_vars]; [reflexivity |].
  rewrite IHcount; cbn [nodes rename].
  change (2*count + S (1 + nodes q) = 2*S count + nodes q); lia.
Qed.

Theorem quote_nodes r n (t : Term nat n) :
  nodes (CS.quote r t) = 34 + 2*n + hoas_mass t.
Proof.
  unfold CS.quote. cbn [nodes CS.unary CS.binary CS.binding CS.arrow shift rename].
  rewrite bind_vars_nodes, body_nodes; lia.
Qed.

Lemma hoas_mass_bound n (t : Term nat n) : forall L,
  maxRankLiteral t <= L -> hoas_mass t <= (2*L+5) * nodes t.
Proof.
  induction t; intros L H; cbn [maxRankLiteral] in H; cbn [hoas_mass nodes].
  - lia.
  - apply Nat.max_lub_iff in H as [HA HB].
    specialize (IHt1 L HA); specialize (IHt2 L HB); nia.
  - lia.
  - apply Nat.max_lub_iff in H as [HA HB].
    specialize (IHt1 L HA); specialize (IHt2 L HB); nia.
  - apply Nat.max_lub_iff in H as [HA HB].
    specialize (IHt1 L HA); specialize (IHt2 L HB); nia.
Qed.

Theorem normalized_quote_size r d n (t : Term nat n) :
  nodes (normalized_quote r d t) <=
    34 + 2*n + (2*maxRankLiteral t+5) * tower d (nodes t).
Proof.
  unfold normalized_quote; rewrite quote_nodes.
  pose proof (literal_reduction t (rounds d t) (rounds_sound d t)) as HL.
  pose proof (hoas_mass_bound n (rounds d t) (maxRankLiteral t) HL) as HM.
  pose proof (rounds_size d t) as HN. nia.
Qed.

(** Automatic coverage has no supplied bound, termination or success premise.
    It remains a metalevel transformation of closed original-typed terms. *)
Theorem automatic_quote_correct r (t T : Term nat 0) :
  @typ nat RankSorts 0 ε t T ->
  let nf := rounds (conservativeRank t) t in
  normalb nf = true /\ reduces_to nat 0 t nf /\
  @typ nat RankSorts 0 ε nf T /\
  fst (automaticNormalizer t) = Some nf /\
  normalb (automatic_quote r t) = true /\
  @typ nat RankSorts 0 ε (automatic_quote r t) (CS.code_type r 0) /\
  @typ nat RankSorts 0 ε (CS.code_type r 0) (𝓤 (r+3)) /\
  automatic_normalization_charge t <=
    tower (4*encodingSize t+3) (18*encodingSize t+8).
Proof.
  intro Ht; cbn zeta.
  destruct (normalized_source_correct 0 (conservativeRank t) ε t T
    (@wf_empty nat RankSorts) Ht (conservative_rank_sound t T Ht))
    as [HN [HR [HT [HS HC]]]].
  destruct (normalized_quote_typed_normal r (conservativeRank t) 0 t)
    as [HQN [HQT HCS]].
  split; [exact HN |]. split; [exact HR |]. split; [exact HT |].
  split; [rewrite automaticNormalizer_projection; exact HS |].
  split; [exact HQN |]. split; [exact HQT |]. split; [exact HCS |].
  apply automaticNormalizer_cost.
Qed.

Theorem automatic_quote_equal_iff r (t u T U : Term nat 0) :
  @typ nat RankSorts 0 ε t T -> @typ nat RankSorts 0 ε u U ->
  (automatic_quote r t = automatic_quote r u <-> def_equiv nat 0 t u).
Proof.
  intros Ht Hu. unfold automatic_quote. eapply normalized_quote_equal_iff;
    [apply wf_empty | exact Ht | exact Hu | apply (conservative_rank_sound t T Ht) |
      apply (conservative_rank_sound u U Hu)].
Qed.

Theorem automatic_quote_conversion_iff r s (t u T U : Term nat 0) :
  @typ nat RankSorts 0 ε t T -> @typ nat RankSorts 0 ε u U ->
  (def_equiv nat 0 (automatic_quote r t) (automatic_quote s u) <->
    r = s /\ def_equiv nat 0 t u).
Proof.
  intros Ht Hu. unfold automatic_quote. eapply normalized_quote_conversion_iff;
    [apply wf_empty | exact Ht | exact Hu | apply (conservative_rank_sound t T Ht) |
      apply (conservative_rank_sound u U Hu)].
Qed.

Theorem automatic_quote_size r (t : Term nat 0) :
  nodes (automatic_quote r t) <=
    34 + (2*maxRankLiteral t+5) * tower (2*encodingSize t+1) (encodingSize t).
Proof.
  unfold automatic_quote.
  pose proof (normalized_quote_size r (conservativeRank t) 0 t) as H.
  pose proof (conservative_rank_magnitude t) as Hr.
  pose proof (nodes_encoding t) as HN.
  assert (HT : tower (conservativeRank t) (nodes t) <=
      tower (2*encodingSize t+1) (encodingSize t)).
  { eapply Nat.le_trans; [apply tower_monotone; exact HN |
      apply tower_height_monotone; exact Hr]. }
  nia.
Qed.

Print Assumptions normalized_source_correct.
Print Assumptions normalized_quote_typed_normal.
Print Assumptions normalized_quote_conversion_iff.
Print Assumptions normalized_quote_equal_iff.
Print Assumptions quote_nodes.
Print Assumptions normalized_quote_size.
Print Assumptions automatic_quote_correct.
Print Assumptions automatic_quote_equal_iff.
Print Assumptions automatic_quote_conversion_iff.
Print Assumptions automatic_quote_size.

End RankedNormalization.
