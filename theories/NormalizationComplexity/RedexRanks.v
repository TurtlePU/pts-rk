From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Inversions
  Preservation Ranks DefEq Reduction.
Import Context.
Require Import PTSrk.NormalizationComplexity.Rank
  PTSrk.NormalizationComplexity.Greedy.

(** Semantic redex ranks from the ORIGINAL typing relation. A redex head's
    rank is the sort of its product TYPE, not just its domain annotation.
    Occurrences inside binder annotations and bodies are both included. *)
Inductive RedexRank : forall {n}, Ctx nat n -> Term nat n -> nat -> Prop :=
| rr_beta {n} (G : Ctx nat n) A b u U V r :
    @typ nat RankSorts n G (lam A b) (Π U V) ->
    @typ nat RankSorts n G (Π U V) (𝓤 r) ->
    RedexRank G (app (lam A b) u) r
| rr_pi_left {n} (G : Ctx nat n) A B r :
    RedexRank G A r -> RedexRank G (Π A B) r
| rr_pi_right {n} (G : Ctx nat n) A B r :
    RedexRank (G & A) B r -> RedexRank G (Π A B) r
| rr_lam_left {n} (G : Ctx nat n) A b r :
    RedexRank G A r -> RedexRank G (lam A b) r
| rr_lam_right {n} (G : Ctx nat n) A b r :
    RedexRank (G & A) b r -> RedexRank G (lam A b) r
| rr_app_left {n} (G : Ctx nat n) f u r :
    RedexRank G f r -> RedexRank G (app f u) r
| rr_app_right {n} (G : Ctx nat n) f u r :
    RedexRank G u r -> RedexRank G (app f u) r.
Definition RedexBound {n} (G : Ctx nat n) (t : Term nat n) d :=
  forall r, RedexRank G t r -> r <= d.

(** The rank belongs to the TYPE of a term. Keeping its witness explicit
    prevents confusing the rank of a function with the rank of its domain. *)
Definition TypeRank {n} (G : Ctx nat n) (t : Term nat n) r :=
  exists T, @typ nat RankSorts n G t T /\
            @typ nat RankSorts n G T (𝓤 r).

Lemma sort_rank_unique {n} G (T : Term nat n) r s :
  @typ nat RankSorts n G T (𝓤 r) ->
  @typ nat RankSorts n G T (𝓤 s) -> r = s.
Proof.
  intros Hr Hs. apply (@equiv_𝓤_inversion nat n r s).
  eapply uniqueness_of_typing; eassumption.
Qed.

Lemma convertible_sort_rank {n} G (T U : Term nat n) r s :
  @wf nat RankSorts n G ->
  @typ nat RankSorts n G T (𝓤 r) ->
  @typ nat RankSorts n G U (𝓤 s) -> def_equiv nat n T U -> r = s.
Proof.
  intros HG HT HU Heq. apply (@equiv_𝓤_inversion nat n r s).
  eapply type_stability; eassumption.
Qed.

Theorem type_rank_unique {n} G (t : Term nat n) r s :
  @wf nat RankSorts n G -> TypeRank G t r -> TypeRank G t s -> r = s.
Proof.
  intros HG [T [Ht HT]] [U [Hu HU]].
  eapply convertible_sort_rank; try eassumption.
  eapply uniqueness_of_typing; eassumption.
Qed.

Theorem type_rank_conversion {n} G (t u : Term nat n) r s :
  @wf nat RankSorts n G -> TypeRank G t r -> TypeRank G u s ->
  def_equiv nat n t u -> r = s.
Proof.
  intros HG [T [Ht HT]] [U [Hu HU]] Heq.
  eapply convertible_sort_rank; try eassumption.
  eapply type_stability; eassumption.
Qed.

Theorem product_rank_components {n} G (A : Term nat n) B r :
  @typ nat RankSorts n G (Π A B) (𝓤 r) ->
  exists a b, @typ nat RankSorts n G A (𝓤 a) /\
              @typ nat RankSorts (S n) (G & A) B (𝓤 b) /\
              r = Nat.max (S a) b /\ a < r /\ b <= r.
Proof.
  intro H. destruct (Π_inversion RankSorts A (𝓤 r) B H)
    as [a [b [s [Hrule [HA [HB Heq]]]]]].
  apply equiv_𝓤_inversion in Heq.
  change (s = Nat.max (S a) b) in Hrule.
  exists a, b. repeat split; try assumption.
  all: pose proof (Nat.le_max_l (S a) b);
       pose proof (Nat.le_max_r (S a) b); lia.
Qed.

(** For a typed application, this rank drop is independent of which
    convertible product was chosen for the function's type. *)
Theorem application_argument_rank {n} G (f u U : Term nat n) V r :
  @wf nat RankSorts n G ->
  @typ nat RankSorts n G f (Π U V) ->
  @typ nat RankSorts n G u U -> TypeRank G f r ->
  exists a, TypeRank G u a /\ a < r.
Proof.
  intros HG Hf Hu [T [HfT HT]].
  destruct (type_is_correct _ _ Hf HG) as [s Hprod].
  assert (Hrs : r = s).
  { eapply convertible_sort_rank; try eassumption.
    eapply uniqueness_of_typing; eassumption. }
  destruct (product_rank_components G U V s Hprod)
    as [a [b [HA [HB [Heq [Hlt Hle]]]]]].
  exists a. split; [exists U; auto | lia].
Qed.

Theorem type_rank_substitution {n} G (U u : Term nat n)
  (t : Term nat (S n)) r :
  @typ nat RankSorts n G u U -> TypeRank (G & U) t r ->
  TypeRank G (subst t u) r.
Proof.
  intros Hu [T [Ht HT]]. exists (subst T u). split.
  - eapply substitution_lemma; eassumption.
  - change (@typ nat RankSorts n G (subst T u) (subst (𝓤 r) u)).
    eapply substitution_lemma; eassumption.
Qed.

Theorem type_rank_reduction {n} G (t u : Term nat n) r :
  @wf nat RankSorts n G -> TypeRank G t r ->
  reduces_to nat n t u -> TypeRank G u r.
Proof.
  intros HG [T [Ht HT]] Hred. exists T. split; [|exact HT].
  eapply subject_reduction'; eassumption.
Qed.

Corollary type_rank_greedy {n} G (t : Term nat n) r :
  @wf nat RankSorts n G -> TypeRank G t r -> TypeRank G (greedy t) r.
Proof. intros; eapply type_rank_reduction; eauto using greedy_sound. Qed.

(** Application never increases type rank along a function spine. This is
    non-strict: strictness is available for the argument, not the result. *)
Theorem application_result_rank {n} G (f u U : Term nat n) V r :
  @wf nat RankSorts n G ->
  @typ nat RankSorts n G f (Π U V) ->
  @typ nat RankSorts n G u U -> TypeRank G f r ->
  exists b, TypeRank G (app f u) b /\ b <= r.
Proof.
  intros HG Hf Hu [T [HfT HT]].
  destruct (type_is_correct _ _ Hf HG) as [s Hprod].
  assert (Hrs : r = s).
  { eapply convertible_sort_rank; try eassumption.
    eapply uniqueness_of_typing; eassumption. }
  destruct (product_rank_components G U V s Hprod)
    as [a [b [HA [HB [Heq [Hlt Hle]]]]]].
  exists b. split; [|lia]. exists (subst V u). split.
  - eapply typ_app; eassumption.
  - change (@typ nat RankSorts n G (subst V u) (subst (𝓤 b) u)).
    eapply substitution_lemma; eassumption.
Qed.

Theorem abstraction_domain_rank {n} G (A : Term nat n) b r :
  @wf nat RankSorts n G -> TypeRank G (lam A b) r ->
  exists a, @typ nat RankSorts n G A (𝓤 a) /\ a < r.
Proof.
  intros HG [T [Ht HT]].
  destruct (λ_inversion RankSorts A T b Ht) as [a [B [HA [HB Heq]]]].
  assert (HG' : @wf nat RankSorts (S n) (G & A)).
  { eapply wf_cons; eassumption. }
  destruct (type_is_correct _ _ HB HG') as [s HBs].
  assert (HP : @typ nat RankSorts n G (Π A B) (𝓤 (Nat.max (S a) s))).
  { eapply typ_Π; try eassumption. reflexivity. }
  assert (Hr : r = Nat.max (S a) s).
  { exact (convertible_sort_rank G T (Π A B) r (Nat.max (S a) s)
      HG HT HP Heq). }
  exists a. split; [exact HA | pose proof (Nat.le_max_l (S a) s); lia].
Qed.

Lemma typing_type_rank {n} G (t T : Term nat n) :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
  exists r, TypeRank G t r.
Proof.
  intros HG Ht. destruct (type_is_correct _ _ Ht HG) as [r Hr].
  exists r, T; auto.
Qed.

Lemma application_rank_le_function {n} G (f u : Term nat n) r s :
  @wf nat RankSorts n G -> TypeRank G (app f u) r ->
  TypeRank G f s -> r <= s.
Proof.
  intros HG Hrank HfRank. destruct Hrank as [T [Ht HT]].
  destruct (app_inversion RankSorts f u T Ht) as [U [V [Hf [Hu Heq]]]].
  destruct (application_result_rank G f u U V s HG Hf Hu HfRank)
    as [b [Hb Hle]].
  assert (r = b) by (eapply type_rank_unique; [exact HG | exists T; eauto | exact Hb]).
  lia.
Qed.

(** A newly exposed lambda cannot come from nowhere: some redex on the
    original application spine has at least its type rank. This includes
    exposure by substitution; no annotation-erasing translation is used. *)
Theorem exposed_lambda_rank {n} (t : Term nat n) : forall G r,
  @wf nat RankSorts n G -> TypeRank G t r ->
  isLambda t = false -> isLambda (greedy t) = true ->
  exists s, RedexRank G t s /\ r <= s.
Proof.
  induction t; intros G r HG Hrank Hbefore Hafter;
    try discriminate Hbefore; try discriminate Hafter.
  destruct Hrank as [T [Ht HT]].
  destruct (app_inversion RankSorts t1 t2 T Ht)
    as [U [V [Hf [Hu Heq]]]].
  destruct (type_is_correct _ _ Hf HG) as [s Hprod].
  assert (HfRank : TypeRank G t1 s) by (exists (Π U V); auto).
  assert (Hrs : r <= s).
  { eapply application_rank_le_function; [exact HG | exists T; eauto | exact HfRank]. }
  assert (Hhead : isLambda (greedy t1) = true).
  { cbn [greedy] in Hafter. destruct (greedy t1); try discriminate; reflexivity. }
  destruct (isLambda t1) eqn:Horiginal.
  - exists s. split; [|exact Hrs].
    destruct t1; try discriminate. eapply rr_beta; eassumption.
  - destruct (IHt1 G s HG HfRank eq_refl Hhead) as [q [Hq Hsq]].
    exists q. split; [apply rr_app_left; exact Hq | lia].
Qed.

(** Every head contracted during the bottom-up application clause is bounded
    by an original redex, even if the input head was not syntactically a lambda.
    Combined with application_argument_rank, its argument has rank < d. *)
Theorem greedy_contracted_head_bound {n} G (f u T : Term nat n) d r :
  @wf nat RankSorts n G -> @typ nat RankSorts n G (app f u) T ->
  RedexBound G (app f u) d -> isLambda (greedy f) = true ->
  TypeRank G (greedy f) r -> r <= d.
Proof.
  intros HG Ht Hbound Hlambda Hrank.
  destruct (app_inversion RankSorts f u T Ht) as [U [V [Hf [Hu Heq]]]].
  destruct (type_is_correct _ _ Hf HG) as [s Hprod].
  assert (HfRank : TypeRank G f s) by (exists (Π U V); auto).
  assert (Hsr : s = r).
  { eapply type_rank_unique; [exact HG | apply type_rank_greedy; eassumption | exact Hrank]. }
  destruct (isLambda f) eqn:Horiginal.
  - assert (Hr : RedexRank G (app f u) s).
    { destruct f; try discriminate. eapply rr_beta; eassumption. }
    specialize (Hbound s Hr). lia.
  - destruct (exposed_lambda_rank f G s HG HfRank Horiginal Hlambda)
      as [q [Hq Hsq]].
    specialize (Hbound q (rr_app_left G f u q Hq)). lia.
Qed.

Theorem redex_rank_positive {n} G (t : Term nat n) r :
  RedexRank G t r -> 0 < r.
Proof.
  intro H; induction H; try assumption.
  destruct (Π_inversion RankSorts U (𝓤 r) V H0)
    as [a [b' [s [Hrule [HA [HB Heq]]]]]].
  apply equiv_𝓤_inversion in Heq.
  change (s = Nat.max (S a) b') in Hrule.
  pose proof (Nat.le_max_l (S a) b'). lia.
Qed.
Lemma redex_bound_monotone {n} G (t : Term nat n) a b :
  RedexBound G t a -> a <= b -> RedexBound G t b.
Proof. unfold RedexBound; intros H Hab r Hr; specialize (H r Hr); lia. Qed.

Theorem nonnormal_has_redex_rank {n} (t : Term nat n) : forall G T,
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
  normalb t = false -> exists r, RedexRank G t r.
Proof.
  induction t; intros G T HG HT Hnormal; cbn [normalb] in Hnormal; try discriminate.
  - destruct (Π_inversion RankSorts t1 T t2 HT)
      as [a [b [s [Hrule [HA [HB Heq]]]]]].
    apply andb_false_iff in Hnormal as [Hna | Hnb].
    + destruct (IHt1 G (𝓤 a) HG HA Hna) as [r Hr]. exists r; apply rr_pi_left; exact Hr.
    + assert (HG' : wf (G & t1)) by (eapply wf_cons; eassumption).
      destruct (IHt2 (G & t1) (𝓤 b) HG' HB Hnb) as [r Hr].
      exists r; apply rr_pi_right; exact Hr.
  - destruct (λ_inversion RankSorts t1 T t2 HT) as [a [B [HA [HB Heq]]]].
    apply andb_false_iff in Hnormal as [Hna | Hnb].
    + destruct (IHt1 G (𝓤 a) HG HA Hna) as [r Hr]. exists r; apply rr_lam_left; exact Hr.
    + assert (HG' : wf (G & t1)) by (eapply wf_cons; eassumption).
      destruct (IHt2 (G & t1) B HG' HB Hnb) as [r Hr].
      exists r; apply rr_lam_right; exact Hr.
  - destruct (app_inversion RankSorts t1 t2 T HT) as [U [V [Hf [Hu Heq]]]].
    apply andb_false_iff in Hnormal as [Hchildren | Hhead].
    + apply andb_false_iff in Hchildren as [Hf' | Hu'].
      * destruct (IHt1 G (Π U V) HG Hf Hf') as [r Hr]. exists r; apply rr_app_left; exact Hr.
      * destruct (IHt2 G U HG Hu Hu') as [r Hr]. exists r; apply rr_app_right; exact Hr.
    + destruct t1; cbn [isLambda] in Hhead; try discriminate.
      destruct (type_is_correct _ _ Hf HG) as [r Hr].
      exists r. eapply rr_beta; eassumption.
Qed.
Theorem zero_bound_normal {n} G (t T : Term nat n) :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
  RedexBound G t 0 -> normalb t = true.
Proof.
  intros HG HT Hbound. destruct (normalb t) eqn:Hnormal; [reflexivity |].
  destruct (nonnormal_has_redex_rank t G T HG HT Hnormal) as [r Hr].
  pose proof (redex_rank_positive G t r Hr). specialize (Hbound r Hr). lia.
Qed.

(** Descent.v proves strict greedy descent using these semantic ranks.
    AutomaticBound.v supplies a conservative linear-cost rank bound.
    The manuscript's estimateRank+1 head-rank bridge is false; see the
    kernel-checked counterexample in EstimatorChecks.v. *)
