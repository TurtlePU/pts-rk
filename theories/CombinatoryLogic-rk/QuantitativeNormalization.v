From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia.
From PTSrk Require Import Syntax Context Typing Inversions Preservation Ranks
  Reduction DefEq AbstractRewriting.
From PTSrk.NormalizationComplexity Require Import Greedy Bounds Runtime
  RedexRanks Safety Descent BoundedNormalization.
From PTSrk.Combinatory Require Import Core.

(** A sequential beta path with an explicit bound on EVERY intermediate
    annotated syntax tree, not merely on the endpoints of parallel passes. *)
Inductive BoundedSteps {n} (limit : nat) : Term nat n -> Term nat n -> Prop :=
| bs_refl t : nodes t <= limit -> BoundedSteps limit t t
| bs_step t u v : nodes t <= limit -> step nat n t u ->
    BoundedSteps limit u v -> BoundedSteps limit t v.

Lemma bounded_steps_start {n} limit (t u : Term nat n) :
  BoundedSteps limit t u -> nodes t <= limit.
Proof. intro H; destruct H; assumption. Qed.

Lemma bounded_steps_end {n} limit (t u : Term nat n) :
  BoundedSteps limit t u -> nodes u <= limit.
Proof. intro H; induction H; assumption. Qed.

Lemma bounded_steps_sound {n} limit (t u : Term nat n) :
  BoundedSteps limit t u -> reduces_to nat n t u.
Proof.
  intro H; induction H; [constructor | eapply rtc_step; eassumption].
Qed.

Lemma bounded_steps_weaken {n} a b (t u : Term nat n) :
  BoundedSteps a t u -> a <= b -> BoundedSteps b t u.
Proof.
  intros H Hab; induction H; [constructor; lia |].
  eapply bs_step; [lia | exact H0 | exact IHBoundedSteps].
Qed.

Lemma bounded_steps_trans {n} limit (t u v : Term nat n) :
  BoundedSteps limit t u -> BoundedSteps limit u v ->
  BoundedSteps limit t v.
Proof.
  intro H; induction H; intro Huv; [exact Huv |].
  eapply bs_step; [exact H | exact H0 | apply IHBoundedSteps; exact Huv].
Qed.

Lemma bounded_steps_snoc {n} limit (t u v : Term nat n) :
  BoundedSteps limit t u -> step nat n u v -> nodes v <= limit ->
  BoundedSteps limit t v.
Proof.
  intros H Hu Hv. eapply bounded_steps_trans; [exact H |].
  eapply bs_step; [eapply bounded_steps_end; exact H | exact Hu |].
  constructor; exact Hv.
Qed.

Lemma bounded_steps_map {m n} a b (F : Term nat m -> Term nat n)
  (t u : Term nat m) :
  (forall x y, step nat m x y -> step nat n (F x) (F y)) ->
  (forall x, nodes x <= a -> nodes (F x) <= b) ->
  BoundedSteps a t u -> BoundedSteps b (F t) (F u).
Proof.
  intros Hstep Hsize H; induction H.
  - constructor; auto.
  - eapply bs_step; [auto | apply Hstep; exact H0 | exact IHBoundedSteps].
Qed.

Lemma bounded_steps_binary {m n p} a b
  (C : Term nat m -> Term nat n -> Term nat p)
  (x x' : Term nat m) (y y' : Term nat n) :
  (forall s s' t, step nat m s s' -> step nat p (C s t) (C s' t)) ->
  (forall s t t', step nat n t t' -> step nat p (C s t) (C s t')) ->
  (forall s t, nodes (C s t) = S (nodes s + nodes t)) ->
  BoundedSteps a x x' -> BoundedSteps b y y' ->
  BoundedSteps (S (a+b)) (C x y) (C x' y').
Proof.
  intros HL HR HC Hx Hy.
  pose proof (bounded_steps_start _ _ _ Hy) as Hys.
  pose proof (bounded_steps_end _ _ _ Hx) as Hxe.
  eapply bounded_steps_trans with (u := C x' y).
  - eapply bounded_steps_map with (F := fun s => C s y);
      [intros; apply HL; assumption | | exact Hx].
    intros s Hs; rewrite HC; lia.
  - eapply bounded_steps_map with (F := C x');
      [intros; apply HR; assumption | | exact Hy].
    intros t Ht; rewrite HC; lia.
Qed.

(** The proof chooses annotation/left child first, body/right child second,
    then the root contraction: a deterministic sequentialization of greedy. *)
Theorem greedy_bounded_steps {n} (t : Term nat n) :
  BoundedSteps (2 ^ nodes t) t (greedy t).
Proof.
  induction t; cbn [greedy].
  - apply bs_refl; cbn; lia.
  - eapply bounded_steps_weaken.
    + eapply bounded_steps_binary; [intros; constructor; assumption |
        intros; constructor; assumption | intros; reflexivity | exact IHt1 | exact IHt2].
    + apply exponential_join; apply nodes_positive.
  - apply bs_refl; cbn; lia.
  - eapply bounded_steps_weaken.
    + eapply bounded_steps_binary; [intros; constructor; assumption |
        intros; constructor; assumption | intros; reflexivity | exact IHt1 | exact IHt2].
    + apply exponential_join; apply nodes_positive.
  - assert (Hchildren : BoundedSteps (2 ^ nodes (app t1 t2))
        (app t1 t2) (app (greedy t1) (greedy t2))).
    { eapply bounded_steps_weaken.
      - eapply bounded_steps_binary; [intros; constructor; assumption |
          intros; constructor; assumption | intros; reflexivity | exact IHt1 | exact IHt2].
      - apply exponential_join; apply nodes_positive. }
    pose proof (greedy_size (app t1 t2)) as Hfinal.
    cbn [greedy] in Hfinal. destruct (greedy t1); try exact Hchildren.
    eapply bounded_steps_snoc; [exact Hchildren | constructor | exact Hfinal].
Qed.

Lemma tower_exponential h x : tower h (2^x) = tower (S h) x.
Proof. induction h; cbn [tower]; [reflexivity | rewrite IHh; reflexivity]. Qed.

Theorem rounds_bounded_steps {n} k (t : Term nat n) :
  BoundedSteps (tower k (nodes t)) t (rounds k t).
Proof.
  revert t; induction k; intro t; cbn [rounds].
  - constructor; cbn [tower]; lia.
  - eapply bounded_steps_trans with (u := greedy t).
    + eapply bounded_steps_weaken; [apply greedy_bounded_steps |].
      change (tower 1 (nodes t) <= tower (S k) (nodes t)).
      apply tower_height_monotone; lia.
    + eapply bounded_steps_weaken; [apply IHk |].
      rewrite <- tower_exponential. apply tower_monotone; apply greedy_size.
Qed.

Theorem fixed_rank_peak_normalization {n} d G (t T : Term nat n) :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
  RedexBound G t d ->
  BoundedSteps (tower d (nodes t)) t (rounds d t) /\
  normalb (rounds d t) = true /\
  @typ nat RankSorts n G (rounds d t) T /\
  nodes (rounds d t) <= tower d (nodes t) /\
  snd (normalizeCosted d t) <= tower (2*d+1) (nodes t+5*d+2).
Proof.
  intros HG Ht HB. split; [apply rounds_bounded_steps |].
  split; [eapply bounded_rounds_normal; eassumption |].
  split; [eapply subject_reduction'; [exact Ht | exact HG | apply rounds_sound] |].
  split; [apply rounds_size |]. rewrite Nat.add_1_r; apply normalizeCosted_elementary.
Qed.

Theorem rounds_rank_bound {n} k G (t T : Term nat n) d :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
  RedexBound G t d -> RedexBound G (rounds k t) d.
Proof.
  revert t T; induction k; intros t T HG Ht HB; cbn [rounds]; [exact HB |].
  eapply IHk; [exact HG | |].
  - eapply subject_reduction'; [exact Ht | exact HG | apply greedy_sound].
  - eapply greedy_strict_descent; [exact HG | exact Ht |].
    eapply redex_bound_monotone; [exact HB | lia].
Qed.

Lemma step_exposed_lambda_rank {n} G (t u : Term nat n) r :
  @wf nat RankSorts n G -> TypeRank G t r -> step nat n t u ->
  isLambda t = false -> isLambda u = true ->
  exists s, RedexRank G t s /\ r <= s.
Proof.
  intros HG Hr Hstep Hbefore Hafter. destruct Hstep;
    cbn [isLambda] in Hbefore, Hafter; try discriminate.
  destruct Hr as [R [Ht HR]].
  destruct (app_inversion RankSorts (lam T f) t R Ht)
    as [A [B [Hf [Hu Heq]]]].
  destruct (type_is_correct _ _ Hf HG) as [s HP].
  assert (Hfr : TypeRank G (lam T f) s) by (exists (Π A B); auto).
  destruct (application_result_rank G (lam T f) t A B s HG Hf Hu Hfr)
    as [q [Hq Hqs]].
  assert (Htr : TypeRank G (app (lam T f) t) r) by (exists R; auto).
  pose proof (type_rank_unique G (app (lam T f) t) r q HG Htr Hq).
  exists s; split; [eapply rr_beta; eassumption | lia].
Qed.

Theorem step_rank_safe {n} (t u : Term nat n) : step nat n t u ->
  forall G T d, @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
  RankSafe G t d -> RankSafe G u d.
Proof.
  intro Hstep; induction Hstep; intros G R d HG Ht HS; cbn [RankSafe] in HS |- *.
  - destruct (Π_inversion RankSorts T R U Ht)
      as [a [b [r [Hrule [HA [HB HE]]]]]]. destruct HS as [HSA HSB].
    split; [eapply IHHstep; eassumption |].
    eapply safe_context_last_reduction; [exact HG | exact HA |
      apply rtc_in; exact Hstep | exact HB | exact HSB].
  - destruct (Π_inversion RankSorts T R U Ht)
      as [a [b [r [Hrule [HA [HB HE]]]]]]. destruct HS as [HSA HSB].
    split; [exact HSA |]. eapply IHHstep; [eapply wf_cons; eassumption | exact HB | exact HSB].
  - destruct (λ_inversion RankSorts T R t Ht) as [a [B [HA [HB HE]]]].
    destruct HS as [HSA HSB]. split; [eapply IHHstep; eassumption |].
    eapply safe_context_last_reduction; [exact HG | exact HA |
      apply rtc_in; exact Hstep | exact HB | exact HSB].
  - destruct (λ_inversion RankSorts T R t Ht) as [a [B [HA [HB HE]]]].
    destruct HS as [HSA HSB]. split; [exact HSA |].
    eapply IHHstep; [eapply wf_cons; eassumption | exact HB | exact HSB].
  - destruct (app_inversion RankSorts f t R Ht) as [A [B [Hf [Hu HE]]]].
    destruct HS as [HSf [HSu HH]]. split; [eapply IHHstep; eassumption |].
    split; [exact HSu |]. intros Hlambda r Hr.
    destruct (type_is_correct _ _ Hf HG) as [q HP].
    assert (Hfr : TypeRank G f q) by (exists (Π A B); auto).
    assert (Hf'r : TypeRank G f' q).
    { eapply type_rank_reduction; [exact HG | exact Hfr | apply rtc_in; exact Hstep]. }
    assert (Er : r = q) by (eapply type_rank_unique; eassumption).
    subst r. destruct (isLambda f) eqn:Hlf.
    + exact (HH eq_refl q Hfr).
    + destruct (step_exposed_lambda_rank G f f' q HG Hfr Hstep Hlf Hlambda)
        as [s [Hs Hqs]].
      pose proof (safe_to_bound G f d HSf s Hs); lia.
  - destruct (app_inversion RankSorts f t R Ht) as [A [B [Hf [Hu HE]]]].
    destruct HS as [HSf [HSu HH]]. split; [exact HSf |].
    split; [eapply IHHstep; eassumption | exact HH].
  - destruct (app_inversion RankSorts (lam T f) t R Ht)
      as [A [B [Hf [Hu HE]]]].
    destruct HS as [[HSA HSbody] [HSu HH]].
    destruct (type_is_correct _ _ Hf HG) as [r HP].
    assert (Hfr : TypeRank G (lam T f) r) by (exists (Π A B); auto).
    pose proof (HH eq_refl r Hfr) as Hrd.
    destruct (application_argument_rank G (lam T f) t A B r HG Hf Hu Hfr)
      as [a [Ha Har]].
    destruct (λ_inversion RankSorts T (Π A B) f Hf)
      as [b [C [HT [Hbody Hconv]]]].
    apply equiv_Π_inversion in Hconv as [HAT HBC].
    assert (HuT : @typ nat RankSorts n G t T).
    { eapply typ_conv; [exact Hu | exact HT | exact HAT]. }
    replace d with (Nat.max d a) by lia.
    eapply safe_substitution; [exact HG | eapply wf_cons; eassumption |
      exact HuT | exact Hbody | exact Ha | exact HSu | exact HSbody].
Qed.

Theorem reduction_preserves_rank_bound {n} G (t u T : Term nat n) d :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
  RedexBound G t d -> reduces_to nat n t u -> RedexBound G u d.
Proof.
  intros HG Ht HB HR; revert T Ht HB. induction HR; intros T Ht HB; [exact HB |].
  apply IHHR with T.
  - eapply subject_reduction; eassumption.
  - apply safe_to_bound. eapply step_rank_safe; [exact H | exact HG | exact Ht |].
    eapply bound_to_safe; eassumption.
Qed.

Lemma normal_rank_safe {n} (t : Term nat n) :
  normalb t = true -> forall G d, RankSafe G t d.
Proof.
  induction t; cbn [normalb RankSafe]; intros H G d; try exact I.
  - apply andb_true_iff in H as [HA HB]; split; auto.
  - apply andb_true_iff in H as [HA HB]; split; auto.
  - apply andb_true_iff in H as [Hpair Hhead].
    apply andb_true_iff in Hpair as [Hf Hu].
    split; [auto |]. split; [auto |].
    intros Hl; rewrite Hl in Hhead; discriminate.
Qed.

(** Outer type rank is not a bound on redex heads.  All these closed terms
    have type U_0 and exactly thirteen syntax nodes, but their head ranks
    are unbounded.  Numeric labels are not charged by [nodes]. *)
Definition discarded_identity a : Term nat 0 :=
  app (lam (Core.identity_type a) (𝓤 0)) (Core.identity a).

Lemma discarded_identity_typed a :
  @typ nat RankSorts 0 ε (discarded_identity a) (𝓤 0).
Proof.
  unfold discarded_identity.
  change (typ ε (app (lam (Core.identity_type a) (𝓤 0)) (Core.identity a))
    (subst (𝓤 0) (Core.identity a))).
  eapply typ_app with (U := Core.identity_type a).
  - eapply typ_λ; [apply Core.identity_type_sorted | constructor; reflexivity].
  - apply Core.identity_typed.
Qed.

Lemma discarded_identity_head_rank a :
  RedexRank ε (discarded_identity a) (S (S a)).
Proof.
  unfold discarded_identity. eapply rr_beta with
    (U := Core.identity_type a) (V := 𝓤 0).
  - eapply typ_λ; [apply Core.identity_type_sorted | constructor; reflexivity].
  - eapply typ_Π with (ℓₜ := S a) (ℓᵤ := 0).
    + apply Core.identity_type_sorted.
    + constructor; reflexivity.
    + reflexivity.
Qed.

Theorem outer_rank_does_not_bound_redexes :
  forall d, exists t : Term nat 0,
    TypeRank ε t 0 /\ nodes t = 13 /\ ~ RedexBound ε t d.
Proof.
  intro d; exists (discarded_identity d); split.
  - exists (𝓤 0); split; [apply discarded_identity_typed | constructor; reflexivity].
  - split; [reflexivity |].
    intro HB; specialize (HB (S (S d)) (discarded_identity_head_rank d)); lia.
Qed.

(** Normal inputs have no internal redexes, even in their annotations.
    Thus the rank of the FUNCTION'S TYPE bounds normalized application. *)
Theorem normal_application_rank_bound {n} G (f y : Term nat n) r :
  @wf nat RankSorts n G ->
  normalb f = true -> normalb y = true -> TypeRank G f r ->
  RedexBound G (app f y) r.
Proof.
  intros HG Hf Hy Hr. apply safe_to_bound; cbn [RankSafe].
  split; [apply normal_rank_safe; exact Hf |].
  split; [apply normal_rank_safe; exact Hy |].
  intros _ s Hs. pose proof (type_rank_unique G f s r HG Hs Hr); lia.
Qed.

Theorem normalized_application {n} G (f y A : Term nat n)
  (B : Term nat (S n)) r :
  @wf nat RankSorts n G ->
  @typ nat RankSorts n G f (Π A B) ->
  @typ nat RankSorts n G y A ->
  @typ nat RankSorts n G (Π A B) (𝓤 r) ->
  normalb f = true -> normalb y = true ->
  BoundedSteps (tower r (1 + nodes f + nodes y))
    (app f y) (rounds r (app f y)) /\
  normalb (rounds r (app f y)) = true /\
  @typ nat RankSorts n G (rounds r (app f y)) (subst B y) /\
  nodes (rounds r (app f y)) <= tower r (1 + nodes f + nodes y) /\
  snd (normalizeCosted r (app f y)) <=
    tower (2*r+1) (1 + nodes f + nodes y + 5*r+2).
Proof.
  intros HG Hf Hy HP Hnf Hny.
  change (1 + nodes f + nodes y) with (nodes (app f y)).
  apply fixed_rank_peak_normalization; [exact HG | eapply typ_app; eassumption |].
  apply normal_application_rank_bound; try assumption.
  exists (Π A B); auto.
Qed.

Print Assumptions greedy_bounded_steps.
Print Assumptions rounds_bounded_steps.
Print Assumptions fixed_rank_peak_normalization.
Print Assumptions rounds_rank_bound.
Print Assumptions reduction_preserves_rank_bound.
Print Assumptions normal_application_rank_bound.
Print Assumptions normalized_application.
Print Assumptions outer_rank_does_not_bound_redexes.
