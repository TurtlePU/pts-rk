From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia.
From Equations Require Import Equations.
From PTSrk Require Import Syntax Context Typing Inversions Preservation Ranks Reduction.
Require Import PTSrk.NormalizationComplexity.Greedy
  PTSrk.NormalizationComplexity.RedexRanks
  PTSrk.NormalizationComplexity.Morphisms.

(** Structural presentation of exactly the same semantic occurrence bound.
    Its equivalence below is for original well-typed terms, not a new typing
    relation or a stronger notion of admissible input. *)
Fixpoint RankSafe {n} (G : Ctx nat n) (t : Term nat n) d : Prop :=
  match t with
  | 𝓤 _ | var _ => True
  | Π A B | lam A B => RankSafe G A d /\ RankSafe (G & A) B d
  | app f u => RankSafe G f d /\ RankSafe G u d /\
      (isLambda f = true -> forall r, TypeRank G f r -> r <= d)
  end.

Lemma safe_to_bound {n} G (t : Term nat n) d :
  RankSafe G t d -> RedexBound G t d.
Proof.
  intros HS r Hr. induction Hr; cbn [RankSafe] in HS.
  - destruct HS as [_ [_ Hroot]]. apply Hroot; [reflexivity |].
    eexists; split; eassumption.
  - apply IHHr; tauto.
  - apply IHHr; tauto.
  - apply IHHr; tauto.
  - apply IHHr; tauto.
  - apply IHHr; tauto.
  - apply IHHr; tauto.
Qed.

Lemma bound_to_safe {n} (t : Term nat n) : forall G T d,
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
  RedexBound G t d -> RankSafe G t d.
Proof.
  induction t; intros G T d HG Ht Hbound; cbn [RankSafe]; try exact I.
  - destruct (Π_inversion RankSorts t1 T t2 Ht)
      as [a [b [r [Hr [HA [HB Heq]]]]]]. split.
    + eapply IHt1; eauto. intros q Hq. apply Hbound. apply rr_pi_left; exact Hq.
    + eapply IHt2; [eapply wf_cons; eassumption | exact HB |].
      intros q Hq. apply Hbound. apply rr_pi_right; exact Hq.
  - destruct (λ_inversion RankSorts t1 T t2 Ht) as [a [B [HA [HB Heq]]]]. split.
    + eapply IHt1; eauto. intros q Hq. apply Hbound. apply rr_lam_left; exact Hq.
    + eapply IHt2; [eapply wf_cons; eassumption | exact HB |].
      intros q Hq. apply Hbound. apply rr_lam_right; exact Hq.
  - destruct (app_inversion RankSorts t1 t2 T Ht) as [U [V [Hf [Hu Heq]]]].
    split; [eapply IHt1; eauto; intros q Hq; apply Hbound; apply rr_app_left; exact Hq |].
    split; [eapply IHt2; eauto; intros q Hq; apply Hbound; apply rr_app_right; exact Hq |].
    intros Hl r Hr. destruct (type_is_correct _ _ Hf HG) as [s Hs].
    assert (E : r = s).
    { eapply type_rank_unique; [exact HG | exact Hr | exists (Π U V); auto]. }
    subst r. apply Hbound. destruct t1; try discriminate. eapply rr_beta; eassumption.
Qed.

Theorem safe_iff_bound {n} G (t T : Term nat n) d :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
  (RankSafe G t d <-> RedexBound G t d).
Proof. intros; split; [apply safe_to_bound | eapply bound_to_safe; eassumption]. Qed.

Lemma safe_monotone {n} (t : Term nat n) : forall G a b,
  RankSafe G t a -> a <= b -> RankSafe G t b.
Proof.
  induction t; intros G a b H Hab; cbn [RankSafe] in *; try exact I.
  - destruct H; split; eauto.
  - destruct H; split; eauto.
  - destruct H as [Hf [Hu Hhead]]. split; [eauto |]. split; [eauto |].
    intros Hl r Hr. specialize (Hhead Hl r Hr). lia.
Qed.

Lemma isLambda_rename {m n} (f : Fin m -> Fin n) (t : Term nat m) :
  isLambda (rename f t) = isLambda t.
Proof. destruct t; reflexivity. Qed.

Theorem safe_rename {m} (t : Term nat m) : forall G T n D (f : Fin m -> Fin n) d,
  @wf nat RankSorts m G -> @wf nat RankSorts n D ->
  @typ nat RankSorts m G t T -> TypedRen G D f ->
  RankSafe G t d -> RankSafe D (rename f t) d.
Proof.
  induction t; intros G T k D ren d HG HD Ht Hf HS;
    cbn [rename RankSafe] in *; try exact I.
  - destruct (Π_inversion RankSorts t1 T t2 Ht)
      as [a [b [r [Hr [HA [HB Heq]]]]]]. destruct HS as [HSa HSb]. split.
    + eapply IHt1; eassumption.
    + eapply IHt2; [eapply wf_cons; eassumption | | exact HB | apply typed_ren_lift; exact Hf | exact HSb].
      eapply wf_cons with (ℓ := a); [exact HD |].
      change (typ D (rename ren t1) (rename ren (𝓤 a))). eapply typing_rename; eassumption.
  - destruct (λ_inversion RankSorts t1 T t2 Ht) as [a [B [HA [HB Heq]]]].
    destruct HS as [HSa HSb]. split.
    + eapply IHt1; eassumption.
    + eapply IHt2; [eapply wf_cons; eassumption | | exact HB | apply typed_ren_lift; exact Hf | exact HSb].
      eapply wf_cons with (ℓ := a); [exact HD |].
      change (typ D (rename ren t1) (rename ren (𝓤 a))). eapply typing_rename; eassumption.
  - destruct (app_inversion RankSorts t1 t2 T Ht) as [U [V [Hhead [Hu Heq]]]].
    destruct HS as [HSf [HSu HShead]]. split; [eapply IHt1; eassumption |].
    split; [eapply IHt2; eassumption |].
    rewrite isLambda_rename. intros Hl r Hr. apply HShead; [exact Hl |].
    rewrite <- replace_as_rename in Hr.
    eapply type_rank_replace_reflect; eassumption.
Qed.

Corollary safe_shift {n} G (t T A : Term nat n) d a :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
  @typ nat RankSorts n G A (𝓤 a) -> RankSafe G t d ->
  RankSafe (G & A) (shift t) d.
Proof.
  intros. eapply safe_rename; eauto using typed_ren_shift.
  eapply wf_cons; eassumption.
Qed.

Definition SafeImages {m n} (D : Ctx nat n) (s : Fin m -> Term nat n) d :=
  forall i, RankSafe D (s i) d /\
    (isLambda (s i) = true -> forall r, TypeRank D (s i) r -> r <= d).

Lemma safe_images_lift {m n} G D (s : Fin m -> Term nat n) A d a :
  @wf nat RankSorts n D -> TypedSub G D s ->
  @typ nat RankSorts n D (replace s A) (𝓤 a) ->
  SafeImages D s d -> SafeImages (D & replace s A) (transpose s) d.
Proof.
  intros HD Hs HA HI i. dependent elimination i; cbn [transpose fin_match].
  - split; [exact I | discriminate].
  - destruct (HI f) as [HS HH]. split.
    + eapply safe_shift; eauto.
    + unfold shift. rewrite isLambda_rename. intros Hl r Hr. apply HH; [exact Hl |].
      rewrite <- replace_as_rename in Hr.
      eapply type_rank_replace_reflect; [exact HD | eapply wf_cons; eassumption | | apply Hs | exact Hr].
      apply typed_ren_shift.
Qed.

Theorem safe_replace {m} (t : Term nat m) : forall G T n D (s : Fin m -> Term nat n) d,
  @wf nat RankSorts m G -> @wf nat RankSorts n D ->
  @typ nat RankSorts m G t T -> TypedSub G D s ->
  SafeImages D s d -> RankSafe G t d -> RankSafe D (replace s t) d.
Proof.
  induction t; intros G T k D sigma d HG HD Ht Hs HI HS;
    cbn [replace RankSafe] in *; try exact I.
  - destruct (Π_inversion RankSorts t1 T t2 Ht)
      as [a [b [r [Hr [HA [HB Heq]]]]]]. destruct HS as [HSa HSb].
    assert (HAs : @typ nat RankSorts k D (replace sigma t1) (𝓤 a)).
    { change (typ D (replace sigma t1) (replace sigma (𝓤 a))). eapply typing_replace; eassumption. }
    split; [eapply IHt1; eassumption |].
    eapply IHt2; [eapply wf_cons; eassumption | eapply wf_cons; eassumption | exact HB |
      apply typed_sub_lift; exact Hs | eapply safe_images_lift; eassumption | exact HSb].
  - exact (proj1 (HI f)).
  - destruct (λ_inversion RankSorts t1 T t2 Ht) as [a [B [HA [HB Heq]]]].
    destruct HS as [HSa HSb].
    assert (HAs : @typ nat RankSorts k D (replace sigma t1) (𝓤 a)).
    { change (typ D (replace sigma t1) (replace sigma (𝓤 a))). eapply typing_replace; eassumption. }
    split; [eapply IHt1; eassumption |].
    eapply IHt2; [eapply wf_cons; eassumption | eapply wf_cons; eassumption | exact HB |
      apply typed_sub_lift; exact Hs | eapply safe_images_lift; eassumption | exact HSb].
  - destruct (app_inversion RankSorts t1 t2 T Ht) as [U [V [Hf [Hu Heq]]]].
    destruct HS as [HSf [HSu HH]]. split; [eapply IHt1; eassumption |].
    split; [eapply IHt2; eassumption |].
    intros Hl r Hr. destruct t1; try discriminate Hl.
    + exact (proj2 (HI f) Hl r Hr).
    + apply HH; [reflexivity |]. eapply type_rank_replace_reflect; eassumption.
Qed.

Lemma typed_sub_single {n} G (u U : Term nat n) :
  @typ nat RankSorts n G u U ->
  TypedSub (G & U) G (fin_match u (fun i => var i)).
Proof.
  intros Hu i. dependent elimination i; cbn [fin_match index ctx_top ctx_pred].
  - unfold shift. rewrite replace_rename. cbn. rewrite replace_var. exact Hu.
  - unfold shift. rewrite replace_rename. cbn. rewrite replace_var. constructor.
Qed.

Theorem safe_substitution {n} G (u U : Term nat n) (t T : Term nat (S n)) d a :
  @wf nat RankSorts n G -> @wf nat RankSorts (S n) (G & U) ->
  @typ nat RankSorts n G u U -> @typ nat RankSorts (S n) (G & U) t T ->
  TypeRank G u a -> RankSafe G u d -> RankSafe (G & U) t d ->
  RankSafe G (subst t u) (Nat.max d a).
Proof.
  intros HG HGU Hu Ht Hr HSu HSt. unfold subst.
  eapply safe_replace; [exact HGU | exact HG | exact Ht | apply typed_sub_single; exact Hu | |].
  - intros i. dependent elimination i; cbn [fin_match].
    + split; [eapply safe_monotone; [exact HSu | apply Nat.le_max_l] |].
      intros Hl r Hr'. assert (E : a = r) by (exact (type_rank_unique G u a r HG Hr Hr')).
      subst; apply Nat.le_max_r.
    + split; [exact I | discriminate].
  - eapply safe_monotone; [exact HSt | apply Nat.le_max_l].
Qed.

Corollary redex_bound_substitution {n} G (u U : Term nat n) (t T : Term nat (S n)) d a :
  @wf nat RankSorts n G -> @wf nat RankSorts (S n) (G & U) ->
  @typ nat RankSorts n G u U -> @typ nat RankSorts (S n) (G & U) t T ->
  TypeRank G u a -> RedexBound G u d -> RedexBound (G & U) t d ->
  RedexBound G (subst t u) (Nat.max d a).
Proof.
  intros. apply safe_to_bound. eapply safe_substitution; try eassumption;
    eapply bound_to_safe; eassumption.
Qed.

Theorem safe_context_last_reduction {n} G (A A' : Term nat n) (t T : Term nat (S n)) d a :
  @wf nat RankSorts n G -> @typ nat RankSorts n G A (𝓤 a) ->
  reduces_to nat n A A' -> @typ nat RankSorts (S n) (G & A) t T ->
  RankSafe (G & A) t d -> RankSafe (G & A') t d.
Proof.
  intros HG HA HR Ht HS. rewrite <- (rename_id t).
  eapply safe_rename; [eapply wf_cons; eassumption | | exact Ht | | exact HS].
  - eapply wf_cons with (ℓ := a); [exact HG |]. eapply subject_reduction'; eassumption.
  - eapply typed_ren_context_last; eassumption.
Qed.
