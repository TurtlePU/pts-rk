From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting Congruence DefEq.
From PTSrk.NormalizationComplexity Require Import Greedy Morphisms.
From PTSrk.SelfInterpreter Require Import BrownPalsberg IndexedEquality
  ContextualTelescope UniformTelescope UniformTelescopeRecovery ContextualTelescopeRun.
Import Context ListNotations.

(** Internal equality of WHOLE dependent argument spines. The telescope and
    all argument substitutions have independent original typing evidence.
    This is not pointwise-to-function equality or a source-quoter premise. *)
Module TelescopeEquality.
Module BP := BrownPalsberg.BrownPalsberg.
Module IE := IndexedEquality.IndexedEquality.
Module CT := ContextualTelescope.ContextualTelescope.
Module UT := UniformTelescope.UniformTelescope.
Module UR := UniformTelescopeRecovery.UniformTelescopeRecovery.
Module TR := ContextualTelescopeRun.ContextualTelescopeRun.

Definition shifted {m n} (sigma : Fin m -> Term nat n) i := shift (sigma i).
Definition same_base {m rs n} (sigma tau : Fin (CT.scope rs m) -> Term nat n) :=
  forall i, @TR.base m rs n sigma i = TR.base tau i.
Definition predicate_type d {m rs} (D : CT.telescope m rs) {n}
    (sigma : Fin (CT.scope rs m) -> Term nat n) :=
  replace (TR.base sigma) (CT.close_type D (𝓤 d)).
Definition eq_type d {m rs} (D : CT.telescope m rs) {n}
    (sigma tau : Fin (CT.scope rs m) -> Term nat n) :=
  Π (predicate_type d D sigma)
    (BP.arr (TR.run D (shifted sigma) (var fzero))
      (TR.run D (shifted tau) (var fzero))).
Definition refl_case d {m rs} (D : CT.telescope m rs) {n}
    (sigma : Fin (CT.scope rs m) -> Term nat n) :=
  lam (predicate_type d D sigma)
    (lam (TR.run D (shifted sigma) (var fzero)) (var fzero)).
Definition rank rs d := Nat.max (S (CT.ceiling rs)) (S d).

Lemma run_ext m rs (D : CT.telescope m rs) : forall n sigma tau q,
  (forall i, sigma i = tau i) -> @TR.run m rs D n sigma q = TR.run D tau q.
Proof. induction D; intros; cbn [TR.run]; [reflexivity | rewrite H; apply IHD; exact H]. Qed.

Lemma run_replace m rs (D : CT.telescope m rs) : forall n p sigma q (theta : Fin n -> Term nat p),
  replace theta (TR.run D sigma q) = TR.run D (fun i => replace theta (sigma i)) (replace theta q).
Proof. induction D; intros; cbn [TR.run]; [reflexivity | rewrite IHD; reflexivity]. Qed.

Lemma base_typed m rs (D : CT.telescope m rs) n G (H : Ctx nat n) sigma :
  TypedSub (CT.context D G) H sigma -> TypedSub G H (@TR.base m rs n sigma).
Proof.
  intros HS i; specialize (HS (UT.base_ren rs i)); rewrite TR.index_base in HS.
  rewrite replace_rename in HS; exact HS.
Qed.

Lemma shifted_typed m n (G : Ctx nat m) (H : Ctx nat n) sigma A :
  TypedSub G H sigma -> TypedSub G (H & A) (shifted sigma).
Proof.
  intros HS i; unfold shifted, shift; rewrite <- rename_replace; apply weakening, HS.
Qed.

Lemma predicate_type_sort d m rs (D : CT.telescope m rs) n G (H : Ctx nat n) sigma :
  CT.formed G D -> TypedSub (CT.context D G) H sigma ->
  @typ nat RankSorts n H (predicate_type d D sigma) (𝓤 (CT.ceiling rs)).
Proof.
  intros HD HS; change (typ H (replace (TR.base sigma) (CT.close_type D (𝓤 d)))
    (replace (TR.base sigma) (𝓤 (CT.ceiling rs)))).
  eapply typing_replace; [apply CT.close_type_sort; [exact HD | constructor; reflexivity] |].
  apply base_typed with (D := D); exact HS.
Qed.

Lemma predicate_shift d m rs (D : CT.telescope m rs) n sigma :
  @predicate_type d m rs D (S n) (shifted sigma) = shift (predicate_type d D sigma).
Proof. unfold predicate_type, shifted, TR.base, shift; rewrite rename_replace; reflexivity. Qed.

Lemma observe_typed d m rs (D : CT.telescope m rs) n G (H : Ctx nat n) sigma P :
  TypedSub (CT.context D G) H sigma ->
  @typ nat RankSorts n H P (predicate_type d D sigma) ->
  @typ nat RankSorts n H (TR.run D sigma P) (𝓤 d).
Proof.
  intros HS HP; change (typ H (TR.run D sigma P) (replace sigma (𝓤 d))).
  eapply TR.run_typing; eassumption.
Qed.

Lemma bound_observe_typed d m rs (D : CT.telescope m rs) n G (H : Ctx nat n) sigma tau :
  TypedSub (CT.context D G) H tau -> same_base sigma tau ->
  @typ nat RankSorts (S n) (H & predicate_type d D sigma)
    (TR.run D (shifted tau) (var fzero)) (𝓤 d).
Proof.
  intros HT HB; eapply observe_typed with (G := G).
  - apply shifted_typed; exact HT.
  - rewrite predicate_shift.
    assert (HE : predicate_type d D tau = predicate_type d D sigma).
    { unfold predicate_type; apply replace_ext; intro i; symmetry; apply HB. }
    rewrite HE; change (typ (H & predicate_type d D sigma) (var fzero)
      ((H & predicate_type d D sigma) !! fzero)); constructor.
Qed.

Theorem eq_type_sort d m rs (D : CT.telescope m rs) n G (H : Ctx nat n) sigma tau :
  CT.formed G D -> TypedSub (CT.context D G) H sigma ->
  TypedSub (CT.context D G) H tau -> same_base sigma tau ->
  @typ nat RankSorts n H (eq_type d D sigma tau) (𝓤 (rank rs d)).
Proof.
  intros HD HS HT HB; unfold eq_type, rank.
  eapply typ_Π with (ℓₜ := CT.ceiling rs) (ℓᵤ := S d).
  - eapply predicate_type_sort; eassumption.
  - replace (S d) with (Nat.max (S d) d) by lia; apply BP.arr_sort.
    + eapply bound_observe_typed; [exact HS | intro i; reflexivity].
    + eapply bound_observe_typed; eassumption.
  - reflexivity.
Qed.

Theorem refl_case_typed d m rs (D : CT.telescope m rs) n G (H : Ctx nat n) sigma :
  CT.formed G D -> TypedSub (CT.context D G) H sigma ->
  @typ nat RankSorts n H (refl_case d D sigma) (eq_type d D sigma sigma).
Proof.
  intros HD HS; unfold refl_case, eq_type, BP.arr at 1.
  apply typ_λ with (ℓ := CT.ceiling rs); [eapply predicate_type_sort; eassumption |].
  apply typ_λ with (ℓ := d).
  - eapply bound_observe_typed; [exact HS | intro i; reflexivity].
  - constructor.
Qed.

Lemma predicate_replace d m rs (D : CT.telescope m rs) n p sigma (theta : Fin n -> Term nat p) :
  replace theta (predicate_type d D sigma) =
  predicate_type d D (fun i => replace theta (sigma i)).
Proof. unfold predicate_type, TR.base; rewrite replace_replace; reflexivity. Qed.

Theorem eq_type_replace d m rs (D : CT.telescope m rs) n p sigma tau (theta : Fin n -> Term nat p) :
  replace theta (eq_type d D sigma tau) =
  eq_type d D (fun i => replace theta (sigma i)) (fun i => replace theta (tau i)).
Proof.
  unfold eq_type; cbn [replace]; rewrite predicate_replace.
  rewrite TypedHOAS.TypedHOAS.arr_replace, !run_replace; cbn [replace transpose fin_match].
  f_equal; f_equal; apply run_ext; intro i; apply replace_lift_shift.
Qed.

Theorem refl_case_replace d m rs (D : CT.telescope m rs) n p sigma (theta : Fin n -> Term nat p) :
  replace theta (refl_case d D sigma) =
  refl_case d D (fun i => replace theta (sigma i)).
Proof.
  unfold refl_case; cbn [replace]; rewrite predicate_replace, run_replace.
  cbn [replace transpose fin_match]; f_equal; f_equal.
  apply run_ext; intro i; apply replace_lift_shift.
Qed.

Lemma observe_subst m rs (D : CT.telescope m rs) n sigma (P : Term nat n) :
  subst (TR.run D (shifted sigma) (var fzero)) P = TR.run D sigma P.
Proof.
  unfold subst; rewrite run_replace; cbn [replace fin_match].
  apply run_ext; intro i; unfold shifted, shift; rewrite replace_rename; apply replace_var.
Qed.

Theorem transport_function_typed d m rs (D : CT.telescope m rs) n (H : Ctx nat n) sigma tau e P :
  @typ nat RankSorts n H e (eq_type d D sigma tau) ->
  @typ nat RankSorts n H P (predicate_type d D sigma) ->
  @typ nat RankSorts n H (app e P) (BP.arr (TR.run D sigma P) (TR.run D tau P)).
Proof.
  intros He HP; unfold eq_type in He.
  pose proof (typ_app (predicate_type d D sigma) He HP) as HT.
  unfold subst in HT; rewrite TypedHOAS.TypedHOAS.arr_replace in HT.
  change (typ H (app e P) (BP.arr
    (subst (TR.run D (shifted sigma) (var fzero)) P)
    (subst (TR.run D (shifted tau) (var fzero)) P))) in HT.
  rewrite !observe_subst in HT; exact HT.
Qed.

Theorem transport_typed d m rs (D : CT.telescope m rs) n (H : Ctx nat n) sigma tau e P p :
  @typ nat RankSorts n H e (eq_type d D sigma tau) ->
  @typ nat RankSorts n H P (predicate_type d D sigma) ->
  @typ nat RankSorts n H p (TR.run D sigma P) ->
  @typ nat RankSorts n H (IE.transport e P p) (TR.run D tau P).
Proof.
  intros He HP Hp; unfold IE.transport; eapply BP.arr_apply;
    [eapply transport_function_typed; eassumption | exact Hp].
Qed.

Theorem transport_refl d m rs (D : CT.telescope m rs) n sigma (P p : Term nat n) :
  reduces_to nat n (IE.transport (refl_case d D sigma) P p) p.
Proof.
  unfold IE.transport, refl_case.
  eapply rtc_step; [apply step_app_left, step_beta |].
  cbn [subst replace]; apply rtc_in; apply step_beta.
Qed.

Theorem eq_type_normal d m rs (D : CT.telescope m rs) n sigma tau :
  normalb (@predicate_type d m rs D n sigma) = true ->
  (forall i, normalb (sigma i) = true) -> (forall i, normalb (tau i) = true) ->
  normalb (eq_type d D sigma tau) = true.
Proof.
  intros HP HS HT; unfold eq_type, BP.arr; cbn [normalb].
  rewrite HP; unfold shift at 1; rewrite TypedHOASFaithful.TypedHOASFaithful.normalb_rename.
  assert (H1 : normalb (TR.run D (shifted sigma) (var fzero)) = true).
  { apply TR.run_normal; [intro i; unfold shifted, shift; rewrite TypedHOASFaithful.TypedHOASFaithful.normalb_rename; apply HS | reflexivity | reflexivity]. }
  assert (H2 : normalb (TR.run D (shifted tau) (var fzero)) = true).
  { apply TR.run_normal; [intro i; unfold shifted, shift; rewrite TypedHOASFaithful.TypedHOASFaithful.normalb_rename; apply HT | reflexivity | reflexivity]. }
  rewrite H1, H2; reflexivity.
Qed.

Theorem refl_case_normal d m rs (D : CT.telescope m rs) n sigma :
  normalb (@predicate_type d m rs D n sigma) = true ->
  (forall i, normalb (sigma i) = true) -> normalb (refl_case d D sigma) = true.
Proof.
  intros HP HS; unfold refl_case; cbn [normalb]; rewrite HP.
  rewrite TR.run_normal; [reflexivity | | reflexivity | reflexivity].
  intro i; unfold shifted, shift; rewrite TypedHOASFaithful.TypedHOASFaithful.normalb_rename; apply HS.
Qed.

(** Reuse the SAME bound arguments with a different open base. This is
    explicit finite-variable reconstruction, not a cast of scoped syntax. *)
Fixpoint retarget (rs : list nat) : forall m p n,
    (Fin (CT.scope rs m) -> Term nat n) -> (Fin p -> Term nat n) ->
    Fin (CT.scope rs p) -> Term nat n :=
  match rs as qs return forall m p n,
    (Fin (CT.scope qs m) -> Term nat n) -> (Fin p -> Term nat n) ->
    Fin (CT.scope qs p) -> Term nat n with
  | [] => fun m p n sigma base => base
  | r :: tail => fun m p n sigma base =>
      retarget tail (S m) (S p) n sigma
        (fin_match (sigma (UT.base_ren tail fzero)) base)
  end.

Lemma retarget_base rs : forall m p n sigma base i,
  retarget rs m p n sigma base (UT.base_ren rs i) = base i.
Proof.
  induction rs; intros; cbn [retarget UT.base_ren]; [reflexivity |].
  rewrite IHrs; reflexivity.
Qed.

Lemma retarget_image rs : forall m p n sigma base (rho : Fin m -> Fin p),
  (forall i, base (rho i) = sigma (UT.base_ren rs i)) -> forall i,
  retarget rs m p n sigma base (CT.lift_ren rs rho i) = sigma i.
Proof.
  induction rs; intros m p n sigma base rho H i; cbn [retarget CT.lift_ren].
  - apply H.
  - apply IHrs; intro j; dependent elimination j; cbn [weak fin_match].
    + reflexivity.
    + apply H.
Qed.

Lemma run_retarget m rs (D : CT.telescope m rs) : forall p (E : CT.telescope p rs) n sigma base q,
  @TR.run p rs E n (retarget rs m p n sigma base) q = TR.run D sigma q.
Proof.
  induction D; intros p E k sigma base q; dependent elimination E; cbn [TR.run retarget].
  - reflexivity.
  - rewrite retarget_base; apply IHD.
Qed.

Lemma lift_ren_base rs : forall m n (rho : Fin m -> Fin n) i,
  CT.lift_ren rs rho (UT.base_ren rs i) = UT.base_ren rs (rho i).
Proof. induction rs; intros; cbn [CT.lift_ren UT.base_ren]; [reflexivity | rewrite IHrs; reflexivity]. Qed.

Definition fixed_base {n rs} (sigma : Fin (CT.scope rs n) -> Term nat n) :=
  forall i, sigma (UT.base_ren rs i) = var i.
Definition base_preserving {n rs ss}
    (theta : Fin (CT.scope ss n) -> Term nat (CT.scope rs n)) :=
  forall i, theta (UT.base_ren ss i) = var (UT.base_ren rs i).
Definition compose {m n p} (sigma : Fin n -> Term nat p) (theta : Fin m -> Term nat n) :=
  fun i => replace sigma (theta i).

Lemma predicate_fixed d n rs (D : CT.telescope n rs) sigma :
  fixed_base sigma -> predicate_type d D sigma = CT.close_type D (𝓤 d).
Proof.
  intro HS; unfold predicate_type; etransitivity; [apply replace_ext; exact HS | apply replace_var].
Qed.

Lemma compose_typed m n p (G : Ctx nat m) (H : Ctx nat n) (K : Ctx nat p) sigma theta :
  TypedSub G H theta -> TypedSub H K sigma -> TypedSub G K (compose sigma theta).
Proof.
  intros HT HS i; unfold compose; rewrite <- replace_replace; eapply typing_replace; [apply HT | exact HS].
Qed.

Lemma compose_fixed n rs ss sigma theta :
  @fixed_base n rs sigma -> @base_preserving n rs ss theta ->
  @fixed_base n ss (compose sigma theta).
Proof. intros HS HT i; unfold compose; rewrite HT; cbn [replace]; apply HS. Qed.

Definition motive (d : nat) {n rs ss} (D : CT.telescope n rs) (E : CT.telescope n ss)
    (theta : Fin (CT.scope ss n) -> Term nat (CT.scope rs n)) : Term nat (S n) :=
  CT.close_term (CT.rename_telescope D (S n) fsucc)
    (TR.run E (fun i => rename (CT.lift_ren rs fsucc) (theta i))
      (var (UT.base_ren rs fzero))).
Definition map_case d {n rs ss} (D : CT.telescope n rs) (E : CT.telescope n ss)
    (theta : Fin (CT.scope ss n) -> Term nat (CT.scope rs n)) (e : Term nat n) :=
  lam (CT.close_type E (𝓤 d)) (app (shift e) (motive d D E theta)).

Lemma motive_typed d n rs ss (D : CT.telescope n rs) (E : CT.telescope n ss)
    (G : Ctx nat n) theta :
  CT.formed G D ->
  TypedSub (CT.context E G) (CT.context D G) theta -> base_preserving theta ->
  @typ nat RankSorts (S n) (G & CT.close_type E (𝓤 d)) (motive d D E theta)
    (shift (CT.close_type D (𝓤 d))).
Proof.
  intros HD HT HB; unfold motive.
  unfold shift; rewrite CT.close_type_rename; cbn [rename].
  apply CT.close_typing.
  - apply CT.formed_rename with (G := G); [exact HD | apply typed_ren_shift].
  - eapply TR.run_typing with (G := G) (T := 𝓤 d).
    + intro i; rewrite <- rename_replace; apply typing_rename with (G := CT.context D G).
      * apply CT.context_ren, typed_ren_shift.
      * apply HT.
    + assert (HE : replace
        (TR.base (fun i => rename (CT.lift_ren rs fsucc) (theta i))) (CT.close_type E (𝓤 d)) =
        rename (UT.base_ren rs) (shift (CT.close_type E (𝓤 d)))).
      { unfold TR.base, shift; rewrite rename_comp.
        rewrite <- replace_as_rename; apply replace_ext; intro i.
        rewrite HB; cbn [rename]; rewrite lift_ren_base; reflexivity. }
      rewrite HE.
      change (typ (CT.context (CT.rename_telescope D (S n) fsucc) (G & CT.close_type E (𝓤 d)))
        (var (UT.base_ren rs fzero))
        (rename (UT.base_ren rs) ((G & CT.close_type E (𝓤 d)) !! fzero))).
      rewrite <- (TR.index_base (S n) rs (CT.rename_telescope D (S n) fsucc)); constructor.
Qed.

Definition lifted_spine {m rs n} (sigma : Fin (CT.scope rs m) -> Term nat n) :=
  retarget rs m (S m) (S n) (shifted sigma) (transpose (TR.base sigma)).

Lemma lifted_image m rs n (sigma : Fin (CT.scope rs m) -> Term nat n) i :
  lifted_spine sigma (CT.lift_ren rs fsucc i) = shift (sigma i).
Proof. apply retarget_image; intro j; reflexivity. Qed.

Lemma lifted_fixed n rs (sigma : Fin (CT.scope rs n) -> Term nat n) :
  fixed_base sigma -> fixed_base (lifted_spine sigma).
Proof.
  intros HS i; unfold lifted_spine; rewrite retarget_base.
  dependent elimination i; cbn [transpose fin_match]; [reflexivity |].
  unfold TR.base; rewrite HS; reflexivity.
Qed.

Lemma motive_recovers d n rs ss (D : CT.telescope n rs) (E : CT.telescope n ss)
    theta sigma : fixed_base sigma ->
  reduces_to nat (S n) (TR.run D (shifted sigma) (motive d D E theta))
    (TR.run E (shifted (compose sigma theta)) (var fzero)).
Proof.
  intro HS; unfold motive.
  rewrite <- (run_retarget n rs D (S n) (CT.rename_telescope D (S n) fsucc)
    (S n) (shifted sigma) (transpose (TR.base sigma))).
  change (reduces_to nat (S n)
    (TR.run (CT.rename_telescope D (S n) fsucc) (lifted_spine sigma)
      (CT.close_term (CT.rename_telescope D (S n) fsucc)
        (TR.run E (fun i => rename (CT.lift_ren rs fsucc) (theta i))
          (var (UT.base_ren rs fzero)))))
    (TR.run E (shifted (compose sigma theta)) (var fzero))).
  assert (HF : forall t : Term nat (S n), replace (TR.base (lifted_spine sigma)) t = t).
  { intro t; etransitivity; [apply replace_ext; apply lifted_fixed; exact HS | apply replace_var]. }
  rewrite <- (HF (CT.close_term (CT.rename_telescope D (S n) fsucc)
    (TR.run E (fun i => rename (CT.lift_ren rs fsucc) (theta i))
      (var (UT.base_ren rs fzero))))) at 1.
  eapply rtc_trans; [apply TR.run_closure |].
  rewrite run_replace; cbn [replace].
  change (reduces_to nat (S n)
    (TR.run E (fun i => replace (lifted_spine sigma) (rename (CT.lift_ren rs fsucc) (theta i)))
      (lifted_spine sigma (UT.base_ren rs fzero)))
    (TR.run E (shifted (compose sigma theta)) (var fzero))).
  unfold lifted_spine at 2; rewrite retarget_base; cbn [transpose fin_match].
  assert (HE : forall t, replace (lifted_spine sigma) (rename (CT.lift_ren rs fsucc) t) =
    shift (replace sigma t)).
  { intro t; unfold shift; rewrite replace_rename, rename_replace; apply replace_ext; apply lifted_image. }
  assert (HR : TR.run E
      (fun i => replace (lifted_spine sigma) (rename (CT.lift_ren rs fsucc) (theta i))) (var fzero) =
      TR.run E (shifted (compose sigma theta)) (var fzero)).
  { apply run_ext; intro i; apply HE. }
  rewrite HR; reflexivity.
Qed.

Lemma eq_type_ext d m rs (D : CT.telescope m rs) n sigma tau sigma' tau' :
  (forall i, sigma i = sigma' i) -> (forall i, tau i = tau' i) ->
  @eq_type d m rs D n sigma tau = eq_type d D sigma' tau'.
Proof.
  intros HS HT; unfold eq_type, predicate_type; f_equal.
  - apply replace_ext; intro i; apply HS.
  - f_equal; apply run_ext; intro i; unfold shifted; now rewrite HS || rewrite HT.
Qed.

Lemma eq_type_shift d m rs (D : CT.telescope m rs) n sigma tau :
  shift (@eq_type d m rs D n sigma tau) = eq_type d D (shifted sigma) (shifted tau).
Proof.
  pose proof (eq_type_replace d m rs D n (S n) sigma tau (fun i => var (fsucc i))) as H.
  rewrite replace_as_rename in H; etransitivity; [exact H |].
  apply eq_type_ext; intro i; apply replace_as_rename.
Qed.

Theorem map_case_typed d n rs ss (D : CT.telescope n rs) (E : CT.telescope n ss)
    (G : Ctx nat n) theta sigma tau e :
  CT.formed G D -> CT.formed G E ->
  TypedSub (CT.context E G) (CT.context D G) theta -> base_preserving theta ->
  TypedSub (CT.context D G) G sigma -> fixed_base sigma ->
  TypedSub (CT.context D G) G tau -> fixed_base tau ->
  @typ nat RankSorts n G e (eq_type d D sigma tau) ->
  @typ nat RankSorts n G (map_case d D E theta e)
    (eq_type d E (compose sigma theta) (compose tau theta)).
Proof.
  intros HD HE Htheta HB HS HSF HT HTF He.
  assert (HS' : TypedSub (CT.context E G) G (compose sigma theta)) by (eapply compose_typed; eassumption).
  assert (HT' : TypedSub (CT.context E G) G (compose tau theta)) by (eapply compose_typed; eassumption).
  assert (HSF' : fixed_base (compose sigma theta)) by (apply compose_fixed; assumption).
  assert (HTF' : fixed_base (compose tau theta)) by (apply compose_fixed; assumption).
  unfold map_case, eq_type; rewrite predicate_fixed by exact HSF'.
  apply typ_λ with (ℓ := CT.ceiling ss).
  - apply CT.close_type_sort; [exact HE | constructor; reflexivity].
  - set (GP := G & CT.close_type E (𝓤 d)).
    assert (He' : typ GP (shift e) (eq_type d D (shifted sigma) (shifted tau))).
    { rewrite <- eq_type_shift; apply weakening; exact He. }
    assert (HM : typ GP (motive d D E theta) (predicate_type d D (shifted sigma))).
    { rewrite predicate_shift, predicate_fixed by exact HSF.
      apply motive_typed with (G := G); assumption. }
    pose proof (transport_function_typed d n rs D (S n) GP (shifted sigma) (shifted tau)
      (shift e) (motive d D E theta) He' HM) as HA.
    assert (HU : typ GP (TR.run E (shifted (compose sigma theta)) (var fzero)) (𝓤 d)).
    { pose proof (bound_observe_typed d n ss E n G G (compose sigma theta) (compose sigma theta)
        HS' (fun i => eq_refl)) as H.
      rewrite predicate_fixed in H by exact HSF'; exact H. }
    assert (HV : typ GP (TR.run E (shifted (compose tau theta)) (var fzero)) (𝓤 d)).
    { pose proof (bound_observe_typed d n ss E n G G (compose tau theta) (compose tau theta)
        HT' (fun i => eq_refl)) as H.
      rewrite predicate_fixed in H by exact HTF'; exact H. }
    eapply typ_conv with (T := BP.arr (TR.run D (shifted sigma) (motive d D E theta))
      (TR.run D (shifted tau) (motive d D E theta))) (ℓ := S d).
    + exact HA.
    + replace (S d) with (Nat.max (S d) d) by lia; apply BP.arr_sort; assumption.
    + apply def_equiv_prop; eexists; split; [apply BP.arr_reduces; apply motive_recovers; eassumption | reflexivity].
Qed.

Lemma refl_case_ext d m rs (D : CT.telescope m rs) n sigma tau :
  (forall i, sigma i = tau i) -> @refl_case d m rs D n sigma = refl_case d D tau.
Proof.
  intro H; unfold refl_case, predicate_type; f_equal.
  - apply replace_ext; intro i; apply H.
  - f_equal; apply run_ext; intro i; unfold shifted; now rewrite H.
Qed.

Lemma refl_case_shift d m rs (D : CT.telescope m rs) n sigma :
  shift (@refl_case d m rs D n sigma) = refl_case d D (shifted sigma).
Proof.
  pose proof (refl_case_replace d m rs D n (S n) sigma (fun i => var (fsucc i))) as H.
  rewrite replace_as_rename in H; etransitivity; [exact H |].
  apply refl_case_ext; intro i; apply replace_as_rename.
Qed.

Theorem map_case_refl d n rs ss (D : CT.telescope n rs) (E : CT.telescope n ss) theta sigma :
  fixed_base sigma -> base_preserving theta ->
  reduces_to nat n (map_case d D E theta (refl_case d D sigma))
    (refl_case d E (compose sigma theta)).
Proof.
  intros HS HT; unfold map_case; rewrite refl_case_shift.
  unfold refl_case at 2; rewrite predicate_fixed by (apply compose_fixed; assumption).
  apply (@λ_cong_r nat (reduces_to nat) _ n).
  unfold refl_case; eapply rtc_step; [apply step_beta |].
  change (reduces_to nat (S n)
    (lam (subst (TR.run D (shifted (shifted sigma)) (var fzero)) (motive d D E theta)) (var fzero))
    (lam (TR.run E (shifted (compose sigma theta)) (var fzero)) (var fzero))).
  rewrite observe_subst.
  apply (@λ_cong_par nat (reduces_to nat) _ _ (S n)); [apply motive_recovers; exact HS | reflexivity].
Qed.

Lemma motive_normal d n rs ss (D : CT.telescope n rs) (E : CT.telescope n ss) theta :
  CT.normal_annotations D = true ->
  (forall i, normalb (theta i) = true) -> normalb (motive d D E theta) = true.
Proof.
  intros HD HT; unfold motive; rewrite CT.close_term_normal, UT.annotations_rename, HD.
  apply TR.run_normal; [| reflexivity | reflexivity].
  intro i; rewrite UT.normalb_rename; apply HT.
Qed.

Theorem map_case_normal d n rs ss (D : CT.telescope n rs) (E : CT.telescope n ss) theta e :
  CT.normal_annotations D = true -> CT.normal_annotations E = true ->
  (forall i, normalb (theta i) = true) -> normalb e = true -> isLambda e = false ->
  normalb (map_case d D E theta e) = true.
Proof.
  intros HD HE HT He Hne; unfold map_case; cbn [normalb].
  rewrite CT.close_type_normal, HE; unfold shift.
  rewrite UT.normalb_rename, UT.isLambda_rename, He, Hne.
  rewrite motive_normal by assumption; reflexivity.
Qed.

Theorem rank_bounded rs k d : Forall (fun r => r <= k) rs -> d <= k -> rank rs d <= k+2.
Proof.
  intros Hr Hd; pose proof (CT.rank_bounded rs k 0 Hr).
  unfold rank, CT.ceiling in *; lia.
Qed.

Print Assumptions eq_type_sort.
Print Assumptions refl_case_typed.
Print Assumptions eq_type_replace.
Print Assumptions refl_case_replace.
Print Assumptions transport_function_typed.
Print Assumptions transport_typed.
Print Assumptions transport_refl.
Print Assumptions eq_type_normal.
Print Assumptions refl_case_normal.
Print Assumptions motive_typed.
Print Assumptions motive_recovers.
Print Assumptions map_case_typed.
Print Assumptions map_case_refl.
Print Assumptions map_case_normal.
Print Assumptions rank_bounded.
End TelescopeEquality.
