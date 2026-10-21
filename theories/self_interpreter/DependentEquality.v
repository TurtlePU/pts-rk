From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation
  Ranks DefEq Reduction AbstractRewriting Congruence.
From PTSrk.NormalizationComplexity Require Import Greedy Morphisms.
From PTSrk.SelfInterpreter Require Import BrownPalsberg DependentPHOAS
  IndexedEquality IndexedCoherence TypedHOASFaithful.
Import Context.

(** Synchronized equality of a dependent index and a value in its fiber.
    All evidence below is ORIGINAL object syntax. This is not equality after
    an arbitrarily chosen transport, a proof-dependent eliminator, or function
    extensionality. In particular no whole-source coherence is assumed. *)
Module DependentEquality.
Module BP := BrownPalsberg.BrownPalsberg.
Module DP := DependentPHOAS.DependentPHOAS.
Module IE := IndexedEquality.IndexedEquality.
Module IC := IndexedCoherence.IndexedCoherence.
Module TF := TypedHOASFaithful.TypedHOASFaithful.

Definition predicate_type d {n} (A B : Term nat n) :=
  Π A (BP.arr (app (shift B) (var fzero)) (𝓤 d)).
Definition observe {n} (P u y : Term nat n) := app (app P u) y.
Definition graph_eq d {n} (A B u y v z : Term nat n) :=
  Π (predicate_type d A B)
    (BP.arr (observe (var fzero) (shift u) (shift y))
      (observe (var fzero) (shift v) (shift z))).
Definition graph_refl d {n} (A B u y : Term nat n) :=
  lam (predicate_type d A B)
    (lam (observe (var fzero) (shift u) (shift y)) (var fzero)).
Definition rank a b d := Nat.max (Nat.max (a+2) (b+2)) (d+1).

Lemma product_shift n (A B : Term nat n) :
  shift (DP.plain_product A B) = DP.plain_product (shift A) (shift B).
Proof. unfold DP.plain_product; syntax_simp. Qed.

Lemma predicate_type_rename d m n (rho : Fin m -> Fin n) A B :
  rename rho (predicate_type d A B) = predicate_type d (rename rho A) (rename rho B).
Proof. unfold predicate_type, BP.arr; syntax_simp. Qed.
Lemma predicate_type_shift d n (A B : Term nat n) :
  shift (predicate_type d A B) = predicate_type d (shift A) (shift B).
Proof. apply predicate_type_rename. Qed.
Lemma predicate_type_replace d m n (sigma : Fin m -> Term nat n) A B :
  replace sigma (predicate_type d A B) = predicate_type d (replace sigma A) (replace sigma B).
Proof. unfold predicate_type, BP.arr; syntax_simp. Qed.
Lemma graph_eq_replace d m n (sigma : Fin m -> Term nat n) A B u y v z :
  replace sigma (graph_eq d A B u y v z) =
    graph_eq d (replace sigma A) (replace sigma B) (replace sigma u)
      (replace sigma y) (replace sigma v) (replace sigma z).
Proof. unfold graph_eq, predicate_type, observe, BP.arr; syntax_simp. Qed.
Lemma graph_refl_replace d m n (sigma : Fin m -> Term nat n) A B u y :
  replace sigma (graph_refl d A B u y) =
    graph_refl d (replace sigma A) (replace sigma B) (replace sigma u) (replace sigma y).
Proof. unfold graph_refl, predicate_type, observe, BP.arr; syntax_simp. Qed.

Lemma dependent_apply_typed n (G : Ctx nat n) A B f u :
  @typ nat RankSorts n G f (DP.plain_product A B) ->
  @typ nat RankSorts n G u A ->
  @typ nat RankSorts n G (app f u) (app B u).
Proof.
  intros Hf Hu; unfold DP.plain_product in Hf.
  pose proof (typ_app A Hf Hu) as H.
  replace (app B u) with (subst (app (shift B) (var fzero)) u) by syntax_simp.
  exact H.
Qed.

Lemma predicate_type_sort a b d n (G : Ctx nat n) A B :
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G B (BP.arr A (𝓤 b)) ->
  @typ nat RankSorts n G (predicate_type d A B) (𝓤 (Nat.max (S a) (S b))).
Proof.
  intros HA HB; unfold predicate_type.
  eapply typ_Π with (ℓₜ := a) (ℓᵤ := S b); [exact HA | | reflexivity].
  replace (S b) with (Nat.max (S b) 0) by lia.
  apply BP.arr_sort; [| constructor; reflexivity].
  eapply BP.arr_apply with (A := shift A).
  - change (typ (G & A) (shift B) (BP.arr (shift A) (shift (𝓤 b)))).
    rewrite <- BP.arr_shift; apply weakening; exact HB.
  - change (typ (G & A) (var fzero) ((G & A) !! fzero)); constructor.
Qed.

Lemma predicate_apply_typed d n (G : Ctx nat n) A B P u y :
  @typ nat RankSorts n G P (predicate_type d A B) ->
  @typ nat RankSorts n G u A ->
  @typ nat RankSorts n G y (app B u) ->
  @typ nat RankSorts n G (observe P u y) (𝓤 d).
Proof.
  intros HP Hu Hy; unfold predicate_type in HP.
  pose proof (typ_app A HP Hu) as H.
  assert (HE : subst (BP.arr (app (shift B) (var fzero)) (𝓤 d)) u =
    BP.arr (app B u) (𝓤 d)).
  { unfold BP.arr; syntax_simp. }
  rewrite HE in H; unfold observe; eapply BP.arr_apply; eassumption.
Qed.

Lemma bound_predicate_application d n (G : Ctx nat n) A B u y :
  @typ nat RankSorts n G u A -> @typ nat RankSorts n G y (app B u) ->
  @typ nat RankSorts (S n) (G & predicate_type d A B)
    (observe (var fzero) (shift u) (shift y)) (𝓤 d).
Proof.
  intros Hu Hy; eapply predicate_apply_typed with (A := shift A) (B := shift B).
  - rewrite <- predicate_type_shift.
    change (typ (G & predicate_type d A B) (var fzero)
      ((G & predicate_type d A B) !! fzero)); constructor.
  - apply weakening; exact Hu.
  - change (typ (G & predicate_type d A B) (shift y) (shift (app B u))).
    apply weakening; exact Hy.
Qed.

Theorem graph_eq_sort a b d n (G : Ctx nat n) A B u y v z :
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G B (BP.arr A (𝓤 b)) ->
  @typ nat RankSorts n G u A -> @typ nat RankSorts n G y (app B u) ->
  @typ nat RankSorts n G v A -> @typ nat RankSorts n G z (app B v) ->
  @typ nat RankSorts n G (graph_eq d A B u y v z) (𝓤 (rank a b d)).
Proof.
  intros HA HB Hu Hy Hv Hz; unfold graph_eq.
  eapply typ_Π with (ℓₜ := Nat.max (S a) (S b)) (ℓᵤ := S d).
  - eapply predicate_type_sort; eassumption.
  - replace (S d) with (Nat.max (S d) d) by lia.
    apply BP.arr_sort; eapply bound_predicate_application; eassumption.
  - unfold rank; change (Nat.max (Nat.max (a+2) (b+2)) (d+1) =
      Nat.max (S (Nat.max (S a) (S b))) (S d)); lia.
Qed.

Theorem graph_refl_typed a b d n (G : Ctx nat n) A B u y :
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G B (BP.arr A (𝓤 b)) ->
  @typ nat RankSorts n G u A -> @typ nat RankSorts n G y (app B u) ->
  @typ nat RankSorts n G (graph_refl d A B u y) (graph_eq d A B u y u y).
Proof.
  intros HA HB Hu Hy; unfold graph_refl, graph_eq, BP.arr at 1.
  apply typ_λ with (ℓ := Nat.max (S a) (S b)); [eapply predicate_type_sort; eassumption |].
  apply typ_λ with (ℓ := d); [eapply bound_predicate_application; eassumption |].
  change (typ ((G & predicate_type d A B) & observe (var fzero) (shift u) (shift y))
    (var fzero) (((G & predicate_type d A B) & observe (var fzero) (shift u) (shift y)) !! fzero)).
  constructor.
Qed.

Theorem graph_transport_typed d n (G : Ctx nat n) A B u y v z e P p :
  @typ nat RankSorts n G e (graph_eq d A B u y v z) ->
  @typ nat RankSorts n G P (predicate_type d A B) ->
  @typ nat RankSorts n G p (observe P u y) ->
  @typ nat RankSorts n G (IE.transport e P p) (observe P v z).
Proof.
  intros He HP Hp; unfold graph_eq in He.
  pose proof (typ_app (predicate_type d A B) He HP) as H.
  assert (HE : subst (BP.arr (observe (var fzero) (shift u) (shift y))
    (observe (var fzero) (shift v) (shift z))) P = BP.arr (observe P u y) (observe P v z)).
  { unfold subst; rewrite TypedHOAS.TypedHOAS.arr_replace; unfold observe; syntax_simp. }
  rewrite HE in H; unfold IE.transport; eapply BP.arr_apply; eassumption.
Qed.

Theorem graph_transport_refl d n (A B u y P p : Term nat n) :
  reduces_to nat n (IE.transport (graph_refl d A B u y) P p) p.
Proof.
  unfold IE.transport, graph_refl; eapply rtc_step; [apply step_app_left, step_beta |].
  unfold observe; syntax_simp; apply rtc_in, step_beta.
Qed.

Definition graph_motive {n} (A f P : Term nat n) :=
  lam A (observe (shift P) (var fzero) (app (shift f) (var fzero))).
Definition dependent_congruence d {n} (A B f e : Term nat n) :=
  lam (predicate_type d A B)
    (app (shift e) (graph_motive (shift A) (shift f) (var fzero))).

Lemma graph_motive_typed a d n (G : Ctx nat n) A B f P :
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G f (DP.plain_product A B) ->
  @typ nat RankSorts n G P (predicate_type d A B) ->
  @typ nat RankSorts n G (graph_motive A f P) (IE.motive_type d A).
Proof.
  intros HA Hf HP; unfold graph_motive, IE.motive_type, BP.arr at 1.
  apply typ_λ with (ℓ := a); [exact HA |].
  eapply predicate_apply_typed with (A := shift A) (B := shift B).
  - rewrite <- predicate_type_shift; apply weakening; exact HP.
  - change (typ (G & A) (var fzero) ((G & A) !! fzero)); constructor.
  - eapply dependent_apply_typed with (A := shift A).
    + rewrite <- product_shift; apply weakening; exact Hf.
    + change (typ (G & A) (var fzero) ((G & A) !! fzero)); constructor.
Qed.

Lemma graph_motive_beta n (A f P u : Term nat n) :
  step nat n (app (graph_motive A f P) u) (observe P u (app f u)).
Proof.
  unfold graph_motive, observe. replace (app (app P u) (app f u)) with
    (subst (app (app (shift P) (var fzero)) (app (shift f) (var fzero))) u)
    by syntax_simp. apply step_beta.
Qed.

(** Unlike an equality after a prescribed cast, this theorem needs only the
    SAME predicate level d. It tracks the dependent index and value together. *)
Theorem dependent_congruence_typed a b d n (G : Ctx nat n) A B f u v e :
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G B (BP.arr A (𝓤 b)) ->
  @typ nat RankSorts n G f (DP.plain_product A B) ->
  @typ nat RankSorts n G u A -> @typ nat RankSorts n G v A ->
  @typ nat RankSorts n G e (IE.eq_type d A u v) ->
  @typ nat RankSorts n G (dependent_congruence d A B f e)
    (graph_eq d A B u (app f u) v (app f v)).
Proof.
  intros HA HB Hf Hu Hv He.
  set (GP := G & predicate_type d A B).
  set (M := graph_motive (shift A) (shift f) (var fzero)).
  assert (HE : typ GP (shift e) (IE.eq_type d (shift A) (shift u) (shift v))).
  { rewrite <- IC.eq_type_shift; apply weakening; exact He. }
  assert (HM : typ GP M (IE.motive_type d (shift A))).
  { unfold M; eapply graph_motive_typed with (a := a) (B := shift B).
    - change (typ GP (shift A) (shift (𝓤 a))); apply weakening; exact HA.
    - rewrite <- product_shift; apply weakening; exact Hf.
    - rewrite <- predicate_type_shift; change (typ GP (var fzero) (GP !! fzero)); constructor. }
  unfold dependent_congruence, graph_eq.
  apply typ_λ with (ℓ := Nat.max (S a) (S b)); [eapply predicate_type_sort; eassumption |].
  change (typ GP (app (shift e) M)
    (BP.arr (observe (var fzero) (shift u) (shift (app f u)))
      (observe (var fzero) (shift v) (shift (app f v))))).
  eapply typ_conv with (T := BP.arr (app M (shift u)) (app M (shift v))) (ℓ := S d).
  - eapply IE.eq_specialize; eassumption.
  - replace (S d) with (Nat.max (S d) d) by lia.
    apply BP.arr_sort; eapply bound_predicate_application; try eassumption;
      eapply dependent_apply_typed; eassumption.
  - apply def_equiv_prop; exists (BP.arr
      (observe (var fzero) (shift u) (shift (app f u)))
      (observe (var fzero) (shift v) (shift (app f v)))); split; [| reflexivity].
    apply BP.arr_reduces; apply rtc_in, graph_motive_beta.
Qed.

Theorem dependent_congruence_replace d m n (sigma : Fin m -> Term nat n) A B f e :
  replace sigma (dependent_congruence d A B f e) =
    dependent_congruence d (replace sigma A) (replace sigma B) (replace sigma f) (replace sigma e).
Proof. unfold dependent_congruence, predicate_type, graph_motive, observe, BP.arr; syntax_simp. Qed.

Theorem dependent_congruence_applies d n (A B f e P z : Term nat n) :
  reduces_to nat n (IE.transport (dependent_congruence d A B f e) P z)
    (IE.transport e (graph_motive A f P) z).
Proof.
  unfold dependent_congruence, IE.transport.
  eapply rtc_step; [apply step_app_left, step_beta |].
  unfold graph_motive, observe; syntax_simp.
  cbn [transpose fin_match]; rewrite BP.replace_fsucc; reflexivity.
Qed.

Theorem dependent_congruence_reflexivity d n (A B f u : Term nat n) :
  reduces_to nat n (dependent_congruence d A B f (IE.refl_case d A u))
    (graph_refl d A B u (app f u)).
Proof.
  unfold dependent_congruence; rewrite IC.refl_case_shift.
  change (reduces_to nat n
    (lam (predicate_type d A B)
      (app (IE.refl_case d (shift A) (shift u))
        (graph_motive (shift A) (shift f) (var fzero))))
    (lam (predicate_type d A B)
      (lam (observe (var fzero) (shift u) (shift (app f u))) (var fzero)))).
  apply (@λ_cong_par nat (reduces_to nat) _ _ n); [reflexivity |].
  eapply rtc_trans; [apply IC.refl_function_specializes |].
  apply (@λ_cong_par nat (reduces_to nat) _ _ (S n));
    [apply rtc_in, graph_motive_beta | reflexivity].
Qed.

(** Ordinary equality inside one fixed fiber embeds into synchronized graph
    equality. In particular the actual finite beta-law witnesses can enter
    this interface without a new coherence-field assumption. *)
Definition fiber_congruence d {n} (A B u e : Term nat n) :=
  lam (predicate_type d A B) (app (shift e) (app (var fzero) (shift u))).

Lemma predicate_specialize_typed d n (G : Ctx nat n) A B P u :
  @typ nat RankSorts n G P (predicate_type d A B) ->
  @typ nat RankSorts n G u A ->
  @typ nat RankSorts n G (app P u) (IE.motive_type d (app B u)).
Proof.
  intros HP Hu; unfold predicate_type in HP.
  pose proof (typ_app A HP Hu) as H.
  replace (IE.motive_type d (app B u)) with
    (subst (BP.arr (app (shift B) (var fzero)) (𝓤 d)) u).
  - exact H.
  - unfold IE.motive_type, BP.arr; syntax_simp.
Qed.

Theorem fiber_congruence_typed a b d n (G : Ctx nat n) A B u y z e :
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G B (BP.arr A (𝓤 b)) ->
  @typ nat RankSorts n G u A ->
  @typ nat RankSorts n G e (IE.eq_type d (app B u) y z) ->
  @typ nat RankSorts n G (fiber_congruence d A B u e)
    (graph_eq d A B u y u z).
Proof.
  intros HA HB Hu He; set (GP := G & predicate_type d A B).
  assert (HE : typ GP (shift e)
    (IE.eq_type d (shift (app B u)) (shift y) (shift z))).
  { rewrite <- IC.eq_type_shift; apply weakening; exact He. }
  assert (HM : typ GP (app (var fzero) (shift u))
    (IE.motive_type d (shift (app B u)))).
  { change (typ GP (app (var fzero) (shift u))
      (IE.motive_type d (app (shift B) (shift u)))).
    eapply predicate_specialize_typed with (A := shift A).
    - rewrite <- predicate_type_shift; change (typ GP (var fzero) (GP !! fzero)); constructor.
    - apply weakening; exact Hu. }
  unfold fiber_congruence, graph_eq.
  apply typ_λ with (ℓ := Nat.max (S a) (S b)); [eapply predicate_type_sort; eassumption |].
  change (typ GP (app (shift e) (app (var fzero) (shift u)))
    (BP.arr (observe (var fzero) (shift u) (shift y))
      (observe (var fzero) (shift u) (shift z)))).
  eapply IE.eq_specialize; eassumption.
Qed.

Theorem fiber_congruence_replace d m n (sigma : Fin m -> Term nat n) A B u e :
  replace sigma (fiber_congruence d A B u e) =
    fiber_congruence d (replace sigma A) (replace sigma B) (replace sigma u) (replace sigma e).
Proof. unfold fiber_congruence, predicate_type, BP.arr; syntax_simp. Qed.

Theorem fiber_congruence_applies d n (A B u e P p : Term nat n) :
  reduces_to nat n (IE.transport (fiber_congruence d A B u e) P p)
    (IE.transport e (app P u) p).
Proof.
  unfold fiber_congruence, IE.transport.
  eapply rtc_step; [apply step_app_left, step_beta |]. syntax_simp; reflexivity.
Qed.

(** Raw beta computation permits any reflexivity annotation Y. Original
    typing above still requires exactly the actual fiber B u. *)
Theorem fiber_congruence_reflexivity d n (A B u Y y : Term nat n) :
  reduces_to nat n (fiber_congruence d A B u (IE.refl_case d Y y))
    (graph_refl d A B u y).
Proof.
  unfold fiber_congruence; rewrite IC.refl_case_shift.
  change (reduces_to nat n
    (lam (predicate_type d A B)
      (app (IE.refl_case d (shift Y) (shift y)) (app (var fzero) (shift u))))
    (lam (predicate_type d A B)
      (lam (observe (var fzero) (shift u) (shift y)) (var fzero)))).
  apply (@λ_cong_par nat (reduces_to nat) _ _ n); [reflexivity |].
  apply IC.refl_function_specializes.
Qed.

(** A lambda-valued family introduces a redex in predicate_type; normality
    therefore explicitly requires a neutral family (and, for congruence,
    neutral function/equality inputs). No normalization oracle is inserted. *)
Lemma predicate_type_normal d n (A B : Term nat n) :
  normalb A = true -> normalb B = true -> isLambda B = false ->
  normalb (predicate_type d A B) = true.
Proof.
  intros HA HB HBl; unfold predicate_type, BP.arr, shift.
  repeat progress (cbn [normalb isLambda]; rewrite ?TF.normalb_rename, ?TF.isLambda_rename).
  now rewrite HA, HB, HBl.
Qed.

Theorem graph_eq_normal d n (A B u y v z : Term nat n) :
  normalb A = true -> normalb B = true -> isLambda B = false ->
  normalb u = true -> normalb y = true -> normalb v = true -> normalb z = true ->
  normalb (graph_eq d A B u y v z) = true.
Proof.
  intros HA HB NB Hu Hy Hv Hz; unfold graph_eq, predicate_type, BP.arr, observe, shift.
  repeat progress (cbn [normalb isLambda]; rewrite ?TF.normalb_rename, ?TF.isLambda_rename).
  now rewrite HA, HB, NB, Hu, Hy, Hv, Hz.
Qed.

Theorem graph_refl_normal d n (A B u y : Term nat n) :
  normalb A = true -> normalb B = true -> isLambda B = false ->
  normalb u = true -> normalb y = true -> normalb (graph_refl d A B u y) = true.
Proof.
  intros HA HB NB Hu Hy; unfold graph_refl, predicate_type, BP.arr, observe, shift.
  repeat progress (cbn [normalb isLambda]; rewrite ?TF.normalb_rename, ?TF.isLambda_rename).
  now rewrite HA, HB, NB, Hu, Hy.
Qed.

Theorem dependent_congruence_normal d n (A B f e : Term nat n) :
  normalb A = true -> normalb B = true -> isLambda B = false ->
  normalb f = true -> isLambda f = false ->
  normalb e = true -> isLambda e = false ->
  normalb (dependent_congruence d A B f e) = true.
Proof.
  intros HA HB NB Hf Nf He Ne.
  unfold dependent_congruence, predicate_type, graph_motive, BP.arr, observe, shift.
  repeat progress (cbn [normalb isLambda]; rewrite ?TF.normalb_rename, ?TF.isLambda_rename).
  now rewrite HA, HB, NB, Hf, Nf, He, Ne.
Qed.

Theorem fiber_congruence_normal d n (A B u e : Term nat n) :
  normalb A = true -> normalb B = true -> isLambda B = false ->
  normalb u = true -> normalb e = true -> isLambda e = false ->
  normalb (fiber_congruence d A B u e) = true.
Proof.
  intros HA HB NB Hu He Ne; unfold fiber_congruence, predicate_type, BP.arr, shift.
  repeat progress (cbn [normalb isLambda]; rewrite ?TF.normalb_rename, ?TF.isLambda_rename).
  now rewrite HA, HB, NB, Hu, He, Ne.
Qed.

Print Assumptions predicate_type_sort.
Print Assumptions graph_eq_sort.
Print Assumptions graph_refl_typed.
Print Assumptions graph_transport_typed.
Print Assumptions graph_transport_refl.
Print Assumptions graph_eq_replace.
Print Assumptions graph_refl_replace.
Print Assumptions dependent_congruence_typed.
Print Assumptions dependent_congruence_replace.
Print Assumptions dependent_congruence_applies.
Print Assumptions dependent_congruence_reflexivity.
Print Assumptions predicate_type_normal.
Print Assumptions fiber_congruence_typed.
Print Assumptions fiber_congruence_replace.
Print Assumptions fiber_congruence_applies.
Print Assumptions fiber_congruence_reflexivity.
Print Assumptions graph_eq_normal.
Print Assumptions graph_refl_normal.
Print Assumptions dependent_congruence_normal.
Print Assumptions fiber_congruence_normal.
End DependentEquality.
