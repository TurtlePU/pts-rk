From Stdlib Require Import Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation
  Ranks DefEq Reduction AbstractRewriting Congruence.
From PTSrk.NormalizationComplexity Require Import Greedy.
From PTSrk.SelfInterpreter Require Import BrownPalsberg IndexedEquality.
Import Context.

(** Actual ORIGINAL object terms composing and mapping indexed equality
    evidence. These operations build new witnesses from supplied witnesses;
    they do not assume source-conversion coherence, function extensionality,
    same-level symmetry, or a successful dependent quotation theorem. *)
Module IndexedCoherence.
Module BP := BrownPalsberg.BrownPalsberg.
Module IE := IndexedEquality.IndexedEquality.

Definition compose b {n} (A u e f : Term nat n) :=
  lam (IE.motive_type b A)
    (lam (app (var fzero) (shift u))
      (IE.transport (shift (shift f)) (var (fsucc fzero))
        (IE.transport (shift (shift e)) (var (fsucc fzero)) (var fzero)))).

Definition map_motive {n} (A g P : Term nat n) :=
  lam A (app (shift P) (app (shift g) (var fzero))).

Definition map_congruence b {n} (A B g e : Term nat n) :=
  lam (IE.motive_type b B)
    (app (shift e) (map_motive (shift A) (shift g) (var fzero))).

Lemma motive_type_shift b n (A : Term nat n) :
  shift (IE.motive_type b A) = IE.motive_type b (shift A).
Proof. apply IE.motive_type_rename. Qed.

Lemma eq_type_shift b n (A u v : Term nat n) :
  shift (IE.eq_type b A u v) = IE.eq_type b (shift A) (shift u) (shift v).
Proof. apply IE.eq_type_rename. Qed.

(** Homogeneous transitivity at the SAME motive level b. The result has
    sort max(a+2,b+1), exactly as the input equality types do. *)
Theorem compose_typed a b n (G : Ctx nat n) A u v w e f :
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G u A -> @typ nat RankSorts n G v A ->
  @typ nat RankSorts n G w A ->
  @typ nat RankSorts n G e (IE.eq_type b A u v) ->
  @typ nat RankSorts n G f (IE.eq_type b A v w) ->
  @typ nat RankSorts n G (compose b A u e f) (IE.eq_type b A u w).
Proof.
  intros HA Hu Hv Hw He Hf.
  set (GP := G & IE.motive_type b A).
  set (D := GP & app (var fzero) (shift u)).
  assert (HE : typ D (shift (shift e))
      (IE.eq_type b (shift (shift A)) (shift (shift u)) (shift (shift v)))).
  { rewrite <- !eq_type_shift; apply weakening, weakening; exact He. }
  assert (HF : typ D (shift (shift f))
      (IE.eq_type b (shift (shift A)) (shift (shift v)) (shift (shift w)))).
  { rewrite <- !eq_type_shift; apply weakening, weakening; exact Hf. }
  assert (HP : typ D (var (fsucc fzero)) (IE.motive_type b (shift (shift A)))).
  { rewrite <- !motive_type_shift.
    change (typ D (shift (var fzero)) (shift (shift (IE.motive_type b A)))).
    apply weakening. change (typ GP (var fzero) (GP !! fzero)); constructor. }
  assert (Hz : typ D (var fzero) (app (var (fsucc fzero)) (shift (shift u)))).
  { change (typ D (var fzero) (D !! fzero)); constructor. }
  unfold compose, IE.eq_type, BP.arr.
  apply typ_λ with (ℓ := S a); [apply IE.motive_type_sort; exact HA |].
  apply typ_λ with (ℓ := b); [apply IE.bound_motive_application; exact Hu |].
  change (typ D (IE.transport (shift (shift f)) (var (fsucc fzero))
      (IE.transport (shift (shift e)) (var (fsucc fzero)) (var fzero)))
    (app (var (fsucc fzero)) (shift (shift w)))).
  eapply IE.transport_typed; [exact HF | exact HP |].
  eapply IE.transport_typed; eassumption.
Qed.

Lemma map_motive_typed a b n (G : Ctx nat n) A B g P :
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G g (BP.arr A B) ->
  @typ nat RankSorts n G P (IE.motive_type b B) ->
  @typ nat RankSorts n G (map_motive A g P) (IE.motive_type b A).
Proof.
  intros HA Hg HP; unfold map_motive, IE.motive_type, BP.arr at 1.
  apply typ_λ with (ℓ := a); [exact HA |].
  eapply BP.arr_apply with (A := shift B).
  - change (typ (G & A) (shift P) (BP.arr (shift B) (shift (𝓤 b)))).
    rewrite <- BP.arr_shift; apply weakening; exact HP.
  - eapply BP.arr_apply with (A := shift A).
    + rewrite <- BP.arr_shift; apply weakening; exact Hg.
    + change (typ (G & A) (var fzero) ((G & A) !! fzero)); constructor.
Qed.

Lemma map_motive_beta n (A g P u : Term nat n) :
  step nat n (app (map_motive A g P) u) (app P (app g u)).
Proof.
  unfold map_motive. replace (app P (app g u)) with
    (subst (app (shift P) (app (shift g) (var fzero))) u) by syntax_simp.
  apply step_beta.
Qed.

(** Ordinary NONDEPENDENT map congruence preserves motive level b.
    Domain and codomain sorts may differ: the output equality type has
    sort max(d+2,b+1). No cumulativity or function equality is used. *)
Theorem map_congruence_typed a d b n (G : Ctx nat n) A B g u v e :
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G B (𝓤 d) ->
  @typ nat RankSorts n G g (BP.arr A B) ->
  @typ nat RankSorts n G u A -> @typ nat RankSorts n G v A ->
  @typ nat RankSorts n G e (IE.eq_type b A u v) ->
  @typ nat RankSorts n G (map_congruence b A B g e)
    (IE.eq_type b B (app g u) (app g v)).
Proof.
  intros HA HB Hg Hu Hv He.
  set (GP := G & IE.motive_type b B).
  set (M := map_motive (shift A) (shift g) (var fzero)).
  assert (HE : typ GP (shift e) (IE.eq_type b (shift A) (shift u) (shift v))).
  { rewrite <- eq_type_shift; apply weakening; exact He. }
  assert (HM : typ GP M (IE.motive_type b (shift A))).
  { unfold M; apply map_motive_typed with (a := a) (B := shift B).
    - change (typ GP (shift A) (shift (𝓤 a))); apply weakening; exact HA.
    - rewrite <- BP.arr_shift; apply weakening; exact Hg.
    - rewrite <- motive_type_shift.
      change (typ GP (var fzero) (GP !! fzero)); constructor. }
  unfold map_congruence, IE.eq_type.
  apply typ_λ with (ℓ := S d); [apply IE.motive_type_sort; exact HB |].
  change (typ GP (app (shift e) M)
    (BP.arr (app (var fzero) (shift (app g u)))
      (app (var fzero) (shift (app g v))))).
  eapply typ_conv with
    (T := BP.arr (app M (shift u)) (app M (shift v))) (ℓ := S b).
  - eapply IE.eq_specialize; eassumption.
  - replace (S b) with (Nat.max (S b) b) by lia.
    apply BP.arr_sort; apply IE.bound_motive_application;
      eapply BP.arr_apply; eassumption.
  - apply def_equiv_prop; exists (BP.arr
      (app (var fzero) (shift (app g u)))
      (app (var fzero) (shift (app g v)))); split; [| reflexivity].
    apply BP.arr_reduces; apply rtc_in, map_motive_beta.
Qed.

Theorem compose_replace b m n (sigma : Fin m -> Term nat n) A u e f :
  replace sigma (compose b A u e f) =
  compose b (replace sigma A) (replace sigma u) (replace sigma e) (replace sigma f).
Proof.
  unfold compose, IE.transport, IE.motive_type, BP.arr; syntax_simp.
Qed.

Lemma map_motive_replace m n (sigma : Fin m -> Term nat n) A g P :
  replace sigma (map_motive A g P) =
  map_motive (replace sigma A) (replace sigma g) (replace sigma P).
Proof. unfold map_motive; syntax_simp. Qed.

Theorem map_congruence_replace b m n (sigma : Fin m -> Term nat n) A B g e :
  replace sigma (map_congruence b A B g e) =
  map_congruence b (replace sigma A) (replace sigma B) (replace sigma g) (replace sigma e).
Proof. unfold map_congruence, map_motive, IE.motive_type, BP.arr; syntax_simp. Qed.

Theorem compose_applies b n (A u e f P z : Term nat n) :
  reduces_to nat n (IE.transport (compose b A u e f) P z)
    (IE.transport f P (IE.transport e P z)).
Proof.
  unfold compose, IE.transport.
  eapply rtc_step; [apply step_app_left, step_beta |].
  eapply rtc_step; [apply step_beta |]. syntax_simp. reflexivity.
Qed.

Theorem map_congruence_applies b n (A B g e P z : Term nat n) :
  reduces_to nat n (IE.transport (map_congruence b A B g e) P z)
    (IE.transport e (map_motive A g P) z).
Proof.
  unfold map_congruence, IE.transport.
  eapply rtc_step; [apply step_app_left, step_beta |].
  unfold map_motive. syntax_simp.
  cbn [transpose fin_match]; rewrite BP.replace_fsucc. reflexivity.
Qed.

Lemma refl_case_shift b n (A u : Term nat n) :
  shift (IE.refl_case b A u) = IE.refl_case b (shift A) (shift u).
Proof. apply IE.refl_case_rename. Qed.

Lemma refl_function_specializes b n (A u P : Term nat n) :
  reduces_to nat n (app (IE.refl_case b A u) P) (lam (app P u) (var fzero)).
Proof.
  unfold IE.refl_case; eapply rtc_step; [apply step_beta |].
  syntax_simp. reflexivity.
Qed.

Theorem compose_reflexivity b n (A u : Term nat n) :
  reduces_to nat n
    (compose b A u (IE.refl_case b A u) (IE.refl_case b A u))
    (IE.refl_case b A u).
Proof.
  unfold compose; rewrite !refl_case_shift.
  change (reduces_to nat n
    (lam (IE.motive_type b A) (lam (app (var fzero) (shift u))
      (IE.transport (IE.refl_case b (shift (shift A)) (shift (shift u)))
        (var (fsucc fzero))
        (IE.transport (IE.refl_case b (shift (shift A)) (shift (shift u)))
          (var (fsucc fzero)) (var fzero)))))
    (lam (IE.motive_type b A) (lam (app (var fzero) (shift u)) (var fzero)))).
  apply (@λ_cong_par nat (reduces_to nat) _ _ n); [reflexivity |].
  apply (@λ_cong_par nat (reduces_to nat) _ _ (S n)); [reflexivity |].
  eapply rtc_trans; apply IE.transport_refl.
Qed.

Theorem map_congruence_reflexivity b n (A B g u : Term nat n) :
  reduces_to nat n (map_congruence b A B g (IE.refl_case b A u))
    (IE.refl_case b B (app g u)).
Proof.
  unfold map_congruence; rewrite refl_case_shift.
  change (reduces_to nat n
    (lam (IE.motive_type b B)
      (app (IE.refl_case b (shift A) (shift u))
        (map_motive (shift A) (shift g) (var fzero))))
    (lam (IE.motive_type b B)
      (lam (app (var fzero) (shift (app g u))) (var fzero)))).
  apply (@λ_cong_par nat (reduces_to nat) _ _ n); [reflexivity |].
  eapply rtc_trans; [apply refl_function_specializes |].
  apply (@λ_cong_par nat (reduces_to nat) _ _ (S n));
    [apply rtc_in, map_motive_beta | reflexivity].
Qed.

(** Identity equations for ARBITRARY evidence are asserted after applying
    the proof to a motive and argument. We do not silently eta-contract
    lambda P.lambda z.e P z to e. *)
Theorem compose_left_identity_applies b n (A u e P z : Term nat n) :
  reduces_to nat n (IE.transport (compose b A u (IE.refl_case b A u) e) P z)
    (IE.transport e P z).
Proof.
  eapply rtc_trans; [apply compose_applies |].
  unfold IE.transport at 1 3.
  apply (@app_cong_par nat (reduces_to nat) _ _ n);
    [reflexivity | apply IE.transport_refl].
Qed.

Theorem compose_right_identity_applies b n (A u v e P z : Term nat n) :
  reduces_to nat n (IE.transport (compose b A u e (IE.refl_case b A v)) P z)
    (IE.transport e P z).
Proof. eapply rtc_trans; [apply compose_applies | apply IE.transport_refl]. Qed.

Print Assumptions compose_typed.
Print Assumptions map_motive_typed.
Print Assumptions map_congruence_typed.
Print Assumptions compose_replace.
Print Assumptions map_congruence_replace.
Print Assumptions compose_applies.
Print Assumptions map_congruence_applies.
Print Assumptions compose_reflexivity.
Print Assumptions map_congruence_reflexivity.
Print Assumptions compose_left_identity_applies.
Print Assumptions compose_right_identity_applies.

End IndexedCoherence.
