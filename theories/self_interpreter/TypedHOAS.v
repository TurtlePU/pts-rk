From Stdlib Require Import Arith.PeanoNat Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation
  Ranks Reduction AbstractRewriting Congruence.
From PTSrk.NormalizationComplexity Require Import STLCEmbedding Greedy.
From PTSrk.SelfInterpreter Require Import BrownPalsberg ExecutableQuotation.
Import Context.

Module TypedHOAS.
Module BP := BrownPalsberg.BrownPalsberg.
Module EQ := ExecutableQuotation.ExecutableQuotation.
Import ChurchSTLC.

(** A source-type-indexed, derivation-directed PHOAS PREquotation.  Families
    and case operations are external parameters; there is no assertion
    here that an infinite family is one internal PTS value.  Each operation
    is already specialized at its two source-type representations. *)
Definition abs_type {n} F (o : Fin n) A B :=
  BP.arr (BP.arr (BP.interpreted_type F o A) (BP.interpreted_type F o B))
    (BP.interpreted_type F o (arrow A B)).
Definition app_type {n} F (o : Fin n) A B :=
  BP.arr (BP.interpreted_type F o (arrow A B))
    (BP.arr (BP.interpreted_type F o A) (BP.interpreted_type F o B)).

Definition lift_family {n} (F : nat -> Term nat n) := fun r => shift (F r).
Definition lift_cases {n} (h : Ty -> Ty -> Term nat n) := fun A B => shift (h A B).

Fixpoint prequote {n E o t A} (d : @EQ.derivation n E o t A) :
  forall m, (Fin n -> Fin m) -> (nat -> Term nat m) ->
    (Ty -> Ty -> Term nat m) -> (Ty -> Ty -> Term nat m) -> Term nat m :=
  match d in @EQ.derivation n' E' o' t' A' return
    forall m, (Fin n' -> Fin m) -> (nat -> Term nat m) ->
      (Ty -> Ty -> Term nat m) -> (Ty -> Ty -> Term nat m) -> Term nat m with
  | EQ.d_var E o i A H => fun m rho F ab ap => var (rho i)
  | EQ.d_lam E o A B b db => fun m rho F ab ap =>
      app (ab A B) (lam (BP.interpreted_type F (rho o) A)
        (prequote db (S m) (weak rho) (lift_family F) (lift_cases ab) (lift_cases ap)))
  | EQ.d_app E o A B f u df du => fun m rho F ab ap =>
      app (app (ap A B) (prequote df m rho F ab ap)) (prequote du m rho F ab ap)
  end.

Lemma arr_rename m n (rho : Fin m -> Fin n) (A B : Term nat m) :
  rename rho (BP.arr A B) = BP.arr (rename rho A) (rename rho B).
Proof. unfold BP.arr. syntax_simp. Qed.

Lemma pretype_rename A : forall m n (rho : Fin m -> Fin n) F o,
  rename rho (BP.pretype F o A) = BP.pretype (fun r => rename rho (F r)) (rho o) A.
Proof.
  induction A; intros; cbn [BP.pretype]; [reflexivity |].
  rewrite arr_rename. cbn [rename]. rewrite IHA1, IHA2. reflexivity.
Qed.

Lemma interpreted_rename A m n (rho : Fin m -> Fin n) F o :
  rename rho (BP.interpreted_type F o A) =
  BP.interpreted_type (fun r => rename rho (F r)) (rho o) A.
Proof. unfold BP.interpreted_type; cbn [rename]; rewrite pretype_rename; reflexivity. Qed.

Lemma interpreted_shift A n F (o : Fin n) :
  shift (BP.interpreted_type F o A) = BP.interpreted_type (lift_family F) (fsucc o) A.
Proof. apply interpreted_rename. Qed.

Lemma abs_type_shift n F (o : Fin n) A B :
  shift (abs_type F o A B) = abs_type (lift_family F) (fsucc o) A B.
Proof. unfold abs_type. rewrite !BP.arr_shift, !interpreted_shift; reflexivity. Qed.
Lemma app_type_shift n F (o : Fin n) A B :
  shift (app_type F o A B) = app_type (lift_family F) (fsucc o) A B.
Proof. unfold app_type. rewrite !BP.arr_shift, !interpreted_shift; reflexivity. Qed.

Definition FamiliesTyped {n} (G : Ctx nat n) F :=
  forall r, @typ nat RankSorts n G (F r) (BP.family_type r r).
Definition CasesTyped {n} (G : Ctx nat n) F o ab ap :=
  (forall A B, @typ nat RankSorts n G (ab A B) (abs_type F o A B)) /\
  (forall A B, @typ nat RankSorts n G (ap A B) (app_type F o A B)).

Theorem prequote_typed n E o t A (d : @EQ.derivation n E o t A) :
  forall m (G : Ctx nat m) rho F ab ap,
  @typ nat RankSorts m G (var (rho o)) (𝓤 0) ->
  FamiliesTyped G F -> CasesTyped G F (rho o) ab ap ->
  (forall i C, E i = Some C ->
    @typ nat RankSorts m G (var (rho i)) (BP.interpreted_type F (rho o) C)) ->
  @typ nat RankSorts m G (prequote d m rho F ab ap) (BP.interpreted_type F (rho o) A).
Proof.
  induction d; intros m G rho F ab ap Ho HF [Hab Hap] HE; cbn [prequote].
  - apply HE; assumption.
  - eapply BP.arr_apply; [apply Hab |].
    unfold BP.arr. eapply typ_λ with (ℓ := order A).
    + apply BP.interpreted_type_sort; assumption.
    + rewrite interpreted_shift. apply IHd.
      * change (typ (G & BP.interpreted_type F (rho o) A)
          (shift (var (rho o))) (shift (𝓤 0))). apply weakening; exact Ho.
      * intro r. change (typ (G & BP.interpreted_type F (rho o) A)
          (shift (F r)) (shift (BP.family_type r r))). apply weakening, HF.
      * split; intros C D; unfold lift_cases; cbn [weak fin_match].
        -- rewrite <- abs_type_shift. apply weakening, Hab.
        -- rewrite <- app_type_shift. apply weakening, Hap.
      * intros i C Hi. dependent elimination i; cbn [extend fin_match] in Hi.
        -- inversion Hi; subst C. cbn [weak fin_match]. rewrite <- interpreted_shift.
           change (typ (G & BP.interpreted_type F (rho o) A) (var fzero)
             ((G & BP.interpreted_type F (rho o) A) !! fzero)). constructor.
        -- cbn [weak fin_match]. rewrite <- interpreted_shift.
           change (typ (G & BP.interpreted_type F (rho o) A)
             (shift (var (rho f))) (shift (BP.interpreted_type F (rho o) C))).
           apply weakening, HE; exact Hi.
  - eapply BP.arr_apply.
    + eapply BP.arr_apply; [apply Hap | apply IHd1; try assumption; split; assumption].
    + apply IHd2; try assumption; split; assumption.
Qed.

Definition FamiliesRecover {n} (F : nat -> Term nat n) :=
  forall r, reduces_to nat n (F r) (BP.type_identity r).
Definition CasesRecover {n} (o : Fin n) (ab ap : Ty -> Ty -> Term nat n) :=
  (forall A B, reduces_to nat n (ab A B) (BP.abs_identity_case (code A o) (code B o))) /\
  (forall A B, reduces_to nat n (ap A B) (BP.app_identity_case (code A o) (code B o))).

Lemma pretype_recovers A : forall n F (o : Fin n), FamiliesRecover F ->
  reduces_to nat n (BP.pretype F o A) (code A o).
Proof.
  induction A; intros n F o HF; cbn [BP.pretype code]; [reflexivity |].
  rewrite <- (code_rename A2 n (S n) fsucc o).
  change (reduces_to nat n
    (BP.arr (app (F (order A1)) (BP.pretype F o A1))
      (app (F (order A2)) (BP.pretype F o A2)))
    (BP.arr (code A1 o) (code A2 o))).
  apply BP.arr_reduces.
  - eapply rtc_trans; [apply (@app_cong_l nat (reduces_to nat) _ n), HF |].
    eapply rtc_step; [apply BP.type_identity_beta | apply IHA1; exact HF].
  - eapply rtc_trans; [apply (@app_cong_l nat (reduces_to nat) _ n), HF |].
    eapply rtc_step; [apply BP.type_identity_beta | apply IHA2; exact HF].
Qed.

Lemma interpreted_recovers A n F (o : Fin n) : FamiliesRecover F ->
  reduces_to nat n (BP.interpreted_type F o A) (code A o).
Proof.
  intro HF. unfold BP.interpreted_type.
  eapply rtc_trans; [apply (@app_cong_l nat (reduces_to nat) _ n), HF |].
  eapply rtc_step; [apply BP.type_identity_beta | apply pretype_recovers; exact HF].
Qed.

Lemma identity_case_rename m n (rho : Fin m -> Fin n) (A B : Term nat m) :
  rename rho (BP.abs_identity_case A B) = BP.abs_identity_case (rename rho A) (rename rho B) /\
  rename rho (BP.app_identity_case A B) = BP.app_identity_case (rename rho A) (rename rho B).
Proof.
  unfold BP.abs_identity_case, BP.app_identity_case, BP.arr.
  split; syntax_simp.
Qed.

Lemma families_recover_lift n (F : nat -> Term nat n) :
  FamiliesRecover F -> FamiliesRecover (lift_family F).
Proof.
  intros HF r. change (reduces_to nat (S n) (shift (F r)) (shift (BP.type_identity r))).
  apply rename_rtc, HF.
Qed.

Lemma cases_recover_lift n (o : Fin n) ab ap :
  CasesRecover o ab ap -> CasesRecover (fsucc o) (lift_cases ab) (lift_cases ap).
Proof.
  intros [Hab Hap]. split; intros A B; unfold lift_cases.
  - rewrite <- !code_rename with (f := fsucc).
    rewrite <- (proj1 (identity_case_rename n (S n) fsucc (code A o) (code B o))).
    apply rename_rtc, Hab.
  - rewrite <- !code_rename with (f := fsucc).
    rewrite <- (proj2 (identity_case_rename n (S n) fsucc (code A o) (code B o))).
    apply rename_rtc, Hap.
Qed.

Theorem prequote_recovers n E o t A (d : @EQ.derivation n E o t A) :
  forall m rho F ab ap, FamiliesRecover F -> CasesRecover (rho o) ab ap ->
  reduces_to nat m (prequote d m rho F ab ap) (rename rho t).
Proof.
  induction d; intros m rho F ab ap HF [Hab Hap]; cbn [prequote rename].
  - reflexivity.
  - rewrite code_rename. eapply rtc_trans.
    + apply (@app_cong_l nat (reduces_to nat) _ m), Hab.
    + eapply rtc_step; [apply BP.abs_identity_case_recovers |].
      apply (@λ_cong_par nat (reduces_to nat) _ _ m).
      * apply interpreted_recovers; exact HF.
      * apply IHd; [apply families_recover_lift; exact HF |].
        apply cases_recover_lift; split; assumption.
  - eapply rtc_trans.
    + apply (@app_cong_l nat (reduces_to nat) _ m), (@app_cong_l nat (reduces_to nat) _ m), Hap.
    + eapply rtc_trans; [apply BP.app_identity_case_recovers |].
      apply (@app_cong_par nat (reduces_to nat) _ _ m);
        [apply IHd1 | apply IHd2]; try assumption; split; assumption.
Qed.

(** The real polymorphic Brown--Palsberg handlers specialize to the recovery
    operations used above.  This is computation in the original syntax. *)
Definition identity_abs {n} (o : Fin n) A B :=
  app (app (BP.abs_identity (order A) (order B)) (code A o)) (code B o).
Definition identity_app {n} (o : Fin n) A B :=
  app (app (BP.app_identity (order A) (order B)) (code A o)) (code B o).

Theorem actual_identity_cases_recover n (o : Fin n) :
  CasesRecover o (identity_abs o) (identity_app o).
Proof.
  split; intros A B; [apply BP.abs_identity_specializes | apply BP.app_identity_specializes].
Qed.

Definition identity_interpretation {n E o t A} (d : @EQ.derivation n E o t A) :=
  prequote d n (fun i => i) (fun r => BP.type_identity r) (identity_abs o) (identity_app o).

Theorem identity_interpretation_recovers n E o t A (d : @EQ.derivation n E o t A) :
  reduces_to nat n (identity_interpretation d) t.
Proof.
  unfold identity_interpretation. rewrite <- (rename_id t) at 2.
  apply prequote_recovers; [intro; reflexivity | apply actual_identity_cases_recover].
Qed.

Lemma pretype_ext A : forall n F H (o : Fin n),
  (forall r, F r = H r) -> BP.pretype F o A = BP.pretype H o A.
Proof.
  induction A; intros n F H o HE; cbn [BP.pretype]; [reflexivity |].
  rewrite (HE (order A1)), (HE (order A2)), (IHA1 n F H o HE), (IHA2 n F H o HE).
  reflexivity.
Qed.
Lemma interpreted_ext A n F H (o : Fin n) :
  (forall r, F r = H r) -> BP.interpreted_type F o A = BP.interpreted_type H o A.
Proof. intro HE; unfold BP.interpreted_type; rewrite HE, (pretype_ext A n F H o HE); reflexivity. Qed.

Lemma prequote_ext n E o t A (d : @EQ.derivation n E o t A) :
  forall m rho F H ab ab' ap ap', (forall r, F r = H r) ->
  (forall B C, ab B C = ab' B C) -> (forall B C, ap B C = ap' B C) ->
  prequote d m rho F ab ap = prequote d m rho H ab' ap'.
Proof.
  induction d; intros m rho F J ab ab' ap ap' HF Hab Hap; cbn [prequote].
  - reflexivity.
  - rewrite Hab, (interpreted_ext A m F J (rho o) HF). f_equal. f_equal.
    apply IHd; intros; unfold lift_family, lift_cases; [rewrite HF | rewrite Hab | rewrite Hap]; reflexivity.
  - rewrite Hap, (IHd1 m rho F J ab ab' ap ap' HF Hab Hap),
      (IHd2 m rho F J ab ab' ap ap' HF Hab Hap). reflexivity.
Qed.

Lemma arr_replace m n (sigma : Fin m -> Term nat n) (A B : Term nat m) :
  replace sigma (BP.arr A B) = BP.arr (replace sigma A) (replace sigma B).
Proof. unfold BP.arr. syntax_simp. Qed.

Lemma pretype_replace A : forall m n (sigma : Fin m -> Term nat n) F o p,
  sigma o = var p ->
  replace sigma (BP.pretype F o A) = BP.pretype (fun r => replace sigma (F r)) p A.
Proof.
  induction A; intros m n sigma F o p Ho; cbn [BP.pretype]; [exact Ho |].
  rewrite arr_replace; cbn [replace].
  rewrite (IHA1 m n sigma F o p Ho), (IHA2 m n sigma F o p Ho). reflexivity.
Qed.

Lemma interpreted_replace A m n (sigma : Fin m -> Term nat n) F o p :
  sigma o = var p -> replace sigma (BP.interpreted_type F o A) =
    BP.interpreted_type (fun r => replace sigma (F r)) p A.
Proof.
  intro Ho. unfold BP.interpreted_type; cbn [replace].
  rewrite (pretype_replace A m n sigma F o p Ho). reflexivity.
Qed.

(** Actual simultaneous replacement of the parameters agrees with parameter
    specialization.  Source variables, including the distinguished ground
    type, remain variables under the explicitly stated source renaming.
    This theorem uses no functional-extensionality axiom. *)
Theorem prequote_substitution n E o t A (d : @EQ.derivation n E o t A) :
  forall m k rho rho' F ab ap (sigma : Fin m -> Term nat k),
  (forall i, sigma (rho i) = var (rho' i)) ->
  replace sigma (prequote d m rho F ab ap) =
  prequote d k rho' (fun r => replace sigma (F r))
    (fun B C => replace sigma (ab B C)) (fun B C => replace sigma (ap B C)).
Proof.
  induction d; intros m k rho rho' F ab ap sigma Hvar; cbn [prequote replace].
  - apply Hvar.
  - rewrite (interpreted_replace A m k sigma F (rho o) (rho' o) (Hvar o)).
    f_equal. f_equal.
    assert (HV : forall i, transpose sigma (weak rho i) = var (weak rho' i)).
    { intro i; dependent elimination i; [reflexivity |].
      change (shift (sigma (rho f)) = var (fsucc (rho' f))).
      rewrite Hvar; reflexivity. }
    rewrite (IHd (S m) (S k) (weak rho) (weak rho') (lift_family F)
      (lift_cases ab) (lift_cases ap) (transpose sigma) HV).
    apply prequote_ext; intros; unfold lift_family, lift_cases; syntax_simp.
  - rewrite (IHd1 m k rho rho' F ab ap sigma Hvar),
      (IHd2 m k rho rho' F ab ap sigma Hvar). reflexivity.
Qed.

Theorem substitution_identity_recovers n E o t A (d : @EQ.derivation n E o t A)
  m k rho rho' F ab ap (sigma : Fin m -> Term nat k) :
  (forall i, sigma (rho i) = var (rho' i)) ->
  (forall r, replace sigma (F r) = BP.type_identity r) ->
  (forall B C, replace sigma (ab B C) = identity_abs (rho' o) B C) ->
  (forall B C, replace sigma (ap B C) = identity_app (rho' o) B C) ->
  reduces_to nat k (replace sigma (prequote d m rho F ab ap)) (rename rho' t).
Proof.
  intros Hvar HF Hab Hap. rewrite (prequote_substitution _ _ _ _ _ d m k rho rho' F ab ap sigma Hvar).
  apply prequote_recovers.
  - intro r; rewrite HF; reflexivity.
  - split; intros B C; [rewrite Hab; apply BP.abs_identity_specializes |
      rewrite Hap; apply BP.app_identity_specializes].
Qed.

(** This budget also bounds abstraction annotations: the earlier shallow
    application's budget alone does not.  Laws above the computed budget
    are not needed by the typing theorem below. *)
Definition rank_budget {n E o t A} (d : @EQ.derivation n E o t A) :=
  Nat.max (order A) (EQ.quote_budget d).
Definition BoundedFamiliesTyped {n} k (G : Ctx nat n) F :=
  forall r, r <= k -> @typ nat RankSorts n G (F r) (BP.family_type r r).
Definition BoundedCasesTyped {n} k (G : Ctx nat n) F o ab ap :=
  (forall A B, order (arrow A B) <= k ->
    @typ nat RankSorts n G (ab A B) (abs_type F o A B)) /\
  (forall A B, order (arrow A B) <= k ->
    @typ nat RankSorts n G (ap A B) (app_type F o A B)).

Lemma interpreted_bounded_sort k A n (G : Ctx nat n) F o :
  order A <= k -> @typ nat RankSorts n G (var o) (𝓤 0) ->
  BoundedFamiliesTyped k G F ->
  @typ nat RankSorts n G (BP.interpreted_type F o A) (𝓤 (order A)).
Proof.
  intros Hk Ho HF. unfold BP.interpreted_type. eapply BP.family_apply.
  - apply HF; exact Hk.
  - apply BP.pretype_sort_bounded; [exact Ho | intros; apply HF; lia].
Qed.

Theorem prequote_bounded_typed n E o t A (d : @EQ.derivation n E o t A) :
  forall k m (G : Ctx nat m) rho F ab ap,
  rank_budget d <= k -> @typ nat RankSorts m G (var (rho o)) (𝓤 0) ->
  BoundedFamiliesTyped k G F -> BoundedCasesTyped k G F (rho o) ab ap ->
  (forall i C, E i = Some C ->
    @typ nat RankSorts m G (var (rho i)) (BP.interpreted_type F (rho o) C)) ->
  @typ nat RankSorts m G (prequote d m rho F ab ap) (BP.interpreted_type F (rho o) A).
Proof.
  induction d; intros k m G rho F ab ap Hk Ho HF [Hab Hap] HE; cbn [prequote].
  - apply HE; assumption.
  - assert (Harrow : order (arrow A B) <= k).
    { unfold rank_budget in Hk; lia. }
    assert (HA : order A <= k) by (cbn [order] in Harrow; lia).
    assert (Hbody : rank_budget d <= k).
    { unfold rank_budget. apply Nat.max_lub.
      - eapply Nat.le_trans; [apply Nat.le_max_r | exact Harrow].
      - change (Nat.max (order (arrow A B)) (EQ.quote_budget d) <= k) in Hk.
        eapply Nat.le_trans; [apply Nat.le_max_r | exact Hk]. }
    eapply BP.arr_apply; [apply Hab; exact Harrow |].
    unfold BP.arr. eapply typ_λ with (ℓ := order A).
    + eapply interpreted_bounded_sort; eassumption.
    + rewrite interpreted_shift. apply (IHd k); [exact Hbody | | | |].
      * change (typ (G & BP.interpreted_type F (rho o) A)
          (shift (var (rho o))) (shift (𝓤 0))). apply weakening; exact Ho.
      * intros r Hr. change (typ (G & BP.interpreted_type F (rho o) A)
          (shift (F r)) (shift (BP.family_type r r))). apply weakening, HF; exact Hr.
      * split; intros C D HCD; unfold lift_cases; cbn [weak fin_match].
        -- rewrite <- abs_type_shift. apply weakening, Hab; exact HCD.
        -- rewrite <- app_type_shift. apply weakening, Hap; exact HCD.
      * intros i C Hi. dependent elimination i; cbn [extend fin_match] in Hi.
        -- inversion Hi; subst C. cbn [weak fin_match]. rewrite <- interpreted_shift.
           change (typ (G & BP.interpreted_type F (rho o) A) (var fzero)
             ((G & BP.interpreted_type F (rho o) A) !! fzero)). constructor.
        -- cbn [weak fin_match]. rewrite <- interpreted_shift.
           change (typ (G & BP.interpreted_type F (rho o) A)
             (shift (var (rho f))) (shift (BP.interpreted_type F (rho o) C))).
           apply weakening, HE; exact Hi.
  - assert (Harrow : order (arrow A B) <= k).
    { change (Nat.max (order B) (Nat.max (order (arrow A B))
        (Nat.max (EQ.quote_budget d1) (EQ.quote_budget d2))) <= k) in Hk. lia. }
    assert (Hfun : rank_budget d1 <= k).
    { unfold rank_budget. apply Nat.max_lub; [exact Harrow |].
      change (Nat.max (order B) (Nat.max (order (arrow A B))
        (Nat.max (EQ.quote_budget d1) (EQ.quote_budget d2))) <= k) in Hk. lia. }
    assert (Harg : rank_budget d2 <= k).
    { unfold rank_budget. apply Nat.max_lub.
      - cbn [order] in Harrow; lia.
      - change (Nat.max (order B) (Nat.max (order (arrow A B))
          (Nat.max (EQ.quote_budget d1) (EQ.quote_budget d2))) <= k) in Hk. lia. }
    eapply BP.arr_apply.
    + eapply BP.arr_apply; [apply Hap; exact Harrow |].
      apply (IHd1 k); try assumption; split; assumption.
    + apply (IHd2 k); try assumption; split; assumption.
Qed.

Print Assumptions prequote_typed.
Print Assumptions prequote_recovers.
Print Assumptions actual_identity_cases_recover.
Print Assumptions identity_interpretation_recovers.
Print Assumptions prequote_substitution.
Print Assumptions substitution_identity_recovers.
Print Assumptions prequote_bounded_typed.

End TypedHOAS.
