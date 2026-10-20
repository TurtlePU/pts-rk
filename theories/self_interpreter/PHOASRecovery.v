From Stdlib Require Import Arith.PeanoNat Lia.
From Equations Require Import Equations.
From PTSrk Require Import Syntax Context Typing Preservation Ranks Reduction
  AbstractRewriting Congruence.
From PTSrk.NormalizationComplexity Require Import STLCEmbedding.
From PTSrk.SelfInterpreter Require Import PHOASAlgebra.
Import Context ChurchSTLC.

Module PHOASRecovery.
Module PA := PHOASAlgebra.PHOASAlgebra.
Module TH := TypedHOAS.TypedHOAS.
Module BP := BrownPalsberg.BrownPalsberg.
Module EQ := ExecutableQuotation.ExecutableQuotation.

Definition FamiliesRecover {n} k (F : nat -> Term nat n) :=
  forall r, r <= k -> reduces_to nat n (F r) (BP.type_identity r).
Definition CasesRecover {n} k (o : Fin n) (ab ap : Ty -> Ty -> Term nat n) :=
  (forall A B, order (arrow A B) <= k ->
    reduces_to nat n (ab A B) (BP.abs_identity_case (code A o) (code B o))) /\
  (forall A B, order (arrow A B) <= k ->
    reduces_to nat n (ap A B) (BP.app_identity_case (code A o) (code B o))).

Lemma pretype_recovers A : forall k n F (o : Fin n),
  order A <= k -> FamiliesRecover k F ->
  reduces_to nat n (BP.pretype F o A) (code A o).
Proof.
  induction A; intros k n F o HA HF; cbn [BP.pretype code]; [reflexivity |].
  cbn [order] in HA. rewrite <- (code_rename A2 n (S n) fsucc o).
  change (reduces_to nat n
    (BP.arr (app (F (order A1)) (BP.pretype F o A1))
      (app (F (order A2)) (BP.pretype F o A2)))
    (BP.arr (code A1 o) (code A2 o))).
  apply BP.arr_reduces.
  - eapply rtc_trans; [apply (@app_cong_l nat (reduces_to nat) _ n), HF; lia |].
    eapply rtc_step; [apply BP.type_identity_beta | apply (IHA1 k); [lia | exact HF]].
  - eapply rtc_trans; [apply (@app_cong_l nat (reduces_to nat) _ n), HF; lia |].
    eapply rtc_step; [apply BP.type_identity_beta | apply (IHA2 k); [lia | exact HF]].
Qed.

Lemma interpreted_recovers A k n F (o : Fin n) :
  order A <= k -> FamiliesRecover k F ->
  reduces_to nat n (BP.interpreted_type F o A) (code A o).
Proof.
  intros HA HF. unfold BP.interpreted_type.
  eapply rtc_trans; [apply (@app_cong_l nat (reduces_to nat) _ n), HF; exact HA |].
  eapply rtc_step; [apply BP.type_identity_beta | apply (pretype_recovers A k); assumption].
Qed.

Lemma families_recover_lift k n (F : nat -> Term nat n) :
  FamiliesRecover k F -> FamiliesRecover k (TH.lift_family F).
Proof.
  intros HF r Hr. change (reduces_to nat (S n) (shift (F r)) (shift (BP.type_identity r))).
  apply rename_rtc, HF; exact Hr.
Qed.

Lemma cases_recover_lift k n (o : Fin n) ab ap :
  CasesRecover k o ab ap -> CasesRecover k (fsucc o) (TH.lift_cases ab) (TH.lift_cases ap).
Proof.
  intros [Hab Hap]. split; intros A B HAB; unfold TH.lift_cases.
  - rewrite <- !code_rename with (f := fsucc).
    rewrite <- (proj1 (TH.identity_case_rename n (S n) fsucc (code A o) (code B o))).
    apply rename_rtc, Hab; exact HAB.
  - rewrite <- !code_rename with (f := fsucc).
    rewrite <- (proj2 (TH.identity_case_rename n (S n) fsucc (code A o) (code B o))).
    apply rename_rtc, Hap; exact HAB.
Qed.

(** Only the finite rank budget of the supplied source derivation is used.
    No laws are required of neutral fallback parameters above that budget. *)
Theorem prequote_recovers n E o t A (d : @EQ.derivation n E o t A) :
  forall k m rho F ab ap, TH.rank_budget d <= k ->
  FamiliesRecover k F -> CasesRecover k (rho o) ab ap ->
  reduces_to nat m (TH.prequote d m rho F ab ap) (rename rho t).
Proof.
  induction d; intros k m rho F ab ap Hk HF [Hab Hap]; cbn [TH.prequote rename].
  - reflexivity.
  - assert (HAB : order (arrow A B) <= k).
    { unfold TH.rank_budget in Hk; lia. }
    assert (HA : order A <= k) by (cbn [order] in HAB; lia).
    assert (Hbody : TH.rank_budget d <= k).
    { unfold TH.rank_budget in *. cbn [EQ.quote_budget] in Hk.
      cbn [order] in Hk; lia. }
    rewrite code_rename. eapply rtc_trans.
    + apply (@app_cong_l nat (reduces_to nat) _ m), Hab; exact HAB.
    + eapply rtc_step; [apply BP.abs_identity_case_recovers |].
      apply (@λ_cong_par nat (reduces_to nat) _ _ m).
      * apply (interpreted_recovers A k); assumption.
      * apply (IHd k); [exact Hbody | apply families_recover_lift; exact HF |].
        apply cases_recover_lift; split; assumption.
  - assert (HAB : order (arrow A B) <= k).
    { unfold TH.rank_budget in Hk; cbn [EQ.quote_budget] in Hk; lia. }
    assert (Hfun : TH.rank_budget d1 <= k).
    { unfold TH.rank_budget in *; cbn [EQ.quote_budget] in Hk; lia. }
    assert (Harg : TH.rank_budget d2 <= k).
    { unfold TH.rank_budget in *; cbn [EQ.quote_budget order] in Hk; lia. }
    eapply rtc_trans.
    + apply (@app_cong_l nat (reduces_to nat) _ m), (@app_cong_l nat (reduces_to nat) _ m), Hap;
        exact HAB.
    + eapply rtc_trans; [apply BP.app_identity_case_recovers |].
      apply (@app_cong_par nat (reduces_to nat) _ _ m).
      * apply (IHd1 k); try assumption; split; assumption.
      * apply (IHd2 k); try assumption; split; assumption.
Qed.

Lemma specialize_case_replace A B m n (sigma : Fin m -> Term nat n) F o p h :
  sigma o = var p ->
  replace sigma (PA.specialize_case F o h A B) =
  PA.specialize_case (fun r => replace sigma (F r)) p
    (fun a b => replace sigma (h a b)) A B.
Proof.
  intro Ho; unfold PA.specialize_case; cbn [replace].
  rewrite (TH.pretype_replace A m n sigma F o p Ho),
    (TH.pretype_replace B m n sigma F o p Ho). reflexivity.
Qed.

Theorem specialized_cases_recover k n F (o : Fin n) hab hap :
  FamiliesRecover k F ->
  (forall a b, Nat.max (S a) b <= k ->
    reduces_to nat n (hab a b) (BP.abs_identity a b)) ->
  (forall a b, Nat.max (S a) b <= k ->
    reduces_to nat n (hap a b) (BP.app_identity a b)) ->
  CasesRecover k o (PA.specialize_case F o hab) (PA.specialize_case F o hap).
Proof.
  intros HF Hab Hap; split; intros A B HAB; unfold PA.specialize_case.
  - eapply rtc_trans; [|apply BP.abs_identity_specializes].
    apply (@app_cong_par nat (reduces_to nat) _ _ n).
    + apply (@app_cong_par nat (reduces_to nat) _ _ n).
      * apply Hab; exact HAB.
      * apply (pretype_recovers A k); [cbn [order] in HAB; lia | exact HF].
    + apply (pretype_recovers B k); [cbn [order] in HAB; lia | exact HF].
  - eapply rtc_trans; [|apply BP.app_identity_specializes].
    apply (@app_cong_par nat (reduces_to nat) _ _ n).
    + apply (@app_cong_par nat (reduces_to nat) _ _ n).
      * apply Hap; exact HAB.
      * apply (pretype_recovers A k); [cbn [order] in HAB; lia | exact HF].
    + apply (pretype_recovers B k); [cbn [order] in HAB; lia | exact HF].
Qed.

Theorem quoted_substitution_recovers n E o t A (d : @EQ.derivation n E o t A)
    k m p rho rho' F hab hap (sigma : Fin m -> Term nat p) :
  TH.rank_budget d <= k ->
  (forall i, sigma (rho i) = var (rho' i)) ->
  (forall r, r <= k -> replace sigma (F r) = BP.type_identity r) ->
  (forall a b, Nat.max (S a) b <= k -> replace sigma (hab a b) = BP.abs_identity a b) ->
  (forall a b, Nat.max (S a) b <= k -> replace sigma (hap a b) = BP.app_identity a b) ->
  reduces_to nat p (replace sigma (PA.quoted d m rho F hab hap)) (rename rho' t).
Proof.
  intros Hk Hvar HF Hab Hap. unfold PA.quoted.
  rewrite (TH.prequote_substitution _ _ _ _ _ d m p rho rho' F
    (PA.specialize_case F (rho o) hab) (PA.specialize_case F (rho o) hap) sigma Hvar).
  assert (HFR : FamiliesRecover k (fun r => replace sigma (F r))).
  { intros r Hr; rewrite HF by exact Hr; reflexivity. }
  assert (HCR : CasesRecover k (rho' o)
    (PA.specialize_case (fun r => replace sigma (F r)) (rho' o)
      (fun a b => replace sigma (hab a b)))
    (PA.specialize_case (fun r => replace sigma (F r)) (rho' o)
      (fun a b => replace sigma (hap a b)))).
  { apply specialized_cases_recover; [exact HFR | |].
    - intros a b H; rewrite Hab by exact H; reflexivity.
    - intros a b H; rewrite Hap by exact H; reflexivity. }
  destruct HCR as [Habs Haps].
  apply (prequote_recovers _ _ _ _ _ d k); [exact Hk | exact HFR |].
  split; intros B C HBC;
    rewrite (specialize_case_replace B C m p sigma F (rho o) (rho' o) _ (Hvar o));
    [apply Habs | apply Haps]; exact HBC.
Qed.

Print Assumptions pretype_recovers.
Print Assumptions prequote_recovers.
Print Assumptions specialized_cases_recover.
Print Assumptions quoted_substitution_recovers.
End PHOASRecovery.
