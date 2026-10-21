From Stdlib Require Import Bool.Bool Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting Congruence DefEq.
From PTSrk.NormalizationComplexity Require Import Greedy Morphisms.
From PTSrk.SelfInterpreter Require Import IndexedEquality OpenCanonical
  ContextualTelescope ContextualTelescopeRun RealizedEquality.
Import Context ListNotations.

(** Normal equality-only realizers over arbitrary dependent telescopes.
    Supplied endpoints and domains have independent ORIGINAL typings.
    Normalization is restricted to an eraser's annotations: its complete
    application still returns the literal supplied payload, not its NF. *)
Module ContextualEqualityRealizer.
Module IE := IndexedEquality.IndexedEquality.
Module OC := OpenCanonical.OpenCanonical.
Module CT := ContextualTelescope.ContextualTelescope.
Module TR := ContextualTelescopeRun.ContextualTelescopeRun.
Module RE := RealizedEquality.RealizedEquality.

(** Only the lambda spine and final bound variable matter. Every original
    annotation remains present and may be arbitrary, even nonnormal. *)
Fixpoint eraser (rs : list nat) : forall n, Term nat n -> Prop :=
  match rs with
  | [] => fun n q => exists (A : Term nat n) (B : Term nat (S n)),
      q = lam A (lam B (var fzero))
  | _ :: tail => fun n q => exists (A : Term nat n) (body : Term nat (S n)),
      q = lam A body /\ eraser tail (S n) body
  end.

Lemma eraser_replace rs : forall m n (sigma : Fin m -> Term nat n) q,
  eraser rs m q -> eraser rs n (replace sigma q).
Proof.
  induction rs; intros m n sigma q H; cbn [eraser] in *.
  - destruct H as [A [B ->]]; cbn [replace]; eexists; eexists; reflexivity.
  - destruct H as [A [body [-> Hbody]]]; cbn [replace].
    eexists; eexists; split; [reflexivity | apply IHrs; exact Hbody].
Qed.

Lemma eraser_greedy rs : forall n q,
  eraser rs n q -> eraser rs n (greedy q).
Proof.
  induction rs; intros n q H; cbn [eraser] in *.
  - destruct H as [A [B ->]]; cbn [greedy]; eexists; eexists; reflexivity.
  - destruct H as [A [body [-> Hbody]]]; cbn [greedy].
    eexists; eexists; split; [reflexivity | apply IHrs; exact Hbody].
Qed.

Lemma eraser_rounds fuel rs n (q : Term nat n) :
  eraser rs n q -> eraser rs n (rounds fuel q).
Proof.
  revert q; induction fuel; intros q H; cbn [rounds]; [exact H |].
  apply IHfuel, eraser_greedy; exact H.
Qed.

Theorem eraser_run m rs (D : CT.telescope m rs) : forall n sigma q P z,
  eraser rs n q ->
  reduces_to nat n (IE.transport (TR.run D sigma q) P z) z.
Proof.
  induction D; intros k sigma q P z H; cbn [eraser] in H.
  - destruct H as [A [B ->]]; cbn [TR.run]; unfold IE.transport.
    eapply rtc_step; [apply step_app_left, step_beta |].
    unfold subst; cbn [replace transpose fin_match].
    eapply rtc_step; [apply step_beta |].
    unfold subst; cbn [replace fin_match]; reflexivity.
  - destruct H as [X [body [-> Hbody]]]; cbn [TR.run]; unfold IE.transport.
    eapply rtc_trans.
    + apply (@app_cong_l nat (reduces_to nat) _ k),
        (@app_cong_l nat (reduces_to nat) _ k), TR.run_reduces, rtc_in, step_beta.
    + apply IHD; unfold subst; apply eraser_replace; exact Hbody.
Qed.

Definition raw_witness d {n rs} (G : Ctx nat n) (D : CT.telescope n rs) C u :=
  CT.close_term D (RE.normal_reflexivity d (CT.context D G) C u).
Definition normal_witness d {n rs} (G : Ctx nat n) (D : CT.telescope n rs) C u :=
  OC.nf G (raw_witness d G D C u).
Definition witness_type d {n rs} (D : CT.telescope n rs) C u v :=
  CT.close_type D (IE.eq_type d C u v).
Definition rank rs c d := CT.rank rs (Nat.max (c+2) (d+1)).

Lemma raw_witness_eraser d n rs (G : Ctx nat n) (D : CT.telescope n rs) C u :
  eraser rs n (raw_witness d G D C u).
Proof.
  unfold raw_witness, RE.normal_reflexivity; revert G C u; induction D;
    intros; cbn [CT.close_term eraser].
  - unfold IE.refl_case; eexists; eexists; reflexivity.
  - eexists; eexists; split; [reflexivity | apply IHD].
Qed.

Theorem normal_witness_eraser d n rs (G : Ctx nat n) (D : CT.telescope n rs) C u :
  eraser rs n (normal_witness d G D C u).
Proof. unfold normal_witness, OC.nf; apply eraser_rounds, raw_witness_eraser. Qed.

Theorem witness_type_sort c d n rs (G : Ctx nat n) (D : CT.telescope n rs) C u v :
  CT.formed G D ->
  @typ nat RankSorts _ (CT.context D G) C (𝓤 c) ->
  @typ nat RankSorts _ (CT.context D G) u C ->
  @typ nat RankSorts _ (CT.context D G) v C ->
  @typ nat RankSorts n G (witness_type d D C u v) (𝓤 (rank rs c d)).
Proof. intros HD HC Hu Hv; apply CT.close_type_sort; [exact HD | eapply IE.eq_type_sort; eassumption]. Qed.

Theorem raw_witness_typed c d n rs (G : Ctx nat n) (D : CT.telescope n rs) C u v :
  @wf nat RankSorts n G -> CT.formed G D ->
  @typ nat RankSorts _ (CT.context D G) C (𝓤 c) ->
  @typ nat RankSorts _ (CT.context D G) u C ->
  @typ nat RankSorts _ (CT.context D G) v C ->
  def_equiv nat _ u v ->
  @typ nat RankSorts n G (raw_witness d G D C u) (witness_type d D C u v).
Proof.
  intros HG HD HC Hu Hv Heq; apply CT.close_typing; [exact HD |].
  eapply RE.normal_reflexivity_typed; try eassumption; apply CT.formed_wf; assumption.
Qed.

Theorem normal_witness_typed c d n rs (G : Ctx nat n) (D : CT.telescope n rs) C u v :
  @wf nat RankSorts n G -> CT.formed G D ->
  @typ nat RankSorts _ (CT.context D G) C (𝓤 c) ->
  @typ nat RankSorts _ (CT.context D G) u C ->
  @typ nat RankSorts _ (CT.context D G) v C ->
  def_equiv nat _ u v ->
  @typ nat RankSorts n G (normal_witness d G D C u) (witness_type d D C u v).
Proof.
  intros HG HD HC Hu Hv Heq; apply OC.nf_typed; [exact HG |].
  eapply raw_witness_typed; eassumption.
Qed.

Theorem normal_witness_normal c d n rs (G : Ctx nat n) (D : CT.telescope n rs) C u :
  @wf nat RankSorts n G -> CT.formed G D ->
  @typ nat RankSorts _ (CT.context D G) C (𝓤 c) ->
  @typ nat RankSorts _ (CT.context D G) u C ->
  normalb (normal_witness d G D C u) = true.
Proof.
  intros HG HD HC Hu; apply OC.nf_normal with (T := witness_type d D C u u); [exact HG |].
  eapply raw_witness_typed; try eassumption; reflexivity.
Qed.

(** The equality's complete application erases even after an ARBITRARY
    target substitution, without typing or normalization assumptions on
    the supplied arguments or returned payload. *)
Theorem normal_witness_erases d m rs (G : Ctx nat m) (D : CT.telescope m rs)
    C u n (sigma : Fin (CT.scope rs m) -> Term nat n) P z :
  reduces_to nat n (IE.transport
    (TR.run D sigma (replace (TR.base sigma) (normal_witness d G D C u))) P z) z.
Proof. apply eraser_run, eraser_replace, normal_witness_eraser. Qed.

Theorem normal_witness_run_typed c d m rs (G : Ctx nat m) (D : CT.telescope m rs)
    C u v n (H : Ctx nat n) (sigma : Fin (CT.scope rs m) -> Term nat n) :
  @wf nat RankSorts m G -> CT.formed G D ->
  @typ nat RankSorts _ (CT.context D G) C (𝓤 c) ->
  @typ nat RankSorts _ (CT.context D G) u C ->
  @typ nat RankSorts _ (CT.context D G) v C -> def_equiv nat _ u v ->
  TypedSub (CT.context D G) H sigma ->
  @typ nat RankSorts n H
    (TR.run D sigma (replace (TR.base sigma) (normal_witness d G D C u)))
    (IE.eq_type d (replace sigma C) (replace sigma u) (replace sigma v)).
Proof.
  intros HG HD HC Hu Hv Heq HS; rewrite <- IE.eq_type_replace.
  apply TR.run_typing with (G := G); [exact HS |].
  eapply typing_replace.
  - eapply normal_witness_typed; eassumption.
  - apply TR.base_typed with (D := D); exact HS.
Qed.

Theorem normal_witness_transport_typed c d m rs (G : Ctx nat m) (D : CT.telescope m rs)
    C u v n (H : Ctx nat n) sigma P z :
  @wf nat RankSorts m G -> CT.formed G D ->
  @typ nat RankSorts _ (CT.context D G) C (𝓤 c) ->
  @typ nat RankSorts _ (CT.context D G) u C ->
  @typ nat RankSorts _ (CT.context D G) v C -> def_equiv nat _ u v ->
  TypedSub (CT.context D G) H sigma ->
  @typ nat RankSorts n H P (IE.motive_type d (replace sigma C)) ->
  @typ nat RankSorts n H z (app P (replace sigma u)) ->
  @typ nat RankSorts n H (IE.transport
    (TR.run D sigma (replace (TR.base sigma) (normal_witness d G D C u))) P z)
    (app P (replace sigma v)).
Proof.
  intros HG HD HC Hu Hv Heq HS HP Hz; eapply IE.transport_typed; try eassumption.
  eapply normal_witness_run_typed; eassumption.
Qed.

Theorem rank_bounded k rs c d :
  Forall (fun r => r <= k) rs -> c <= k -> d <= k -> rank rs c d <= k+2.
Proof. intros Hrs Hc Hd; unfold rank; pose proof (CT.rank_bounded rs k (Nat.max (c+2) (d+1)) Hrs); lia. Qed.

Print Assumptions eraser_replace.
Print Assumptions eraser_rounds.
Print Assumptions eraser_run.
Print Assumptions normal_witness_eraser.
Print Assumptions witness_type_sort.
Print Assumptions raw_witness_typed.
Print Assumptions normal_witness_typed.
Print Assumptions normal_witness_normal.
Print Assumptions normal_witness_erases.
Print Assumptions normal_witness_run_typed.
Print Assumptions normal_witness_transport_typed.
Print Assumptions rank_bounded.
End ContextualEqualityRealizer.
