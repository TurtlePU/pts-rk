From Stdlib Require Import Arith.PeanoNat Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation
  Ranks Reduction AbstractRewriting Congruence DefEq.
From PTSrk.NormalizationComplexity Require Import STLCEmbedding Morphisms Greedy.
From PTSrk.SelfInterpreter Require Import PHOASPackage PHOASRecovery.
Import Context ChurchSTLC.

Module PHOASDecoder.
Module PP := PHOASPackage.PHOASPackage.
Module PT := PHOASTelescope.PHOASTelescope.
Module PR := PHOASRecovery.PHOASRecovery.
Module BP := BrownPalsberg.BrownPalsberg.
Module EQ := ExecutableQuotation.ExecutableQuotation.
Module TH := TypedHOAS.TypedHOAS.

Lemma run_ext m (G : Ctx nat m) : forall n (sigma tau : Fin m -> Term nat n) q,
  (forall i, sigma i = tau i) -> PT.run G sigma q = PT.run G tau q.
Proof.
  induction G; intros k sigma tau q HE; cbn [PT.run]; [reflexivity |].
  rewrite HE. f_equal. apply IHG; intro i; apply HE.
Qed.

(** The ground-type abstraction belongs to this actual closed decoder;
    recovery does not append an external lambda wrapper. *)
Definition output_type A {n} : Term nat n := Π (𝓤 0) (code A fzero).

Lemma output_type_rename A m n (rho : Fin m -> Fin n) :
  rename rho (@output_type A m) = @output_type A n.
Proof. unfold output_type; cbn [rename]. rewrite code_rename; reflexivity. Qed.

Lemma output_type_shift A n : shift (@output_type A n) = @output_type A (S n).
Proof. apply output_type_rename. Qed.

Theorem output_type_sort A n (G : Ctx nat n) :
  @typ nat RankSorts n G (output_type A) (𝓤 (Nat.max 1 (order A))).
Proof.
  unfold output_type. eapply typ_Π with (ℓₜ := 0) (ℓᵤ := order A).
  - constructor; reflexivity.
  - apply code_typed.
    change (typ (G & 𝓤 0) (var fzero) ((G & 𝓤 0) !! fzero)); constructor.
  - reflexivity.
Qed.

Lemma closed_shift n (t : Term nat 0) :
  shift (@PT.lift_closed n t) = @PT.lift_closed (S n) t.
Proof. apply PT.lift_closed_rename. Qed.

Lemma closed_lift_zero (t : Term nat 0) : @PT.lift_closed 0 t = t.
Proof.
  unfold PT.lift_closed. rewrite <- (rename_id t) at 2.
  apply rename_ext; intro i; inversion i.
Qed.

Lemma closed_lift_typing n (G : Ctx nat n) t T :
  @typ nat RankSorts 0 ε t T ->
  @typ nat RankSorts n G (PT.lift_closed t) (PT.lift_closed T).
Proof.
  intro H. unfold PT.lift_closed. eapply typing_rename with (G := ε).
  - intro i; inversion i.
  - exact H.
Qed.

(** Domain formation is independent of source inhabitation: no quoted
    program is used to obtain a universe for the decoder's input type. *)
Theorem quote_type_has_sort k A :
  order A <= k -> exists r, @typ nat RankSorts 0 ε (PP.quote_type k A) (𝓤 r).
Proof.
  intro HA. unfold PP.quote_type.
  apply PT.close_type_sort with (s := order A); [apply PP.package_context_wf |].
  unfold PP.result_type, BP.interpreted_type.
  eapply BP.family_apply with (a := order A).
  - apply PP.families_typed; exact HA.
  - apply BP.pretype_sort_bounded; [apply PP.ground_typed |].
    intros r Hr. apply PP.families_typed; lia.
Qed.

Definition run_at k {n} (o : Fin n) (q : Term nat n) :=
  PT.run (PP.package_context k) (PP.fill k o) q.

Definition decoder k A : Term nat 0 :=
  lam (PP.quote_type k A) (lam (𝓤 0) (run_at k fzero (var (fsucc fzero)))).
Definition decoder_type k A : Term nat 0 :=
  BP.arr (PP.quote_type k A) (output_type A).
Definition decode k A (q : Term nat 0) := app (decoder k A) q.

Lemma filled_result_recovers k A n (o : Fin n) : order A <= k ->
  reduces_to nat n (replace (PP.fill k o) (PP.result_type k A)) (code A o).
Proof.
  intro HA. unfold PP.result_type.
  rewrite TH.interpreted_replace with (p := o) by apply PP.fill_ground.
  apply (PR.interpreted_recovers A k); [exact HA |].
  intros r Hr. rewrite PP.fill_family by lia. reflexivity.
Qed.

Theorem run_at_typed k A n (G : Ctx nat n) (o : Fin n) q :
  order A <= k ->
  @typ nat RankSorts n G (var o) (𝓤 0) ->
  @typ nat RankSorts n G q (PT.lift_closed (PP.quote_type k A)) ->
  @typ nat RankSorts n G (run_at k o q) (code A o).
Proof.
  intros HA Ho Hq. eapply typ_conv with
    (T := replace (PP.fill k o) (PP.result_type k A)) (ℓ := order A).
  - unfold run_at. apply PT.run_typing; [apply PP.fill_typed; exact Ho | exact Hq].
  - apply code_typed; exact Ho.
  - apply def_equiv_prop. exists (code A o); split;
      [apply filled_result_recovers; exact HA | reflexivity].
Qed.

Lemma closed_lift_two (t : Term nat 0) :
  @PT.lift_closed 2 t = shift (shift t).
Proof.
  unfold PT.lift_closed, shift. rewrite rename_comp.
  apply rename_ext; intro i; inversion i.
Qed.

(** A is a full EXTERNAL simple-type index, not merely its numerical order.
    This theorem does not claim one rank-only decoder for all type shapes. *)
Theorem decoder_typed k A : order A <= k ->
  @typ nat RankSorts 0 ε (decoder k A) (decoder_type k A).
Proof.
  intro HA. destruct (quote_type_has_sort k A HA) as [r Hr].
  unfold decoder, decoder_type, BP.arr.
  eapply typ_λ with (ℓ := r); [exact Hr |].
  rewrite output_type_shift. unfold output_type.
  eapply typ_λ with (ℓ := 0); [constructor; reflexivity |].
  apply run_at_typed.
  - exact HA.
  - change (typ ((ε & PP.quote_type k A) & 𝓤 0) (var fzero)
      (((ε & PP.quote_type k A) & 𝓤 0) !! fzero)); constructor.
  - rewrite closed_lift_two.
    change (typ ((ε & PP.quote_type k A) & 𝓤 0) (var (fsucc fzero))
      (((ε & PP.quote_type k A) & 𝓤 0) !! fsucc fzero)); constructor.
Qed.

Theorem decoder_type_has_sort k A : order A <= k ->
  exists r, @typ nat RankSorts 0 ε (decoder_type k A) (𝓤 r).
Proof.
  intro HA. destruct (quote_type_has_sort k A HA) as [r Hr].
  exists (Nat.max (S r) (Nat.max 1 (order A))).
  unfold decoder_type. apply BP.arr_sort; [exact Hr | apply output_type_sort].
Qed.

Theorem decode_typed k A q : order A <= k ->
  @typ nat RankSorts 0 ε q (PP.quote_type k A) ->
  @typ nat RankSorts 0 ε (decode k A q) (output_type A).
Proof.
  intros HA Hq. unfold decode. eapply BP.arr_apply;
    [apply decoder_typed; exact HA | exact Hq].
Qed.

Lemma run_at_replace k m n (sigma : Fin m -> Term nat n) o p q :
  sigma o = var p ->
  replace sigma (run_at k o q) = run_at k p (replace sigma q).
Proof.
  intro Ho. unfold run_at; rewrite PT.run_replace.
  apply run_ext. intro i; apply PP.fill_replace; exact Ho.
Qed.

Theorem decoder_application k A q :
  reduces_to nat 0 (decode k A q)
    (lam (𝓤 0) (run_at k fzero (PT.lift_closed q))).
Proof.
  unfold decode, decoder. eapply rtc_step; [apply step_beta |].
  unfold subst; cbn [replace]. rewrite run_at_replace with (p := fzero) by reflexivity.
  cbn [replace transpose fin_match eq_rect].
  replace (shift q) with (@PT.lift_closed 1 q).
  - reflexivity.
  - unfold shift, PT.lift_closed. apply rename_ext; intro i; inversion i.
Qed.

Lemma filled_payload_recovers k t A (d : @EQ.derivation 1 emptyEnv fzero t A) :
  TH.rank_budget d <= k ->
  reduces_to nat 1 (replace (PP.fill k fzero) (PP.payload k d)) t.
Proof.
  intro Hk. rewrite <- (rename_id t) at 2. unfold PP.payload.
  eapply PR.quoted_substitution_recovers with (k := k).
  - exact Hk.
  - intro i. unfold PP.source_ren. rewrite PP.fill_ground.
    f_equal. dependent elimination i; [reflexivity |].
    match goal with z : Fin 0 |- _ => inversion z end.
  - intros r Hr. apply PP.fill_family; lia.
  - intros a b H. cbn [replace]. apply PP.fill_abs; exact H.
  - intros a b H. cbn [replace]. apply PP.fill_app; exact H.
Qed.

Theorem quote_strong_recovery k t A (d : @EQ.derivation 1 emptyEnv fzero t A) :
  TH.rank_budget d <= k ->
  reduces_to nat 0 (decode k A (PP.quote k d)) (lam (𝓤 0) t).
Proof.
  intro Hk. eapply rtc_trans; [apply decoder_application |].
  apply (@λ_cong_par nat (reduces_to nat) _ _ 0); [reflexivity |].
  unfold run_at, PP.quote. eapply rtc_trans; [apply PT.run_closed_term |].
  apply filled_payload_recovers; exact Hk.
Qed.

(** Closed normal PHOAS representation of the independent ChurchSTLC
    source, with actual direct typing and strong unreduced-source recovery. *)
Theorem closed_phoas_interpretation k t A (d : @EQ.derivation 1 emptyEnv fzero t A) :
  TH.rank_budget d <= k ->
  normalb (PP.quote k d) = true /\
  @typ nat RankSorts 0 ε (PP.quote k d) (PP.quote_type k A) /\
  @typ nat RankSorts 0 ε (decoder k A) (decoder_type k A) /\
  @typ nat RankSorts 0 ε (decode k A (PP.quote k d)) (output_type A) /\
  reduces_to nat 0 (decode k A (PP.quote k d)) (lam (𝓤 0) t).
Proof.
  intro Hk. assert (HA : order A <= k) by (unfold TH.rank_budget in Hk; lia).
  split; [apply PP.quote_normal |].
  split; [apply PP.quote_typed; exact Hk |].
  split; [apply decoder_typed; exact HA |].
  split; [apply decode_typed; [exact HA | apply PP.quote_typed; exact Hk] |].
  apply quote_strong_recovery; exact Hk.
Qed.

(** Executable regression: the source contains a beta redex, the actual
    finite PHOAS package is normal, and decoding recovers that redex. *)
Example beta_budget_computes : TH.rank_budget EQ.beta_source_derivation = 1.
Proof. vm_compute; reflexivity. Qed.

Example beta_source_is_reducible : normalb (lam (𝓤 0) EQ.beta_source) = false.
Proof. vm_compute; reflexivity. Qed.

Example beta_quote_normal_computes : normalb (PP.quote 1 EQ.beta_source_derivation) = true.
Proof. vm_compute; reflexivity. Qed.

Example beta_interpretation_recovers_source :
  reduces_to nat 0
    (decode 1 (arrow base base) (PP.quote 1 EQ.beta_source_derivation))
    (lam (𝓤 0) EQ.beta_source).
Proof. apply quote_strong_recovery. rewrite beta_budget_computes; reflexivity. Qed.

Print Assumptions quote_type_has_sort.
Print Assumptions run_at_typed.
Print Assumptions decoder_typed.
Print Assumptions decoder_type_has_sort.
Print Assumptions decode_typed.
Print Assumptions decoder_application.
Print Assumptions quote_strong_recovery.
Print Assumptions closed_phoas_interpretation.
Print Assumptions beta_interpretation_recovers_source.

End PHOASDecoder.
