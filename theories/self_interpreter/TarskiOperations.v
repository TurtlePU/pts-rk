From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation
  Ranks DefEq Reduction AbstractRewriting Congruence.
From PTSrk.NormalizationComplexity Require Import Morphisms Greedy.
From PTSrk.SelfInterpreter Require Import BrownPalsberg DependentPHOAS
  TarskiProducts TarskiCasts TarskiIdentity TarskiLawFamily TarskiSignature.
Import Context.

(** Actual local operations in the finite Tarski signature. The law is
    obtained by applying its polymorphic FIELD, not supplied as a new
    operation premise. These definitions do not quote source derivations. *)
Module TarskiOperations.
Module BP := BrownPalsberg.BrownPalsberg.
Module DP := DependentPHOAS.DependentPHOAS.
Module TP := TarskiProducts.TarskiProducts.
Module TC := TarskiCasts.TarskiCasts.
Module TI := TarskiIdentity.TarskiIdentity.
Module LF := TarskiLawFamily.TarskiLawFamily.
Module TS := TarskiSignature.TarskiSignature.

Definition product_code k a b (A B : Term nat (TS.width k)) :=
  app (app (TS.product k a b) A) B.
Definition product_evidence k a b (A B : Term nat (TS.width k)) :=
  app (app (TS.law k a b) A) B.
Definition decoded k a b (A B : Term nat (TS.width k)) :=
  TP.decoded_product (TS.decoder k a) (TS.decoder k b) A B.
Definition encoded k a b (A B : Term nat (TS.width k)) :=
  app (TS.decoder k (Nat.max (S a) b)) (product_code k a b A B).
Definition abstract_term k a b (A B f : Term nat (TS.width k)) :=
  TC.cast_abs a b (TS.decoder k a) (TS.decoder k b) A B
    (product_evidence k a b A B) f.
Definition application_term k a b (A B f u : Term nat (TS.width k)) :=
  TC.cast_app a b (TS.decoder k a) (TS.decoder k b) A B
    (product_evidence k a b A B) f u.

Theorem product_code_typed k a b A B : a <= k -> b <= k ->
  @typ nat RankSorts _ (TS.context k) A (TS.carrier k a) ->
  @typ nat RankSorts _ (TS.context k) B
    (TP.code_family (TS.carrier k b) (TS.decoder k a) A) ->
  @typ nat RankSorts _ (TS.context k) (product_code k a b A B)
    (TS.carrier k (Nat.max (S a) b)).
Proof.
  intros Ha Hb HA HB; unfold product_code.
  eapply TP.product_specialize; [apply TS.product_typed; assumption | exact HA | exact HB].
Qed.

Theorem product_evidence_typed k a b A B : a <= k -> b <= k ->
  @typ nat RankSorts _ (TS.context k) A (TS.carrier k a) ->
  @typ nat RankSorts _ (TS.context k) B
    (TP.code_family (TS.carrier k b) (TS.decoder k a) A) ->
  @typ nat RankSorts _ (TS.context k) (product_evidence k a b A B)
    (TC.product_law a b (TS.decoder k a) (TS.decoder k b)
      (TS.decoder k (Nat.max (S a) b)) (TS.product k a b) A B).
Proof.
  intros Ha Hb HA HB; unfold product_evidence.
  eapply LF.family_specialize; [apply TS.law_typed; assumption | exact HA | exact HB].
Qed.

Theorem product_sorts k a b A B : a <= k -> b <= k ->
  @typ nat RankSorts _ (TS.context k) A (TS.carrier k a) ->
  @typ nat RankSorts _ (TS.context k) B
    (TP.code_family (TS.carrier k b) (TS.decoder k a) A) ->
  @typ nat RankSorts _ (TS.context k) (decoded k a b A B) (𝓤 (Nat.max (S a) b)) /\
  @typ nat RankSorts _ (TS.context k) (encoded k a b A B) (𝓤 (Nat.max (S a) b)).
Proof.
  intros Ha Hb HA HB; split.
  - unfold decoded; eapply TP.decoded_product_sort.
    + apply TS.decoder_typed; lia.
    + apply TS.decoder_typed; lia.
    + exact HA.
    + exact HB.
  - unfold encoded; eapply BP.arr_apply.
    + apply TS.decoder_typed; lia.
    + apply product_code_typed; assumption.
Qed.

Theorem abstract_term_typed k a b A B f : a <= k -> b <= k ->
  @typ nat RankSorts _ (TS.context k) A (TS.carrier k a) ->
  @typ nat RankSorts _ (TS.context k) B
    (TP.code_family (TS.carrier k b) (TS.decoder k a) A) ->
  @typ nat RankSorts _ (TS.context k) f (decoded k a b A B) ->
  @typ nat RankSorts _ (TS.context k) (abstract_term k a b A B f) (encoded k a b A B).
Proof.
  intros Ha Hb HA HB Hf; unfold abstract_term, encoded, product_code.
  eapply TC.cast_abs_typed with (Ca := TS.carrier k a) (Cb := TS.carrier k b)
    (Cc := TS.carrier k (Nat.max (S a) b)).
  - apply TS.decoder_typed; lia.
  - apply TS.decoder_typed; lia.
  - apply TS.decoder_typed; lia.
  - apply TS.product_typed; assumption.
  - exact HA.
  - exact HB.
  - apply product_evidence_typed; assumption.
  - exact Hf.
Qed.

Theorem application_term_typed k a b A B f u : a <= k -> b <= k ->
  @typ nat RankSorts _ (TS.context k) A (TS.carrier k a) ->
  @typ nat RankSorts _ (TS.context k) B
    (TP.code_family (TS.carrier k b) (TS.decoder k a) A) ->
  @typ nat RankSorts _ (TS.context k) f (encoded k a b A B) ->
  @typ nat RankSorts _ (TS.context k) u (app (TS.decoder k a) A) ->
  @typ nat RankSorts _ (TS.context k) (application_term k a b A B f u)
    (app (TS.decoder k b) (app B u)).
Proof.
  intros Ha Hb HA HB Hf Hu; unfold application_term.
  eapply TC.cast_app_typed with (Ca := TS.carrier k a) (Cb := TS.carrier k b)
    (Cc := TS.carrier k (Nat.max (S a) b))
    (Ec := TS.decoder k (Nat.max (S a) b)) (p := TS.product k a b).
  - apply TS.decoder_typed; lia.
  - apply TS.decoder_typed; lia.
  - apply TS.decoder_typed; lia.
  - apply TS.product_typed; assumption.
  - exact HA.
  - exact HB.
  - apply product_evidence_typed; assumption.
  - exact Hf.
  - exact Hu.
Qed.

Lemma decoded_product_replace m n (sigma : Fin m -> Term nat n) Ea Eb A B :
  replace sigma (TP.decoded_product Ea Eb A B) =
  TP.decoded_product (replace sigma Ea) (replace sigma Eb) (replace sigma A) (replace sigma B).
Proof. unfold TP.decoded_product, DP.product; syntax_simp. Qed.

Lemma cast_abs_replace a b m n (sigma : Fin m -> Term nat n) Ea Eb A B e f :
  replace sigma (TC.cast_abs a b Ea Eb A B e f) =
  TC.cast_abs a b (replace sigma Ea) (replace sigma Eb) (replace sigma A)
    (replace sigma B) (replace sigma e) (replace sigma f).
Proof.
  unfold TC.cast_abs; cbn [replace].
  rewrite (proj1 (TC.casts_replace _ m n sigma _ _)), decoded_product_replace; reflexivity.
Qed.

Lemma cast_app_replace a b m n (sigma : Fin m -> Term nat n) Ea Eb A B e f u :
  replace sigma (TC.cast_app a b Ea Eb A B e f u) =
  TC.cast_app a b (replace sigma Ea) (replace sigma Eb) (replace sigma A)
    (replace sigma B) (replace sigma e) (replace sigma f) (replace sigma u).
Proof.
  unfold TC.cast_app; cbn [replace].
  rewrite (proj2 (TC.casts_replace _ m n sigma _ _)), decoded_product_replace; reflexivity.
Qed.

Lemma cast_abs_law_reduces a b n (Ea Eb A B e e' f : Term nat n) :
  reduces_to nat n e e' ->
  reduces_to nat n (TC.cast_abs a b Ea Eb A B e f) (TC.cast_abs a b Ea Eb A B e' f).
Proof.
  intro He; unfold TC.cast_abs, TC.forward.
  do 3 apply (@app_cong_l nat (reduces_to nat) _ n); exact He.
Qed.

Lemma cast_app_law_reduces a b n (Ea Eb A B e e' f u : Term nat n) :
  reduces_to nat n e e' ->
  reduces_to nat n (TC.cast_app a b Ea Eb A B e f u) (TC.cast_app a b Ea Eb A B e' f u).
Proof.
  intro He; unfold TC.cast_app, TC.backward.
  do 4 apply (@app_cong_l nat (reduces_to nat) _ n); exact He.
Qed.

Theorem product_code_normal k a b A B :
  normalb A = true -> normalb B = true -> normalb (product_code k a b A B) = true.
Proof.
  intros HA HB. assert (HP : normalb (TS.product k a b) = true) by reflexivity.
  assert (HN : isLambda (TS.product k a b) = false) by reflexivity.
  unfold product_code; cbn [normalb isLambda]; now rewrite HP, HN, HA, HB.
Qed.

Theorem product_evidence_normal k a b A B :
  normalb A = true -> normalb B = true -> normalb (product_evidence k a b A B) = true.
Proof.
  intros HA HB. assert (HP : normalb (TS.law k a b) = true) by reflexivity.
  assert (HN : isLambda (TS.law k a b) = false) by reflexivity.
  unfold product_evidence; cbn [normalb isLambda]; now rewrite HP, HN, HA, HB.
Qed.

(** The decoded annotation is an EXPLICIT normality premise. In particular
    normality of B alone does not imply normality of B x when B is a lambda.
    These local lemmas do not assert arbitrary dependent quotation normality. *)
Theorem abstract_term_normal k a b A B f :
  normalb A = true -> normalb B = true -> normalb (decoded k a b A B) = true ->
  normalb f = true -> normalb (abstract_term k a b A B f) = true.
Proof.
  intros HA HB HD Hf; unfold abstract_term, TC.cast_abs.
  apply (proj1 (TC.neutral_casts_normal _ _ _ _ f HD
    (product_evidence_normal k a b A B HA HB) eq_refl Hf)).
Qed.

Theorem application_term_normal k a b A B f u :
  normalb A = true -> normalb B = true -> normalb (decoded k a b A B) = true ->
  normalb f = true -> normalb u = true -> normalb (application_term k a b A B f u) = true.
Proof.
  intros HA HB HD Hf Hu.
  pose proof (proj2 (TC.neutral_casts_normal (Nat.max (S a) b) _ _ _ f HD
    (product_evidence_normal k a b A B HA HB) eq_refl Hf)) as H.
  change (normalb (app (app (TC.backward (Nat.max (S a) b) (decoded k a b A B)
    (product_evidence k a b A B)) f) u) = true).
  change (normalb (app (TC.backward (Nat.max (S a) b) (decoded k a b A B)
    (product_evidence k a b A B)) f) && normalb u && negb false = true).
  now rewrite H, Hu.
Qed.

(** Strong computation after the ACTUAL finite simultaneous substitution.
    Inputs need not be normal or typed; no precomputed semantic value is
    carried. All source-input redexes are retained in the stated reducts. *)
Theorem product_code_recovers k a b n (A B : Term nat (TS.width k)) :
  a <= k -> b <= k ->
  reduces_to nat n (replace (@TS.fill k n) (product_code k a b A B))
    (DP.plain_product (replace (TS.fill k) A) (replace (TS.fill k) B)).
Proof.
  intros Ha Hb; unfold product_code; cbn [replace].
  rewrite TS.fill_product by assumption. apply TP.identity_product_specializes.
Qed.

Theorem product_evidence_recovers k a b n (A B : Term nat (TS.width k)) :
  a <= k -> b <= k ->
  reduces_to nat n (replace (@TS.fill k n) (product_evidence k a b A B))
    (TI.identity_law a b (replace (TS.fill k) A) (replace (TS.fill k) B)).
Proof.
  intros Ha Hb; unfold product_evidence; cbn [replace].
  rewrite TS.fill_law by assumption. apply LF.identity_family_specializes.
Qed.

Theorem decoded_recovers k a b n (A B : Term nat (TS.width k)) :
  a <= k -> b <= k ->
  reduces_to nat n (replace (@TS.fill k n) (decoded k a b A B))
    (DP.plain_product (replace (TS.fill k) A) (replace (TS.fill k) B)).
Proof.
  intros Ha Hb; unfold decoded; rewrite decoded_product_replace.
  rewrite !TS.fill_decoder by lia. apply TP.decoded_product_identity_recovers.
Qed.

Theorem encoded_recovers k a b n (A B : Term nat (TS.width k)) :
  a <= k -> b <= k ->
  reduces_to nat n (replace (@TS.fill k n) (encoded k a b A B))
    (DP.plain_product (replace (TS.fill k) A) (replace (TS.fill k) B)).
Proof.
  intros Ha Hb; unfold encoded; cbn [replace].
  rewrite TS.fill_decoder by lia.
  eapply rtc_step; [apply BP.type_identity_beta | apply product_code_recovers; assumption].
Qed.

Theorem abstract_term_recovers k a b n (A B f : Term nat (TS.width k)) :
  a <= k -> b <= k ->
  reduces_to nat n (replace (@TS.fill k n) (abstract_term k a b A B f))
    (replace (TS.fill k) f).
Proof.
  intros Ha Hb; unfold abstract_term; rewrite cast_abs_replace.
  rewrite !TS.fill_decoder by lia.
  eapply rtc_trans with (y := TI.identity_abs a b (replace (TS.fill k) A)
    (replace (TS.fill k) B) (replace (TS.fill k) f)).
  - apply cast_abs_law_reduces, product_evidence_recovers; assumption.
  - apply TI.identity_abs_recovers.
Qed.

Theorem application_term_recovers k a b n (A B f u : Term nat (TS.width k)) :
  a <= k -> b <= k ->
  reduces_to nat n (replace (@TS.fill k n) (application_term k a b A B f u))
    (app (replace (TS.fill k) f) (replace (TS.fill k) u)).
Proof.
  intros Ha Hb; unfold application_term; rewrite cast_app_replace.
  rewrite !TS.fill_decoder by lia.
  eapply rtc_trans with (y := TI.identity_app a b (replace (TS.fill k) A)
    (replace (TS.fill k) B) (replace (TS.fill k) f) (replace (TS.fill k) u)).
  - apply cast_app_law_reduces, product_evidence_recovers; assumption.
  - apply TI.identity_app_recovers.
Qed.

Print Assumptions product_code_typed.
Print Assumptions product_evidence_typed.
Print Assumptions product_sorts.
Print Assumptions abstract_term_typed.
Print Assumptions application_term_typed.
Print Assumptions product_code_normal.
Print Assumptions product_evidence_normal.
Print Assumptions abstract_term_normal.
Print Assumptions application_term_normal.
Print Assumptions product_code_recovers.
Print Assumptions product_evidence_recovers.
Print Assumptions decoded_recovers.
Print Assumptions encoded_recovers.
Print Assumptions abstract_term_recovers.
Print Assumptions application_term_recovers.
End TarskiOperations.
