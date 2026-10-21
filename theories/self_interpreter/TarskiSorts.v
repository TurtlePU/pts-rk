From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation
  Ranks DefEq Reduction AbstractRewriting Congruence.
From PTSrk.NormalizationComplexity Require Import Greedy Morphisms.
From PTSrk.SelfInterpreter Require Import BrownPalsberg TarskiCasts
  TarskiUniverses TarskiSignature PHOASTelescope.
Import Context.

(** Sorts and the code/represented-type interface in the ACTUAL finite
    signature. Abstract universe laws are used through explicit object
    casts; their endpoints are not silently identified by conversion. *)
Module TarskiSorts.
Module BP := BrownPalsberg.BrownPalsberg.
Module TC := TarskiCasts.TarskiCasts.
Module TU := TarskiUniverses.TarskiUniverses.
Module TS := TarskiSignature.TarskiSignature.
Module PT := PHOASTelescope.PHOASTelescope.

Definition decoded_universe k r : Term nat (TS.width k) :=
  app (TS.decoder k 0) (TS.universe k r).

(** The law points FROM El0(u_r) TO C_r; hence a type code is viewed as
    a represented term at universe u_r using the BACKWARD cast. *)
Definition code_to_term k r (A : Term nat (TS.width k)) :=
  app (TC.backward 0 (decoded_universe k r) (TS.universe_law k r)) A.
Definition term_to_code k r (t : Term nat (TS.width k)) :=
  app (TC.forward 0 (decoded_universe k r) (TS.universe_law k r)) t.

Theorem decoded_universe_sort k r : r <= S k ->
  @typ nat RankSorts _ (TS.context k) (decoded_universe k r) (𝓤 0).
Proof.
  intro Hr; unfold decoded_universe. eapply BP.arr_apply.
  - apply TS.decoder_typed; lia.
  - apply TS.universe_typed; exact Hr.
Qed.

Theorem universe_casts_typed k r : r <= S k ->
  @typ nat RankSorts _ (TS.context k)
    (TC.forward 0 (decoded_universe k r) (TS.universe_law k r))
    (BP.arr (decoded_universe k r) (TS.carrier k r)) /\
  @typ nat RankSorts _ (TS.context k)
    (TC.backward 0 (decoded_universe k r) (TS.universe_law k r))
    (BP.arr (TS.carrier k r) (decoded_universe k r)).
Proof.
  intro Hr; unfold decoded_universe. apply TC.universe_casts_typed with (C0 := TS.carrier k 0).
  - apply TS.carrier_typed; exact Hr.
  - apply TS.decoder_typed; lia.
  - apply TS.universe_typed; exact Hr.
  - apply TS.universe_law_typed; exact Hr.
Qed.

Theorem universe_cast_types_sort k r : r <= S k ->
  @typ nat RankSorts _ (TS.context k)
    (BP.arr (decoded_universe k r) (TS.carrier k r)) (𝓤 1) /\
  @typ nat RankSorts _ (TS.context k)
    (BP.arr (TS.carrier k r) (decoded_universe k r)) (𝓤 1).
Proof.
  intro Hr; replace 1 with (Nat.max (S 0) 0) by reflexivity; split;
    apply BP.arr_sort; try (apply TS.carrier_typed; exact Hr);
    apply decoded_universe_sort; exact Hr.
Qed.

Theorem code_to_term_typed k r A : r <= S k ->
  @typ nat RankSorts _ (TS.context k) A (TS.carrier k r) ->
  @typ nat RankSorts _ (TS.context k) (code_to_term k r A) (decoded_universe k r).
Proof.
  intros Hr HA; unfold code_to_term; eapply BP.arr_apply;
    [apply (proj2 (universe_casts_typed k r Hr)) | exact HA].
Qed.

Theorem term_to_code_typed k r t : r <= S k ->
  @typ nat RankSorts _ (TS.context k) t (decoded_universe k r) ->
  @typ nat RankSorts _ (TS.context k) (term_to_code k r t) (TS.carrier k r).
Proof.
  intros Hr Ht; unfold term_to_code; eapply BP.arr_apply;
    [apply (proj1 (universe_casts_typed k r Hr)) | exact Ht].
Qed.

Lemma decoded_universe_normal k r : normalb (decoded_universe k r) = true.
Proof. reflexivity. Qed.

Theorem code_to_term_normal k r A :
  normalb A = true -> normalb (code_to_term k r A) = true.
Proof.
  intro HA; unfold code_to_term.
  apply (proj2 (TC.neutral_casts_normal 0 _ (decoded_universe k r) (TS.universe_law k r) A
    (decoded_universe_normal k r) eq_refl eq_refl HA)).
Qed.

Theorem term_to_code_normal k r t :
  normalb t = true -> normalb (term_to_code k r t) = true.
Proof.
  intro Ht; unfold term_to_code.
  apply (proj1 (TC.neutral_casts_normal 0 _ (decoded_universe k r) (TS.universe_law k r) t
    (decoded_universe_normal k r) eq_refl eq_refl Ht)).
Qed.

Theorem decoded_universe_recovers k r n : r <= S k ->
  reduces_to nat n (replace (@TS.fill k n) (decoded_universe k r)) (𝓤 r).
Proof.
  intro Hr; unfold decoded_universe; cbn [replace].
  rewrite TS.fill_decoder, TS.fill_universe by lia.
  apply rtc_in, BP.type_identity_beta.
Qed.

Theorem code_to_term_recovers k r n (A : Term nat (TS.width k)) : r <= S k ->
  reduces_to nat n (replace (@TS.fill k n) (code_to_term k r A)) (replace (TS.fill k) A).
Proof.
  intro Hr; unfold code_to_term; cbn [replace].
  rewrite (proj2 (TC.casts_replace 0 _ n (TS.fill k) _ _)).
  unfold decoded_universe; cbn [replace].
  rewrite TS.fill_decoder, TS.fill_universe, TS.fill_universe_law by lia.
  apply (proj2 (TC.identity_universe_casts_recover r n (replace (TS.fill k) A))).
Qed.

Theorem term_to_code_recovers k r n (t : Term nat (TS.width k)) : r <= S k ->
  reduces_to nat n (replace (@TS.fill k n) (term_to_code k r t)) (replace (TS.fill k) t).
Proof.
  intro Hr; unfold term_to_code; cbn [replace].
  rewrite (proj1 (TC.casts_replace 0 _ n (TS.fill k) _ _)).
  unfold decoded_universe; cbn [replace].
  rewrite TS.fill_decoder, TS.fill_universe, TS.fill_universe_law by lia.
  apply (proj1 (TC.identity_universe_casts_recover r n (replace (TS.fill k) t))).
Qed.

(** This is the original axiom U_r : U_0: u_r is a code in C0 and must
    be cast using law ZERO to become a term in El0(u_0). Using law r here
    would generally be ill typed. *)
Definition sort_quote k r := code_to_term k 0 (TS.universe k r).

Theorem sort_quote_typed k r : r <= S k ->
  @typ nat RankSorts _ (TS.context k) (sort_quote k r) (decoded_universe k 0).
Proof. intro Hr; apply code_to_term_typed; [lia | apply TS.universe_typed; exact Hr]. Qed.

Theorem sort_quote_normal k r : normalb (sort_quote k r) = true.
Proof. apply code_to_term_normal; reflexivity. Qed.

Theorem sort_quote_recovers k r n : r <= S k ->
  reduces_to nat n (replace (@TS.fill k n) (sort_quote k r)) (𝓤 r).
Proof.
  intro Hr; unfold sort_quote.
  eapply rtc_trans; [apply code_to_term_recovers; lia |].
  rewrite TS.fill_universe by exact Hr; reflexivity.
Qed.

Definition closed_sort_quote k r := TS.close k (sort_quote k r).

Theorem closed_sort_quote_typed k r : r <= S k ->
  @typ nat RankSorts 0 ε (closed_sort_quote k r) (TS.closed_type k (decoded_universe k 0)).
Proof. intro Hr; apply TS.close_typed, sort_quote_typed; exact Hr. Qed.

Theorem closed_sort_quote_normal k r : normalb (closed_sort_quote k r) = true.
Proof. apply TS.close_normal, sort_quote_normal. Qed.

Lemma lift_closed_typing n (G : Ctx nat n) q T :
  @typ nat RankSorts 0 ε q T ->
  @typ nat RankSorts n G (PT.lift_closed q) (PT.lift_closed T).
Proof.
  intro Hq; unfold PT.lift_closed; eapply typing_rename with (G := ε);
    [intro i; inversion i | exact Hq].
Qed.

(** Direct typing of the actual identity application, independently of its
    reduction to the source sort. This is not subject expansion. *)
Theorem closed_sort_run_typed k r n (G : Ctx nat n) : r <= S k ->
  @typ nat RankSorts n G
    (TS.identity_run k (@PT.lift_closed n (closed_sort_quote k r))) (𝓤 0).
Proof.
  intro Hr; eapply typ_conv with
    (T := replace (@TS.fill k n) (decoded_universe k 0)) (ℓ := 0).
  - apply TS.identity_run_typed, lift_closed_typing, closed_sort_quote_typed; exact Hr.
  - constructor; reflexivity.
  - apply def_equiv_prop; exists (𝓤 0); split;
      [apply decoded_universe_recovers; lia | reflexivity].
Qed.

Theorem closed_sort_quote_recovers k r n : r <= S k ->
  reduces_to nat n
    (TS.identity_run k (@PT.lift_closed n (closed_sort_quote k r))) (𝓤 r).
Proof.
  intro Hr; eapply rtc_trans; [apply TS.identity_run_closed | apply sort_quote_recovers; exact Hr].
Qed.

Print Assumptions decoded_universe_sort.
Print Assumptions universe_casts_typed.
Print Assumptions universe_cast_types_sort.
Print Assumptions code_to_term_typed.
Print Assumptions term_to_code_typed.
Print Assumptions code_to_term_normal.
Print Assumptions term_to_code_normal.
Print Assumptions decoded_universe_recovers.
Print Assumptions code_to_term_recovers.
Print Assumptions term_to_code_recovers.
Print Assumptions sort_quote_typed.
Print Assumptions sort_quote_normal.
Print Assumptions sort_quote_recovers.
Print Assumptions closed_sort_quote_typed.
Print Assumptions closed_sort_quote_normal.
Print Assumptions closed_sort_run_typed.
Print Assumptions closed_sort_quote_recovers.
End TarskiSorts.
