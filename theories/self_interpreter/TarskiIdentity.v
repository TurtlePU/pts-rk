From Stdlib Require Import Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation
  Ranks DefEq Reduction AbstractRewriting Congruence.
From PTSrk.NormalizationComplexity Require Import Greedy.
From PTSrk.SelfInterpreter Require Import BrownPalsberg DependentPHOAS
  IndexedEquality TarskiProducts TarskiCasts.
Import Context.

(** Concrete identity interpretation of the local Tarski product algebra.
    The equality law below is an actual ORIGINAL term, not a law premise.
    No source normal form, semantic payload or eta principle is supplied. *)
Module TarskiIdentity.
Module BP := BrownPalsberg.BrownPalsberg.
Module DP := DependentPHOAS.DependentPHOAS.
Module IE := IndexedEquality.IndexedEquality.
Module TP := TarskiProducts.TarskiProducts.
Module TC := TarskiCasts.TarskiCasts.

Lemma eq_type_reduces b n (A u u' v v' : Term nat n) :
  reduces_to nat n u u' -> reduces_to nat n v v' ->
  reduces_to nat n (IE.eq_type b A u v) (IE.eq_type b A u' v').
Proof.
  intros Hu Hv; unfold IE.eq_type.
  apply (@Π_cong_par nat (reduces_to nat) _ _ n); [reflexivity |].
  apply BP.arr_reduces;
    apply (@app_cong_par nat (reduces_to nat) _ _ (S n));
    try reflexivity; apply rename_rtc; assumption.
Qed.

Definition identity_law a b {n} (A B : Term nat n) :=
  IE.refl_case (S (Nat.max (S a) b)) (𝓤 (Nat.max (S a) b))
    (DP.plain_product A B).

Lemma identity_family_typed a b n (G : Ctx nat n) A B :
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G B (BP.arr A (𝓤 b)) ->
  @typ nat RankSorts n G B
    (TP.code_family (𝓤 b) (BP.type_identity a) A).
Proof.
  intros HA HB; eapply typ_conv with (T := BP.arr A (𝓤 b)) (ℓ := S a).
  - exact HB.
  - eapply TP.code_family_sort with (Ca := 𝓤 a).
    + constructor; reflexivity.
    + apply BP.type_identity_typing.
    + exact HA.
  - apply def_equiv_prop; exists (BP.arr A (𝓤 b)); split; [reflexivity |].
    unfold TP.code_family. apply BP.arr_reduces; [apply rtc_in, BP.type_identity_beta | reflexivity].
Qed.

Lemma identity_product_law_sort a b n (G : Ctx nat n) A B :
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G B (BP.arr A (𝓤 b)) ->
  @typ nat RankSorts n G
    (TC.product_law a b (BP.type_identity a) (BP.type_identity b)
      (BP.type_identity (Nat.max (S a) b)) (TP.identity_product a b) A B)
    (𝓤 (Nat.max (S a) b + 2)).
Proof.
  intros HA HB.
  eapply TC.product_law_sort with (Ca := 𝓤 a) (Cb := 𝓤 b)
    (Cc := 𝓤 (Nat.max (S a) b)).
  - apply BP.type_identity_typing.
  - apply BP.type_identity_typing.
  - apply BP.type_identity_typing.
  - apply TP.identity_product_typed.
  - exact HA.
  - apply identity_family_typed; assumption.
Qed.

Theorem identity_law_typed a b n (G : Ctx nat n) A B :
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G B (BP.arr A (𝓤 b)) ->
  @typ nat RankSorts n G (identity_law a b A B)
    (TC.product_law a b (BP.type_identity a) (BP.type_identity b)
      (BP.type_identity (Nat.max (S a) b)) (TP.identity_product a b) A B).
Proof.
  intros HA HB.
  eapply typ_conv with
    (T := IE.eq_type (S (Nat.max (S a) b)) (𝓤 (Nat.max (S a) b))
      (DP.plain_product A B) (DP.plain_product A B))
    (ℓ := Nat.max (S a) b + 2).
  - unfold identity_law. apply IE.refl_case_typed with (a := 0).
    + constructor; reflexivity.
    + eapply DP.plain_product_sort; eassumption.
  - apply identity_product_law_sort; assumption.
  - apply def_equiv_prop; exists (IE.eq_type (S (Nat.max (S a) b))
      (𝓤 (Nat.max (S a) b)) (DP.plain_product A B) (DP.plain_product A B)).
    split; [reflexivity |]. unfold TC.product_law, TC.type_law.
    apply eq_type_reduces.
    + apply TP.decoded_product_identity_recovers.
    + eapply rtc_step; [apply BP.type_identity_beta | apply TP.identity_product_specializes].
Qed.

Lemma identity_decoded_sort a b n (G : Ctx nat n) A B :
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G B (BP.arr A (𝓤 b)) ->
  @typ nat RankSorts n G
    (TP.decoded_product (BP.type_identity a) (BP.type_identity b) A B)
    (𝓤 (Nat.max (S a) b)).
Proof.
  intros HA HB; eapply TP.decoded_product_sort with (Ca := 𝓤 a) (Cb := 𝓤 b).
  - apply BP.type_identity_typing.
  - apply BP.type_identity_typing.
  - exact HA.
  - apply identity_family_typed; assumption.
Qed.

Lemma identity_encoded_sort a b n (G : Ctx nat n) A B :
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G B (BP.arr A (𝓤 b)) ->
  @typ nat RankSorts n G
    (app (BP.type_identity (Nat.max (S a) b))
      (app (app (TP.identity_product a b) A) B))
    (𝓤 (Nat.max (S a) b)).
Proof.
  intros HA HB; eapply BP.arr_apply.
  - apply BP.type_identity_typing.
  - eapply TP.product_specialize with (Ca := 𝓤 a) (Cb := 𝓤 b)
      (Ea := BP.type_identity a).
    + apply TP.identity_product_typed.
    + exact HA.
    + apply identity_family_typed; assumption.
Qed.

Lemma identity_encoded_reduces a b n (A B : Term nat n) :
  reduces_to nat n (app (BP.type_identity (Nat.max (S a) b))
      (app (app (TP.identity_product a b) A) B)) (DP.plain_product A B).
Proof.
  eapply rtc_step; [apply BP.type_identity_beta | apply TP.identity_product_specializes].
Qed.

Lemma convert_to_reduct n (G : Ctx nat n) t T V r :
  @typ nat RankSorts n G t V -> @typ nat RankSorts n G T (𝓤 r) ->
  reduces_to nat n T V -> @typ nat RankSorts n G t T.
Proof.
  intros Ht HT Hred; eapply typ_conv; [exact Ht | exact HT |].
  apply def_equiv_prop; exists V; split; [reflexivity | exact Hred].
Qed.

Definition identity_abs a b {n} (A B f : Term nat n) :=
  TC.cast_abs a b (BP.type_identity a) (BP.type_identity b) A B
    (identity_law a b A B) f.
Definition identity_app a b {n} (A B f u : Term nat n) :=
  TC.cast_app a b (BP.type_identity a) (BP.type_identity b) A B
    (identity_law a b A B) f u.

(** The typing derivations below use the constructed law and the original
    application/conversion rules, not subject expansion from recovery. *)
Theorem identity_abs_typed a b n (G : Ctx nat n) A B f :
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G B (BP.arr A (𝓤 b)) ->
  @typ nat RankSorts n G f (DP.plain_product A B) ->
  @typ nat RankSorts n G (identity_abs a b A B f) (DP.plain_product A B).
Proof.
  intros HA HB Hf; eapply typ_conv with
    (T := app (BP.type_identity (Nat.max (S a) b))
      (app (app (TP.identity_product a b) A) B)) (ℓ := Nat.max (S a) b).
  - unfold identity_abs. eapply TC.cast_abs_typed with
      (Ca := 𝓤 a) (Cb := 𝓤 b) (Cc := 𝓤 (Nat.max (S a) b)).
    + apply BP.type_identity_typing.
    + apply BP.type_identity_typing.
    + apply BP.type_identity_typing.
    + apply TP.identity_product_typed.
    + exact HA.
    + apply identity_family_typed; assumption.
    + apply identity_law_typed; assumption.
    + eapply convert_to_reduct; [exact Hf | apply identity_decoded_sort; eassumption |].
      apply TP.decoded_product_identity_recovers.
  - eapply DP.plain_product_sort; eassumption.
  - apply def_equiv_prop; exists (DP.plain_product A B); split;
      [apply identity_encoded_reduces | reflexivity].
Qed.

Theorem identity_app_typed a b n (G : Ctx nat n) A B f u :
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G B (BP.arr A (𝓤 b)) ->
  @typ nat RankSorts n G f (DP.plain_product A B) ->
  @typ nat RankSorts n G u A ->
  @typ nat RankSorts n G (identity_app a b A B f u) (app B u).
Proof.
  intros HA HB Hf Hu; eapply typ_conv with
    (T := app (BP.type_identity b) (app B u)) (ℓ := b).
  - unfold identity_app. eapply TC.cast_app_typed with
      (Ca := 𝓤 a) (Cb := 𝓤 b) (Cc := 𝓤 (Nat.max (S a) b))
      (Ec := BP.type_identity (Nat.max (S a) b)) (p := TP.identity_product a b).
    + apply BP.type_identity_typing.
    + apply BP.type_identity_typing.
    + apply BP.type_identity_typing.
    + apply TP.identity_product_typed.
    + exact HA.
    + apply identity_family_typed; assumption.
    + apply identity_law_typed; assumption.
    + eapply convert_to_reduct; [exact Hf | apply identity_encoded_sort; eassumption |].
      apply identity_encoded_reduces.
    + eapply convert_to_reduct with (r := a); [exact Hu | |].
      * eapply BP.arr_apply; [apply BP.type_identity_typing | exact HA].
      * apply rtc_in, BP.type_identity_beta.
  - eapply BP.arr_apply; eassumption.
  - apply def_equiv_prop; exists (app B u); split;
      [apply rtc_in, BP.type_identity_beta | reflexivity].
Qed.

Theorem identity_abs_recovers a b n (A B f : Term nat n) :
  reduces_to nat n (identity_abs a b A B f) f.
Proof.
  unfold identity_abs, identity_law, TC.cast_abs.
  apply (proj1 (TC.cast_application_reflexivity _ n _ _ f)).
Qed.

Theorem identity_app_recovers a b n (A B f u : Term nat n) :
  reduces_to nat n (identity_app a b A B f u) (app f u).
Proof.
  unfold identity_app, identity_law, TC.cast_app.
  apply (@app_cong_par nat (reduces_to nat) _ _ n); [| reflexivity].
  apply (proj2 (TC.cast_application_reflexivity _ n _ _ f)).
Qed.

Print Assumptions identity_law_typed.
Print Assumptions identity_product_law_sort.
Print Assumptions identity_abs_typed.
Print Assumptions identity_app_typed.
Print Assumptions identity_abs_recovers.
Print Assumptions identity_app_recovers.
End TarskiIdentity.
