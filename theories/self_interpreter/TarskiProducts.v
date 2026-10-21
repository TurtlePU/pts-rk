From Stdlib Require Import Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation
  Ranks DefEq Reduction AbstractRewriting Congruence.
From PTSrk.NormalizationComplexity Require Import Greedy.
From PTSrk.SelfInterpreter Require Import BrownPalsberg DependentPHOAS.
Import Context.

(** Actual original-PTS product-code operations for externally rank-indexed
    Tarski carriers. The code carriers and decoders are explicit object
    parameters; no recursive dependent quotation or conversion-coherence
    theorem is assumed. The closed identity constructor is built below. *)
Module TarskiProducts.
Module BP := BrownPalsberg.BrownPalsberg.
Module DP := DependentPHOAS.DependentPHOAS.

Definition code_family {n} (Cb Ea A : Term nat n) :=
  BP.arr (app Ea A) Cb.

Definition product_type {n} (Ca Cb Cc Ea : Term nat n) :=
  Π Ca (BP.arr (code_family (shift Cb) (shift Ea) (var fzero)) (shift Cc)).

Definition decoded_product {n} (Ea Eb A B : Term nat n) :=
  DP.product Ea Eb A B.

Lemma code_family_shift n (Cb Ea A : Term nat n) :
  shift (code_family Cb Ea A) = code_family (shift Cb) (shift Ea) (shift A).
Proof. unfold code_family; rewrite BP.arr_shift; reflexivity. Qed.

Lemma code_family_sort a n (G : Ctx nat n) Ca Cb Ea A :
  @typ nat RankSorts n G Cb (𝓤 0) ->
  @typ nat RankSorts n G Ea (BP.arr Ca (𝓤 a)) ->
  @typ nat RankSorts n G A Ca ->
  @typ nat RankSorts n G (code_family Cb Ea A) (𝓤 (S a)).
Proof.
  intros HC HE HA; unfold code_family.
  replace (S a) with (Nat.max (S a) 0) by lia.
  apply BP.arr_sort; [eapply BP.arr_apply; eassumption | exact HC].
Qed.

(** The constructor's type sort is a+2, independent of b and of the result
    index c: all code carriers have sort U0. This uses no cumulativity. *)
Theorem product_type_sort a n (G : Ctx nat n) Ca Cb Cc Ea :
  @typ nat RankSorts n G Ca (𝓤 0) ->
  @typ nat RankSorts n G Cb (𝓤 0) ->
  @typ nat RankSorts n G Cc (𝓤 0) ->
  @typ nat RankSorts n G Ea (BP.arr Ca (𝓤 a)) ->
  @typ nat RankSorts n G (product_type Ca Cb Cc Ea) (𝓤 (a+2)).
Proof.
  intros HA HB HC HE; unfold product_type.
  eapply typ_Π with (ℓₜ := 0) (ℓᵤ := S (S a)); [exact HA | | cbn; lia].
  replace (S (S a)) with (Nat.max (S (S a)) 0) by lia.
  apply BP.arr_sort.
  - eapply code_family_sort with (Ca := shift Ca).
    + change (typ (G & Ca) (shift Cb) (shift (𝓤 0))); apply weakening; exact HB.
    + change (typ (G & Ca) (shift Ea) (BP.arr (shift Ca) (shift (𝓤 a)))).
      rewrite <- BP.arr_shift. apply weakening; exact HE.
    + change (typ (G & Ca) (var fzero) ((G & Ca) !! fzero)); constructor.
  - change (typ (G & Ca) (shift Cc) (shift (𝓤 0))); apply weakening; exact HC.
Qed.

Theorem product_specialize n (G : Ctx nat n) Ca Cb Cc Ea p A B :
  @typ nat RankSorts n G p (product_type Ca Cb Cc Ea) ->
  @typ nat RankSorts n G A Ca ->
  @typ nat RankSorts n G B (code_family Cb Ea A) ->
  @typ nat RankSorts n G (app (app p A) B) Cc.
Proof.
  intros Hp HA HB; unfold product_type in Hp.
  pose proof (typ_app Ca Hp HA) as Hfirst.
  assert (Hsub : subst (BP.arr
      (code_family (shift Cb) (shift Ea) (var fzero)) (shift Cc)) A =
      BP.arr (code_family Cb Ea A) Cc).
  { unfold code_family, BP.arr; syntax_simp. unfold shift; syntax_simp.
    rewrite !BP.replace_fsucc; reflexivity. }
  rewrite Hsub in Hfirst. eapply BP.arr_apply; eassumption.
Qed.

(** In contrast with the earlier same-universe families, Ea and Eb decode
    arbitrary carriers Ca and Cb, both of sort U0. The represented body
    B is genuinely dependent on an inhabitant of Ea A. *)
Theorem decoded_product_sort a b n (G : Ctx nat n) Ca Cb Ea Eb A B :
  @typ nat RankSorts n G Ea (BP.arr Ca (𝓤 a)) ->
  @typ nat RankSorts n G Eb (BP.arr Cb (𝓤 b)) ->
  @typ nat RankSorts n G A Ca ->
  @typ nat RankSorts n G B (code_family Cb Ea A) ->
  @typ nat RankSorts n G (decoded_product Ea Eb A B)
    (𝓤 (Nat.max (S a) b)).
Proof.
  intros HE HF HA HB; unfold decoded_product, DP.product.
  eapply typ_Π with (ℓₜ := a) (ℓᵤ := b).
  - eapply BP.arr_apply; eassumption.
  - eapply BP.arr_apply with (A := shift Cb).
    + change (typ (G & app Ea A) (shift Eb) (BP.arr (shift Cb) (shift (𝓤 b)))).
      rewrite <- BP.arr_shift; apply weakening; exact HF.
    + eapply BP.arr_apply with (A := shift (app Ea A)).
      * change (typ (G & app Ea A) (shift B)
          (BP.arr (shift (app Ea A)) (shift Cb))).
        rewrite <- BP.arr_shift; apply weakening; exact HB.
      * change (typ (G & app Ea A) (var fzero) ((G & app Ea A) !! fzero)); constructor.
  - reflexivity.
Qed.

Definition plain_product_type a b {n} : Term nat n :=
  Π (𝓤 a) (BP.arr (BP.arr (var fzero) (𝓤 b)) (𝓤 (Nat.max (S a) b))).

Definition identity_product a b {n} : Term nat n :=
  lam (𝓤 a) (lam (BP.arr (var fzero) (𝓤 b))
    (DP.plain_product (var (fsucc fzero)) (var fzero))).

Lemma identity_product_plain_typed a b n (G : Ctx nat n) :
  @typ nat RankSorts n G (identity_product a b) (plain_product_type a b).
Proof.
  set (GA := G & 𝓤 a).
  set (BA := @BP.arr (S n) (var fzero) (𝓤 b)).
  assert (HA : typ GA (var fzero) (𝓤 a)).
  { change (typ GA (var fzero) (GA !! fzero)); constructor. }
  assert (HBA : typ GA BA (𝓤 (S a))).
  { unfold BA; replace (S a) with (Nat.max (S a) 0) by lia.
    apply BP.arr_sort; [exact HA | constructor; reflexivity]. }
  assert (HA' : typ (GA & BA) (var (fsucc fzero)) (𝓤 a)).
  { change (typ (GA & BA) (shift (var fzero)) (shift (𝓤 a))); apply weakening; exact HA. }
  assert (HB : typ (GA & BA) (var fzero) (BP.arr (var (fsucc fzero)) (𝓤 b))).
  { change (typ (GA & BA) (var fzero) (BP.arr (shift (var fzero)) (shift (𝓤 b)))).
    rewrite <- BP.arr_shift.
    change (typ (GA & BA) (var fzero) ((GA & BA) !! fzero)); constructor. }
  unfold identity_product, plain_product_type, BP.arr at 1.
  apply typ_λ with (ℓ := 0); [constructor; reflexivity |].
  apply typ_λ with (ℓ := S a); [exact HBA |].
  eapply DP.plain_product_sort; eassumption.
Qed.

Lemma product_type_identity_reduces a b n :
  reduces_to nat n
    (product_type (𝓤 a) (𝓤 b) (𝓤 (Nat.max (S a) b)) (BP.type_identity a))
    (plain_product_type a b).
Proof.
  unfold product_type, plain_product_type.
  apply (@Π_cong_par nat (reduces_to nat) _ _ n); [reflexivity |].
  apply BP.arr_reduces; [| reflexivity].
  unfold code_family; apply BP.arr_reduces; [| reflexivity].
  apply rtc_in, BP.type_identity_beta.
Qed.

Theorem identity_product_typed a b n (G : Ctx nat n) :
  @typ nat RankSorts n G (identity_product a b)
    (product_type (𝓤 a) (𝓤 b) (𝓤 (Nat.max (S a) b)) (BP.type_identity a)).
Proof.
  eapply typ_conv with (T := plain_product_type a b) (ℓ := a+2).
  - apply identity_product_plain_typed.
  - apply product_type_sort with (a := a); try (constructor; reflexivity).
    apply BP.type_identity_typing.
  - apply def_equiv_prop; exists (plain_product_type a b); split;
      [reflexivity | apply product_type_identity_reduces].
Qed.

Theorem identity_product_normal a b n :
  normalb (@identity_product a b n) = true.
Proof. reflexivity. Qed.

Theorem identity_product_specializes a b n (A B : Term nat n) :
  reduces_to nat n (app (app (identity_product a b) A) B) (DP.plain_product A B).
Proof.
  unfold identity_product, DP.plain_product, BP.arr.
  eapply rtc_step; [apply step_app_left, step_beta |].
  eapply rtc_step; [apply step_beta |]. syntax_simp.
  reflexivity.
Qed.

Theorem decoded_product_identity_recovers a b n (A B : Term nat n) :
  reduces_to nat n (decoded_product (BP.type_identity a) (BP.type_identity b) A B)
    (DP.plain_product A B).
Proof. apply DP.product_identity_recovers. Qed.

(** The identity algebra's decoding law is genuine original beta conversion,
    ready to give a reflexivity witness at a sufficiently indexed equality
    type. No equality law for arbitrary abstract decoders is postulated. *)
Theorem identity_decoded_product_agrees a b n (A B : Term nat n) :
  def_equiv nat n
    (app (BP.type_identity (Nat.max (S a) b))
      (app (app (identity_product a b) A) B))
    (decoded_product (BP.type_identity a) (BP.type_identity b) A B).
Proof.
  apply def_equiv_prop; exists (DP.plain_product A B); split.
  - eapply rtc_step; [apply BP.type_identity_beta | apply identity_product_specializes].
  - apply decoded_product_identity_recovers.
Qed.

Print Assumptions code_family_sort.
Print Assumptions product_type_sort.
Print Assumptions product_specialize.
Print Assumptions decoded_product_sort.
Print Assumptions identity_product_typed.
Print Assumptions identity_product_normal.
Print Assumptions identity_product_specializes.
Print Assumptions decoded_product_identity_recovers.
Print Assumptions identity_decoded_product_agrees.

End TarskiProducts.
