From Stdlib Require Import Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation
  Ranks DefEq Reduction AbstractRewriting Congruence.
From PTSrk.NormalizationComplexity Require Import Greedy Morphisms.
From PTSrk.SelfInterpreter Require Import BrownPalsberg DependentPHOAS
  IndexedEquality TarskiProducts TarskiCasts TarskiIdentity TypedHOASFaithful.
Import Context.

(** A single polymorphic product-law field per external rank pair, not one
    field for every source type shape. Its concrete identity inhabitant is
    constructed below. No global source-conversion law is assumed. *)
Module TarskiLawFamily.
Module BP := BrownPalsberg.BrownPalsberg.
Module DP := DependentPHOAS.DependentPHOAS.
Module IE := IndexedEquality.IndexedEquality.
Module TP := TarskiProducts.TarskiProducts.
Module TC := TarskiCasts.TarskiCasts.
Module TI := TarskiIdentity.TarskiIdentity.
Module TF := TypedHOASFaithful.TypedHOASFaithful.

Definition family_type a b {n} (Ca Cb Ea Eb Ec p : Term nat n) :=
  Π Ca (Π (TP.code_family (shift Cb) (shift Ea) (var fzero))
    (TC.product_law a b (shift (shift Ea)) (shift (shift Eb))
      (shift (shift Ec)) (shift (shift p)) (var (fsucc fzero)) (var fzero))).

Lemma product_law_rename a b m n (rho : Fin m -> Fin n) Ea Eb Ec p A B :
  rename rho (TC.product_law a b Ea Eb Ec p A B) =
  TC.product_law a b (rename rho Ea) (rename rho Eb) (rename rho Ec)
    (rename rho p) (rename rho A) (rename rho B).
Proof.
  unfold TC.product_law, TC.type_law, TP.decoded_product, DP.product.
  rewrite IE.eq_type_rename. syntax_simp.
Qed.

Lemma product_law_replace a b m n (sigma : Fin m -> Term nat n) Ea Eb Ec p A B :
  replace sigma (TC.product_law a b Ea Eb Ec p A B) =
  TC.product_law a b (replace sigma Ea) (replace sigma Eb) (replace sigma Ec)
    (replace sigma p) (replace sigma A) (replace sigma B).
Proof.
  unfold TC.product_law, TC.type_law, TP.decoded_product, DP.product.
  rewrite IE.eq_type_replace. syntax_simp.
Qed.

Theorem family_type_rename a b m n (rho : Fin m -> Fin n) Ca Cb Ea Eb Ec p :
  rename rho (family_type a b Ca Cb Ea Eb Ec p) =
  family_type a b (rename rho Ca) (rename rho Cb) (rename rho Ea)
    (rename rho Eb) (rename rho Ec) (rename rho p).
Proof.
  unfold family_type, TC.product_law, TC.type_law, TP.decoded_product,
    DP.product, TP.code_family, IE.eq_type, IE.motive_type, BP.arr; syntax_simp.
Qed.

Theorem family_type_replace a b m n (sigma : Fin m -> Term nat n) Ca Cb Ea Eb Ec p :
  replace sigma (family_type a b Ca Cb Ea Eb Ec p) =
  family_type a b (replace sigma Ca) (replace sigma Cb) (replace sigma Ea)
    (replace sigma Eb) (replace sigma Ec) (replace sigma p).
Proof.
  assert (HF : forall m n (s : Fin m -> Term nat n) C E A,
      replace s (TP.code_family C E A) =
      TP.code_family (replace s C) (replace s E) (replace s A)).
  { intros; unfold TP.code_family, BP.arr; syntax_simp. }
  unfold family_type; cbn [replace]. rewrite HF, product_law_replace.
  rewrite !replace_lift_shift. reflexivity.
Qed.

Lemma product_type_shift n (Ca Cb Cc Ea : Term nat n) :
  shift (TP.product_type Ca Cb Cc Ea) =
  TP.product_type (shift Ca) (shift Cb) (shift Cc) (shift Ea).
Proof. unfold TP.product_type, TP.code_family, BP.arr; syntax_simp. Qed.

Theorem family_type_sort a b n (G : Ctx nat n) Ca Cb Cc Ea Eb Ec p :
  @typ nat RankSorts n G Ca (𝓤 0) ->
  @typ nat RankSorts n G Cb (𝓤 0) ->
  @typ nat RankSorts n G Ea (BP.arr Ca (𝓤 a)) ->
  @typ nat RankSorts n G Eb (BP.arr Cb (𝓤 b)) ->
  @typ nat RankSorts n G Ec (BP.arr Cc (𝓤 (Nat.max (S a) b))) ->
  @typ nat RankSorts n G p (TP.product_type Ca Cb Cc Ea) ->
  @typ nat RankSorts n G (family_type a b Ca Cb Ea Eb Ec p)
    (𝓤 (Nat.max (S a) b + 2)).
Proof.
  intros HCa HCb HEa HEb HEc Hp.
  set (F := TP.code_family (shift Cb) (shift Ea) (var (@fzero n))).
  assert (HF : typ (G & Ca) F (𝓤 (S a))).
  { unfold F. eapply TP.code_family_sort with (Ca := shift Ca).
    - change (typ (G & Ca) (shift Cb) (shift (𝓤 0))); apply weakening; exact HCb.
    - change (typ (G & Ca) (shift Ea) (shift (BP.arr Ca (𝓤 a)))).
      apply weakening; exact HEa.
    - change (typ (G & Ca) (var fzero) ((G & Ca) !! fzero)); constructor. }
  unfold family_type.
  eapply typ_Π with (ℓₜ := 0) (ℓᵤ := Nat.max (S a) b+2);
    [exact HCa | | change (Nat.max (S a) b+2 = Nat.max 1 (Nat.max (S a) b+2)); lia].
  eapply typ_Π with (ℓₜ := S a) (ℓᵤ := Nat.max (S a) b+2);
    [exact HF | | change (Nat.max (S a) b+2 = Nat.max (S (S a)) (Nat.max (S a) b+2)); lia].
  eapply TC.product_law_sort with
    (Ca := shift (shift Ca)) (Cb := shift (shift Cb)) (Cc := shift (shift Cc)).
  - change (typ ((G & Ca) & F) (shift (shift Ea)) (shift (shift (BP.arr Ca (𝓤 a))))).
    apply weakening, weakening; exact HEa.
  - change (typ ((G & Ca) & F) (shift (shift Eb)) (shift (shift (BP.arr Cb (𝓤 b))))).
    apply weakening, weakening; exact HEb.
  - change (typ ((G & Ca) & F) (shift (shift Ec))
      (shift (shift (BP.arr Cc (𝓤 (Nat.max (S a) b)))))).
    apply weakening, weakening; exact HEc.
  - rewrite <- !product_type_shift. apply weakening, weakening; exact Hp.
  - change (typ ((G & Ca) & F) (var (fsucc fzero)) (((G & Ca) & F) !! fsucc fzero)).
    constructor.
  - change (typ ((G & Ca) & F) (var fzero)
      (TP.code_family (shift (shift Cb)) (shift (shift Ea)) (shift (var fzero)))).
    rewrite <- TP.code_family_shift.
    change (typ ((G & Ca) & F) (var fzero) (((G & Ca) & F) !! fzero)). constructor.
Qed.

Theorem family_type_normal a b n (Ca Cb Ea Eb Ec p : Fin n) :
  normalb (family_type a b (var Ca) (var Cb) (var Ea) (var Eb) (var Ec) (var p)) = true.
Proof. reflexivity. Qed.

Theorem family_specialize a b n (G : Ctx nat n) Ca Cb Ea Eb Ec p e A B :
  @typ nat RankSorts n G e (family_type a b Ca Cb Ea Eb Ec p) ->
  @typ nat RankSorts n G A Ca ->
  @typ nat RankSorts n G B (TP.code_family Cb Ea A) ->
  @typ nat RankSorts n G (app (app e A) B) (TC.product_law a b Ea Eb Ec p A B).
Proof.
  intros He HA HB. unfold family_type in He.
  pose proof (typ_app Ca He HA) as Hfirst.
  assert (Hsub : subst
      (Π (TP.code_family (shift Cb) (shift Ea) (var fzero))
        (TC.product_law a b (shift (shift Ea)) (shift (shift Eb))
          (shift (shift Ec)) (shift (shift p)) (var (fsucc fzero)) (var fzero))) A =
      Π (TP.code_family Cb Ea A)
        (TC.product_law a b (shift Ea) (shift Eb) (shift Ec) (shift p) (shift A) (var fzero))).
  { unfold subst; cbn [replace]. rewrite product_law_replace.
    rewrite !replace_lift_shift. unfold TP.code_family, BP.arr; syntax_simp.
    cbn [transpose fin_match]. rewrite !BP.replace_fsucc. reflexivity. }
  rewrite Hsub in Hfirst.
  pose proof (typ_app (TP.code_family Cb Ea A) Hfirst HB) as Hsecond.
  assert (Hsub2 : subst
      (TC.product_law a b (shift Ea) (shift Eb) (shift Ec) (shift p) (shift A) (var fzero)) B =
      TC.product_law a b Ea Eb Ec p A B).
  { unfold subst; rewrite product_law_replace; syntax_simp. }
  rewrite Hsub2 in Hsecond. exact Hsecond.
Qed.

Definition identity_type a b {n} : Term nat n :=
  Π (𝓤 a) (Π (BP.arr (var fzero) (𝓤 b))
    (IE.eq_type (S (Nat.max (S a) b)) (𝓤 (Nat.max (S a) b))
      (DP.plain_product (var (fsucc fzero)) (var fzero))
      (DP.plain_product (var (fsucc fzero)) (var fzero)))).

Definition identity_family a b {n} : Term nat n :=
  lam (𝓤 a) (lam (BP.arr (var fzero) (𝓤 b))
    (TI.identity_law a b (var (fsucc fzero)) (var fzero))).

Lemma identity_family_plain_typed a b n (G : Ctx nat n) :
  @typ nat RankSorts n G (identity_family a b) (identity_type a b).
Proof.
  unfold identity_family, identity_type.
  eapply typ_λ with (ℓ := 0); [constructor; reflexivity |].
  eapply typ_λ with (ℓ := S a).
  - replace (S a) with (Nat.max (S a) 0) by lia.
    apply BP.arr_sort; [| constructor; reflexivity].
    change (typ (G & 𝓤 a) (var fzero) ((G & 𝓤 a) !! fzero)); constructor.
  - unfold TI.identity_law. apply IE.refl_case_typed with (a := 0).
    + constructor; reflexivity.
    + apply DP.plain_product_sort with (a := a) (b := b).
      * change (typ ((G & 𝓤 a) & BP.arr (var fzero) (𝓤 b))
          (var (fsucc fzero)) (((G & 𝓤 a) & BP.arr (var fzero) (𝓤 b)) !! fsucc fzero)).
        constructor.
      * change (typ ((G & 𝓤 a) & BP.arr (var fzero) (𝓤 b))
          (var fzero) (((G & 𝓤 a) & BP.arr (var fzero) (𝓤 b)) !! fzero)).
        constructor.
Qed.

Theorem identity_type_recovers a b n :
  reduces_to nat n
    (family_type a b (𝓤 a) (𝓤 b) (BP.type_identity a) (BP.type_identity b)
      (BP.type_identity (Nat.max (S a) b)) (TP.identity_product a b))
    (identity_type a b).
Proof.
  unfold family_type, identity_type.
  apply (@Π_cong_par nat (reduces_to nat) _ _ n); [reflexivity |].
  apply (@Π_cong_par nat (reduces_to nat) _ _ (S n)).
  - change (reduces_to nat (S n)
      (TP.code_family (𝓤 b) (BP.type_identity a) (var fzero)) (BP.arr (var fzero) (𝓤 b))).
    unfold TP.code_family; apply BP.arr_reduces; [apply rtc_in, BP.type_identity_beta | reflexivity].
  - change (reduces_to nat (S (S n))
      (TC.product_law a b (BP.type_identity a) (BP.type_identity b)
        (BP.type_identity (Nat.max (S a) b)) (TP.identity_product a b)
        (var (fsucc fzero)) (var fzero))
      (IE.eq_type (S (Nat.max (S a) b)) (𝓤 (Nat.max (S a) b))
        (DP.plain_product (var (fsucc fzero)) (var fzero))
        (DP.plain_product (var (fsucc fzero)) (var fzero)))).
    unfold TC.product_law, TC.type_law; apply TI.eq_type_reduces.
    + apply TP.decoded_product_identity_recovers.
    + eapply rtc_step; [apply BP.type_identity_beta | apply TP.identity_product_specializes].
Qed.

Theorem identity_family_typed a b n (G : Ctx nat n) :
  @typ nat RankSorts n G (identity_family a b)
    (family_type a b (𝓤 a) (𝓤 b) (BP.type_identity a) (BP.type_identity b)
      (BP.type_identity (Nat.max (S a) b)) (TP.identity_product a b)).
Proof.
  eapply typ_conv with (T := identity_type a b) (ℓ := Nat.max (S a) b+2).
  - apply identity_family_plain_typed.
  - apply family_type_sort with (Cc := 𝓤 (Nat.max (S a) b));
      try (constructor; reflexivity); try apply BP.type_identity_typing.
    apply TP.identity_product_typed.
  - apply def_equiv_prop; exists (identity_type a b); split;
      [reflexivity | apply identity_type_recovers].
Qed.

Theorem identity_family_normal a b n : normalb (@identity_family a b n) = true.
Proof. reflexivity. Qed.

Lemma identity_family_replace a b m n (sigma : Fin m -> Term nat n) :
  replace sigma (@identity_family a b m) = @identity_family a b n.
Proof. reflexivity. Qed.

Theorem identity_family_specializes a b n (A B : Term nat n) :
  reduces_to nat n (app (app (identity_family a b) A) B) (TI.identity_law a b A B).
Proof.
  unfold identity_family, TI.identity_law, DP.plain_product, IE.refl_case,
    IE.motive_type, BP.arr.
  eapply rtc_step; [apply step_app_left, step_beta |].
  eapply rtc_step; [apply step_beta |].
  syntax_simp. unfold shift; syntax_simp. rewrite ?BP.replace_fsucc. reflexivity.
Qed.

Print Assumptions family_type_sort.
Print Assumptions family_type_normal.
Print Assumptions family_type_replace.
Print Assumptions family_specialize.
Print Assumptions identity_type_recovers.
Print Assumptions identity_family_typed.
Print Assumptions identity_family_normal.
Print Assumptions identity_family_specializes.
End TarskiLawFamily.
