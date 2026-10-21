From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation
  Ranks DefEq Reduction AbstractRewriting Congruence.
From PTSrk.NormalizationComplexity Require Import Greedy Morphisms.
From PTSrk.SelfInterpreter Require Import BrownPalsberg DependentPHOAS
  IndexedEquality TarskiProducts TarskiCasts TarskiIdentity TarskiLawFamily TarskiOperations.
Import Context.

(** A prospective finite polymorphic BETA-COHERENCE field and its concrete
    identity realization. Formation does not claim that an arbitrary
    existing product-law witness generates this additional witness. No
    source-quoter, function extensionality or cast-cancellation premise is
    assumed. All displayed types and witnesses are original PTS terms. *)
Module TarskiBeta.
Module BP := BrownPalsberg.BrownPalsberg.
Module DP := DependentPHOAS.DependentPHOAS.
Module IE := IndexedEquality.IndexedEquality.
Module TP := TarskiProducts.TarskiProducts.
Module TC := TarskiCasts.TarskiCasts.
Module TI := TarskiIdentity.TarskiIdentity.
Module LF := TarskiLawFamily.TarskiLawFamily.
Module TO := TarskiOperations.TarskiOperations.

Definition beta_type a b d {n} (Ea Eb A B e f u : Term nat n) :=
  IE.eq_type d (app Eb (app B u))
    (TC.cast_app a b Ea Eb A B e (TC.cast_abs a b Ea Eb A B e f) u)
    (app f u).

Definition rank a b d := Nat.max (S (Nat.max (S a) b)) (Nat.max (b+2) (d+1)).

Lemma plain_apply n (G : Ctx nat n) A B f u :
  @typ nat RankSorts n G f (DP.plain_product A B) ->
  @typ nat RankSorts n G u A ->
  @typ nat RankSorts n G (app f u) (app B u).
Proof.
  intros Hf Hu; unfold DP.plain_product in Hf.
  replace (app B u) with (subst (app (shift B) (var fzero)) u) by syntax_simp.
  eapply typ_app; eassumption.
Qed.

Lemma decoded_apply n (G : Ctx nat n) Ea Eb A B f u :
  @typ nat RankSorts n G f (TP.decoded_product Ea Eb A B) ->
  @typ nat RankSorts n G u (app Ea A) ->
  @typ nat RankSorts n G (app f u) (app Eb (app B u)).
Proof.
  intros Hf Hu; unfold TP.decoded_product, DP.product in Hf.
  replace (app Eb (app B u)) with
    (subst (app (shift Eb) (app (shift B) (var fzero))) u) by syntax_simp.
  eapply typ_app; eassumption.
Qed.

Theorem beta_type_sort a b d n (G : Ctx nat n) Ca Cb Cc Ea Eb Ec p A B e f u :
  @typ nat RankSorts n G Ea (BP.arr Ca (𝓤 a)) ->
  @typ nat RankSorts n G Eb (BP.arr Cb (𝓤 b)) ->
  @typ nat RankSorts n G Ec (BP.arr Cc (𝓤 (Nat.max (S a) b))) ->
  @typ nat RankSorts n G p (TP.product_type Ca Cb Cc Ea) ->
  @typ nat RankSorts n G A Ca ->
  @typ nat RankSorts n G B (TP.code_family Cb Ea A) ->
  @typ nat RankSorts n G e (TC.product_law a b Ea Eb Ec p A B) ->
  @typ nat RankSorts n G f (TP.decoded_product Ea Eb A B) ->
  @typ nat RankSorts n G u (app Ea A) ->
  @typ nat RankSorts n G (beta_type a b d Ea Eb A B e f u)
    (𝓤 (Nat.max (b+2) (d+1))).
Proof.
  intros HEa HEb HEc Hp HA HB He Hf Hu.
  unfold beta_type; apply IE.eq_type_sort with (a := b).
  - eapply BP.arr_apply; [exact HEb |]. eapply BP.arr_apply; [exact HB | exact Hu].
  - eapply TC.cast_app_typed; try eassumption.
    eapply TC.cast_abs_typed; eassumption.
  - eapply decoded_apply; eassumption.
Qed.

Definition arguments_type a b d {n} (Ea Eb A B e : Term nat n) :=
  Π (TP.decoded_product Ea Eb A B)
    (Π (app (shift Ea) (shift A))
      (beta_type a b d (shift (shift Ea)) (shift (shift Eb))
        (shift (shift A)) (shift (shift B)) (shift (shift e))
        (var (fsucc fzero)) (var fzero))).

Definition family_type a b d {n} (Ca Cb Ea Eb ell : Term nat n) :=
  Π Ca (Π (TP.code_family (shift Cb) (shift Ea) (var fzero))
    (arguments_type a b d (shift (shift Ea)) (shift (shift Eb))
      (var (fsucc fzero)) (var fzero)
      (app (app (shift (shift ell)) (var (fsucc fzero))) (var fzero)))).

Lemma decoded_shift n (Ea Eb A B : Term nat n) :
  shift (TP.decoded_product Ea Eb A B) =
  TP.decoded_product (shift Ea) (shift Eb) (shift A) (shift B).
Proof. unfold TP.decoded_product, DP.product; syntax_simp. Qed.

Lemma product_type_shift n (Ca Cb Cc Ea : Term nat n) :
  shift (TP.product_type Ca Cb Cc Ea) =
  TP.product_type (shift Ca) (shift Cb) (shift Cc) (shift Ea).
Proof. apply LF.product_type_shift. Qed.

Lemma product_law_shift a b n (Ea Eb Ec p A B : Term nat n) :
  shift (TC.product_law a b Ea Eb Ec p A B) =
  TC.product_law a b (shift Ea) (shift Eb) (shift Ec) (shift p) (shift A) (shift B).
Proof. apply LF.product_law_rename. Qed.

Lemma law_family_shift a b n (Ca Cb Ea Eb Ec p : Term nat n) :
  shift (LF.family_type a b Ca Cb Ea Eb Ec p) =
  LF.family_type a b (shift Ca) (shift Cb) (shift Ea) (shift Eb) (shift Ec) (shift p).
Proof. apply LF.family_type_rename. Qed.

Theorem arguments_type_sort a b d n (G : Ctx nat n) Ca Cb Cc Ea Eb Ec p A B e :
  @typ nat RankSorts n G Ea (BP.arr Ca (𝓤 a)) ->
  @typ nat RankSorts n G Eb (BP.arr Cb (𝓤 b)) ->
  @typ nat RankSorts n G Ec (BP.arr Cc (𝓤 (Nat.max (S a) b))) ->
  @typ nat RankSorts n G p (TP.product_type Ca Cb Cc Ea) ->
  @typ nat RankSorts n G A Ca ->
  @typ nat RankSorts n G B (TP.code_family Cb Ea A) ->
  @typ nat RankSorts n G e (TC.product_law a b Ea Eb Ec p A B) ->
  @typ nat RankSorts n G (arguments_type a b d Ea Eb A B e) (𝓤 (rank a b d)).
Proof.
  intros HEa HEb HEc Hp HA HB He.
  set (D := TP.decoded_product Ea Eb A B).
  set (GF := G & D).
  set (GU := GF & app (shift Ea) (shift A)).
  unfold arguments_type, rank.
  eapply typ_Π with (ℓₜ := Nat.max (S a) b)
    (ℓᵤ := Nat.max (S a) (Nat.max (b+2) (d+1))).
  - eapply TP.decoded_product_sort; eassumption.
  - eapply typ_Π with (ℓₜ := a) (ℓᵤ := Nat.max (b+2) (d+1)).
    + change (typ GF (shift (app Ea A)) (shift (𝓤 a))).
      apply weakening; eapply BP.arr_apply; eassumption.
    + eapply beta_type_sort with
        (Ca := shift (shift Ca)) (Cb := shift (shift Cb))
        (Cc := shift (shift Cc)) (Ec := shift (shift Ec)) (p := shift (shift p)).
      * change (typ GU (shift (shift Ea)) (shift (shift (BP.arr Ca (𝓤 a))))).
        apply weakening, weakening; exact HEa.
      * change (typ GU (shift (shift Eb)) (shift (shift (BP.arr Cb (𝓤 b))))).
        apply weakening, weakening; exact HEb.
      * change (typ GU (shift (shift Ec)) (shift (shift (BP.arr Cc (𝓤 (Nat.max (S a) b)))))).
        apply weakening, weakening; exact HEc.
      * rewrite <- !product_type_shift. apply weakening, weakening; exact Hp.
      * apply weakening, weakening; exact HA.
      * rewrite <- !TP.code_family_shift. apply weakening, weakening; exact HB.
      * rewrite <- !product_law_shift. apply weakening, weakening; exact He.
      * rewrite <- !decoded_shift.
        change (typ GU (var (fsucc fzero)) (GU !! fsucc fzero)); constructor.
      * change (typ GU (var fzero) (GU !! fzero)); constructor.
    + reflexivity.
  - change (Nat.max (S (Nat.max (S a) b)) (Nat.max (b+2) (d+1)) =
      Nat.max (S (Nat.max (S a) b)) (Nat.max (S a) (Nat.max (b+2) (d+1)))); lia.
Qed.

Theorem family_type_sort a b d n (G : Ctx nat n) Ca Cb Cc Ea Eb Ec p ell :
  @typ nat RankSorts n G Ca (𝓤 0) ->
  @typ nat RankSorts n G Cb (𝓤 0) ->
  @typ nat RankSorts n G Ea (BP.arr Ca (𝓤 a)) ->
  @typ nat RankSorts n G Eb (BP.arr Cb (𝓤 b)) ->
  @typ nat RankSorts n G Ec (BP.arr Cc (𝓤 (Nat.max (S a) b))) ->
  @typ nat RankSorts n G p (TP.product_type Ca Cb Cc Ea) ->
  @typ nat RankSorts n G ell (LF.family_type a b Ca Cb Ea Eb Ec p) ->
  @typ nat RankSorts n G (family_type a b d Ca Cb Ea Eb ell) (𝓤 (rank a b d)).
Proof.
  intros HCa HCb HEa HEb HEc Hp Hell.
  set (F := TP.code_family (shift Cb) (shift Ea) (var (@fzero n))).
  set (GAB := (G & Ca) & F).
  assert (HF : typ (G & Ca) F (𝓤 (S a))).
  { unfold F. eapply TP.code_family_sort with (Ca := shift Ca).
    - change (typ (G & Ca) (shift Cb) (shift (𝓤 0))); apply weakening; exact HCb.
    - change (typ (G & Ca) (shift Ea) (shift (BP.arr Ca (𝓤 a)))); apply weakening; exact HEa.
    - change (typ (G & Ca) (var fzero) ((G & Ca) !! fzero)); constructor. }
  assert (HA : typ GAB (var (fsucc fzero)) (shift (shift Ca))).
  { change (typ GAB (var (fsucc fzero)) (GAB !! fsucc fzero)); constructor. }
  assert (HB : typ GAB (var fzero)
    (TP.code_family (shift (shift Cb)) (shift (shift Ea)) (var (fsucc fzero)))).
  { change (typ GAB (var fzero)
      (TP.code_family (shift (shift Cb)) (shift (shift Ea)) (shift (var fzero)))).
    rewrite <- TP.code_family_shift.
    change (typ GAB (var fzero) (GAB !! fzero)); constructor. }
  unfold family_type.
  eapply typ_Π with (ℓₜ := 0) (ℓᵤ := rank a b d); [exact HCa | |].
  - eapply typ_Π with (ℓₜ := S a) (ℓᵤ := rank a b d); [exact HF | |].
    + eapply arguments_type_sort with
        (Ca := shift (shift Ca)) (Cb := shift (shift Cb))
        (Cc := shift (shift Cc)) (Ec := shift (shift Ec)) (p := shift (shift p)).
      * change (typ GAB (shift (shift Ea)) (shift (shift (BP.arr Ca (𝓤 a))))).
        apply weakening, weakening; exact HEa.
      * change (typ GAB (shift (shift Eb)) (shift (shift (BP.arr Cb (𝓤 b))))).
        apply weakening, weakening; exact HEb.
      * change (typ GAB (shift (shift Ec)) (shift (shift (BP.arr Cc (𝓤 (Nat.max (S a) b)))))).
        apply weakening, weakening; exact HEc.
      * rewrite <- !product_type_shift; apply weakening, weakening; exact Hp.
      * exact HA.
      * exact HB.
      * eapply LF.family_specialize; [| exact HA | exact HB].
        rewrite <- !law_family_shift.
        apply weakening, weakening; exact Hell.
    + change (rank a b d = Nat.max (S (S a)) (rank a b d)); unfold rank; lia.
  - change (rank a b d = Nat.max 1 (rank a b d)); unfold rank; lia.
Qed.

Theorem family_type_normal a b d n (Ca Cb Ea Eb ell : Fin n) :
  normalb (family_type a b d (var Ca) (var Cb) (var Ea) (var Eb) (var ell)) = true.
Proof. reflexivity. Qed.

Theorem beta_type_replace a b d m n (sigma : Fin m -> Term nat n) Ea Eb A B e f u :
  replace sigma (beta_type a b d Ea Eb A B e f u) =
  beta_type a b d (replace sigma Ea) (replace sigma Eb) (replace sigma A)
    (replace sigma B) (replace sigma e) (replace sigma f) (replace sigma u).
Proof.
  unfold beta_type; rewrite IE.eq_type_replace.
  rewrite TO.cast_app_replace, TO.cast_abs_replace; reflexivity.
Qed.

Lemma arguments_type_replace a b d m n (sigma : Fin m -> Term nat n) Ea Eb A B e :
  replace sigma (arguments_type a b d Ea Eb A B e) =
  arguments_type a b d (replace sigma Ea) (replace sigma Eb) (replace sigma A)
    (replace sigma B) (replace sigma e).
Proof.
  unfold arguments_type; cbn [replace]. rewrite beta_type_replace, TO.decoded_product_replace.
  rewrite !replace_lift_shift; reflexivity.
Qed.

Theorem family_type_replace a b d m n (sigma : Fin m -> Term nat n) Ca Cb Ea Eb ell :
  replace sigma (family_type a b d Ca Cb Ea Eb ell) =
  family_type a b d (replace sigma Ca) (replace sigma Cb) (replace sigma Ea)
    (replace sigma Eb) (replace sigma ell).
Proof.
  unfold family_type, arguments_type; cbn [replace]. rewrite beta_type_replace.
  unfold TP.decoded_product, DP.product, TP.code_family, BP.arr; syntax_simp.
Qed.

Lemma arguments_specialize a b d n (G : Ctx nat n) Ea Eb A B e q f u :
  @typ nat RankSorts n G q (arguments_type a b d Ea Eb A B e) ->
  @typ nat RankSorts n G f (TP.decoded_product Ea Eb A B) ->
  @typ nat RankSorts n G u (app Ea A) ->
  @typ nat RankSorts n G (app (app q f) u) (beta_type a b d Ea Eb A B e f u).
Proof.
  intros Hq Hf Hu; unfold arguments_type in Hq.
  pose proof (typ_app (TP.decoded_product Ea Eb A B) Hq Hf) as Hfirst.
  assert (Hsub : subst
      (Π (app (shift Ea) (shift A))
        (beta_type a b d (shift (shift Ea)) (shift (shift Eb))
          (shift (shift A)) (shift (shift B)) (shift (shift e))
          (var (fsucc fzero)) (var fzero))) f =
      Π (app Ea A) (beta_type a b d (shift Ea) (shift Eb) (shift A) (shift B)
        (shift e) (shift f) (var fzero))).
  { unfold subst; cbn [replace]; rewrite beta_type_replace.
    rewrite !replace_lift_shift. syntax_simp.
    cbn [transpose fin_match]; rewrite !BP.replace_fsucc; reflexivity. }
  rewrite Hsub in Hfirst.
  pose proof (typ_app (app Ea A) Hfirst Hu) as Hsecond.
  assert (Hsub2 : subst (beta_type a b d (shift Ea) (shift Eb) (shift A)
      (shift B) (shift e) (shift f) (var fzero)) u = beta_type a b d Ea Eb A B e f u).
  { unfold subst; rewrite beta_type_replace; syntax_simp. }
  rewrite Hsub2 in Hsecond; exact Hsecond.
Qed.

(** Direct application typing for a supplied beta-law FIELD. This does not
    construct that field from the separate product equality ell. *)
Theorem family_specialize a b d n (G : Ctx nat n) Ca Cb Ea Eb ell q A B f u :
  @typ nat RankSorts n G q (family_type a b d Ca Cb Ea Eb ell) ->
  @typ nat RankSorts n G A Ca ->
  @typ nat RankSorts n G B (TP.code_family Cb Ea A) ->
  @typ nat RankSorts n G f (TP.decoded_product Ea Eb A B) ->
  @typ nat RankSorts n G u (app Ea A) ->
  @typ nat RankSorts n G (app (app (app (app q A) B) f) u)
    (beta_type a b d Ea Eb A B (app (app ell A) B) f u).
Proof.
  intros Hq HA HB Hf Hu; unfold family_type in Hq.
  pose proof (typ_app Ca Hq HA) as Hfirst.
  assert (Hsub : subst
      (Π (TP.code_family (shift Cb) (shift Ea) (var fzero))
        (arguments_type a b d (shift (shift Ea)) (shift (shift Eb))
          (var (fsucc fzero)) (var fzero)
          (app (app (shift (shift ell)) (var (fsucc fzero))) (var fzero)))) A =
      Π (TP.code_family Cb Ea A)
        (arguments_type a b d (shift Ea) (shift Eb) (shift A) (var fzero)
          (app (app (shift ell) (shift A)) (var fzero)))).
  { unfold subst; cbn [replace]; rewrite arguments_type_replace.
    rewrite !replace_lift_shift. unfold TP.code_family, BP.arr; syntax_simp.
    cbn [transpose fin_match]; rewrite !BP.replace_fsucc; reflexivity. }
  rewrite Hsub in Hfirst.
  pose proof (typ_app (TP.code_family Cb Ea A) Hfirst HB) as Hsecond.
  assert (Hsub2 : subst
      (arguments_type a b d (shift Ea) (shift Eb) (shift A) (var fzero)
        (app (app (shift ell) (shift A)) (var fzero))) B =
      arguments_type a b d Ea Eb A B (app (app ell A) B)).
  { unfold subst; rewrite arguments_type_replace; syntax_simp. }
  rewrite Hsub2 in Hsecond.
  eapply arguments_specialize; eassumption.
Qed.

Definition plain_arguments_type d {n} (A B : Term nat n) :=
  Π (DP.plain_product A B) (Π (shift A)
    (IE.eq_type d (app (shift (shift B)) (var fzero))
      (app (var (fsucc fzero)) (var fzero)) (app (var (fsucc fzero)) (var fzero)))).

Definition identity_arguments d {n} (A B : Term nat n) :=
  lam (DP.plain_product A B) (lam (shift A)
    (IE.refl_case d (app (shift (shift B)) (var fzero))
      (app (var (fsucc fzero)) (var fzero)))).

Definition identity_type a b d {n} : Term nat n :=
  Π (𝓤 a) (Π (BP.arr (var fzero) (𝓤 b))
    (plain_arguments_type d (var (fsucc fzero)) (var fzero))).

Definition identity_family a b d {n} : Term nat n :=
  lam (𝓤 a) (lam (BP.arr (var fzero) (𝓤 b))
    (identity_arguments d (var (fsucc fzero)) (var fzero))).

Lemma plain_product_shift n (A B : Term nat n) :
  shift (DP.plain_product A B) = DP.plain_product (shift A) (shift B).
Proof. unfold DP.plain_product; syntax_simp. Qed.

Lemma identity_arguments_typed a b d n (G : Ctx nat n) A B :
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G B (BP.arr A (𝓤 b)) ->
  @typ nat RankSorts n G (identity_arguments d A B) (plain_arguments_type d A B).
Proof.
  intros HA HB.
  set (GF := G & DP.plain_product A B).
  set (GU := GF & shift A).
  assert (HB' : typ GU (shift (shift B)) (BP.arr (shift (shift A)) (𝓤 b))).
  { change (typ GU (shift (shift B)) (shift (shift (BP.arr A (𝓤 b))))).
    apply weakening, weakening; exact HB. }
  assert (Hu : typ GU (var fzero) (shift (shift A))).
  { change (typ GU (var fzero) (GU !! fzero)); constructor. }
  assert (Hf : typ GU (var (fsucc fzero))
    (DP.plain_product (shift (shift A)) (shift (shift B)))).
  { rewrite <- !plain_product_shift.
    change (typ GU (var (fsucc fzero)) (GU !! fsucc fzero)); constructor. }
  unfold identity_arguments, plain_arguments_type.
  eapply typ_λ with (ℓ := Nat.max (S a) b); [eapply DP.plain_product_sort; eassumption |].
  eapply typ_λ with (ℓ := a).
  - change (typ GF (shift A) (shift (𝓤 a))); apply weakening; exact HA.
  - apply IE.refl_case_typed with (a := b).
    + eapply BP.arr_apply; eassumption.
    + eapply plain_apply; eassumption.
Qed.

Lemma identity_family_plain_typed a b d n (G : Ctx nat n) :
  @typ nat RankSorts n G (identity_family a b d) (identity_type a b d).
Proof.
  unfold identity_family, identity_type.
  eapply typ_λ with (ℓ := 0); [constructor; reflexivity |].
  eapply typ_λ with (ℓ := S a).
  - replace (S a) with (Nat.max (S a) 0) by lia; apply BP.arr_sort.
    + change (typ (G & 𝓤 a) (var fzero) ((G & 𝓤 a) !! fzero)); constructor.
    + constructor; reflexivity.
  - apply identity_arguments_typed with (a := a) (b := b).
    + change (typ ((G & 𝓤 a) & BP.arr (var fzero) (𝓤 b))
        (var (fsucc fzero)) (((G & 𝓤 a) & BP.arr (var fzero) (𝓤 b)) !! fsucc fzero)); constructor.
    + change (typ ((G & 𝓤 a) & BP.arr (var fzero) (𝓤 b))
        (var fzero) (((G & 𝓤 a) & BP.arr (var fzero) (𝓤 b)) !! fzero)); constructor.
Qed.

Theorem identity_family_normal a b d n : normalb (@identity_family a b d n) = true.
Proof. reflexivity. Qed.

Lemma eq_type_full_reduces d n (A A' u u' v v' : Term nat n) :
  reduces_to nat n A A' -> reduces_to nat n u u' -> reduces_to nat n v v' ->
  reduces_to nat n (IE.eq_type d A u v) (IE.eq_type d A' u' v').
Proof.
  intros HA Hu Hv; unfold IE.eq_type.
  apply (@Π_cong_par nat (reduces_to nat) _ _ n).
  - unfold IE.motive_type; apply BP.arr_reduces; [exact HA | reflexivity].
  - apply BP.arr_reduces; apply (@app_cong_par nat (reduces_to nat) _ _ (S n));
      try reflexivity; apply rename_rtc; assumption.
Qed.

Lemma cast_beta_recovers a b n (Ea Eb A B e V f u : Term nat n) :
  reduces_to nat n e (IE.refl_case (S (Nat.max (S a) b)) (𝓤 (Nat.max (S a) b)) V) ->
  reduces_to nat n (TC.cast_app a b Ea Eb A B e (TC.cast_abs a b Ea Eb A B e f) u)
    (app f u).
Proof.
  intro He.
  assert (HF : reduces_to nat n (TC.cast_abs a b Ea Eb A B e f) f).
  { eapply rtc_trans with (y := TC.cast_abs a b Ea Eb A B
      (IE.refl_case (S (Nat.max (S a) b)) (𝓤 (Nat.max (S a) b)) V) f).
    - unfold TC.cast_abs, TC.forward.
      do 3 apply (@app_cong_l nat (reduces_to nat) _ n); exact He.
    - unfold TC.cast_abs; apply (proj1 (TC.cast_application_reflexivity _ _ _ _ _)). }
  eapply rtc_trans with (y := TC.cast_app a b Ea Eb A B e f u).
  - unfold TC.cast_app. apply (@app_cong_l nat (reduces_to nat) _ n).
    apply (@app_cong_r nat (reduces_to nat) _ n); exact HF.
  - eapply rtc_trans with (y := TC.cast_app a b Ea Eb A B
      (IE.refl_case (S (Nat.max (S a) b)) (𝓤 (Nat.max (S a) b)) V) f u).
    + unfold TC.cast_app, TC.backward.
      do 4 apply (@app_cong_l nat (reduces_to nat) _ n); exact He.
    + unfold TC.cast_app. apply (@app_cong_l nat (reduces_to nat) _ n).
      apply (proj2 (TC.cast_application_reflexivity _ _ _ _ _)).
Qed.

Lemma identity_beta_type_recovers a b d n (A B f u : Term nat n) :
  reduces_to nat n
    (beta_type a b d (BP.type_identity a) (BP.type_identity b) A B
      (app (app (LF.identity_family a b) A) B) f u)
    (IE.eq_type d (app B u) (app f u) (app f u)).
Proof.
  unfold beta_type; apply eq_type_full_reduces.
  - apply rtc_in, BP.type_identity_beta.
  - eapply cast_beta_recovers; apply LF.identity_family_specializes.
  - reflexivity.
Qed.

Lemma arguments_type_identity_recovers a b d n (A B : Term nat n) :
  reduces_to nat n
    (arguments_type a b d (BP.type_identity a) (BP.type_identity b) A B
      (app (app (LF.identity_family a b) A) B)) (plain_arguments_type d A B).
Proof.
  unfold arguments_type, plain_arguments_type.
  apply (@Π_cong_par nat (reduces_to nat) _ _ n).
  - apply TP.decoded_product_identity_recovers.
  - apply (@Π_cong_par nat (reduces_to nat) _ _ (S n)).
    + change (reduces_to nat (S n) (app (BP.type_identity a) (shift A)) (shift A)).
      apply rtc_in, BP.type_identity_beta.
    + change (reduces_to nat (S (S n))
        (beta_type a b d (BP.type_identity a) (BP.type_identity b) (shift (shift A))
          (shift (shift B)) (app (app (LF.identity_family a b) (shift (shift A)))
            (shift (shift B))) (var (fsucc fzero)) (var fzero))
        (IE.eq_type d (app (shift (shift B)) (var fzero))
          (app (var (fsucc fzero)) (var fzero)) (app (var (fsucc fzero)) (var fzero)))).
      apply identity_beta_type_recovers.
Qed.

Theorem identity_type_recovers a b d n :
  reduces_to nat n
    (family_type a b d (𝓤 a) (𝓤 b) (BP.type_identity a) (BP.type_identity b)
      (LF.identity_family a b)) (identity_type a b d).
Proof.
  unfold family_type, identity_type.
  apply (@Π_cong_par nat (reduces_to nat) _ _ n); [reflexivity |].
  apply (@Π_cong_par nat (reduces_to nat) _ _ (S n)).
  - change (reduces_to nat (S n) (TP.code_family (𝓤 b) (BP.type_identity a) (var fzero))
      (BP.arr (var fzero) (𝓤 b))).
    unfold TP.code_family; apply BP.arr_reduces; [apply rtc_in, BP.type_identity_beta | reflexivity].
  - change (reduces_to nat (S (S n))
      (arguments_type a b d (BP.type_identity a) (BP.type_identity b)
        (var (fsucc fzero)) (var fzero)
        (app (app (LF.identity_family a b) (var (fsucc fzero))) (var fzero)))
      (plain_arguments_type d (var (fsucc fzero)) (var fzero))).
    apply arguments_type_identity_recovers.
Qed.

Theorem identity_family_typed a b d n (G : Ctx nat n) :
  @typ nat RankSorts n G (identity_family a b d)
    (family_type a b d (𝓤 a) (𝓤 b) (BP.type_identity a) (BP.type_identity b)
      (LF.identity_family a b)).
Proof.
  eapply typ_conv with (T := identity_type a b d) (ℓ := rank a b d).
  - apply identity_family_plain_typed.
  - eapply family_type_sort with (Cc := 𝓤 (Nat.max (S a) b))
      (Ec := BP.type_identity (Nat.max (S a) b)) (p := TP.identity_product a b);
      try (constructor; reflexivity); try apply BP.type_identity_typing.
    + apply TP.identity_product_typed.
    + apply LF.identity_family_typed.
  - apply def_equiv_prop; exists (identity_type a b d); split;
      [reflexivity | apply identity_type_recovers].
Qed.

Theorem identity_family_specializes a b d n (A B f u : Term nat n) :
  reduces_to nat n (app (app (app (app (identity_family a b d) A) B) f) u)
    (IE.refl_case d (app B u) (app f u)).
Proof.
  unfold identity_family, identity_arguments, DP.plain_product,
    IE.refl_case, IE.motive_type, BP.arr.
  eapply rtc_step; [apply step_app_left, step_app_left, step_app_left, step_beta |].
  eapply rtc_step; [apply step_app_left, step_app_left, step_beta |].
  eapply rtc_step; [apply step_app_left, step_beta |].
  eapply rtc_step; [apply step_beta |].
  syntax_simp. cbn [transpose fin_match]. rewrite ?BP.replace_fsucc; reflexivity.
Qed.

Theorem identity_family_replace a b d m n (sigma : Fin m -> Term nat n) :
  replace sigma (@identity_family a b d m) = @identity_family a b d n.
Proof. reflexivity. Qed.

Print Assumptions beta_type_sort.
Print Assumptions arguments_type_sort.
Print Assumptions family_type_sort.
Print Assumptions family_type_normal.
Print Assumptions beta_type_replace.
Print Assumptions family_type_replace.
Print Assumptions family_specialize.
Print Assumptions identity_family_normal.
Print Assumptions identity_type_recovers.
Print Assumptions identity_family_typed.
Print Assumptions identity_family_specializes.
Print Assumptions identity_family_replace.

End TarskiBeta.
