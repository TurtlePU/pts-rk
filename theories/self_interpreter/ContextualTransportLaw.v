From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting Congruence DefEq.
From PTSrk.NormalizationComplexity Require Import Morphisms Greedy.
From PTSrk.SelfInterpreter Require Import BrownPalsberg IndexedEquality
  DependentEquality TarskiProducts TarskiCasts TarskiIdentity TarskiLawFamily
  TarskiBeta ContextualTelescope UniformTelescope TelescopeBetaFamily.
Import Context ListNotations.

(** A SPECIFIC chosen-transport coherence schema. Formation of [law] is
    generic, but no inhabitant for arbitrary Leibniz evidence is assumed.
    The independently realized contextual instance uses the actual beta
    field, whose identity implementation computes to literal reflexivity. *)
Module ContextualTransportLaw.
Module BP := BrownPalsberg.BrownPalsberg.
Module IE := IndexedEquality.IndexedEquality.
Module DE := DependentEquality.DependentEquality.
Module TP := TarskiProducts.TarskiProducts.
Module TC := TarskiCasts.TarskiCasts.
Module TI := TarskiIdentity.TarskiIdentity.
Module LF := TarskiLawFamily.TarskiLawFamily.
Module TB := TarskiBeta.TarskiBeta.
Module CT := ContextualTelescope.ContextualTelescope.
Module UT := UniformTelescope.UniformTelescope.
Module BF := TelescopeBetaFamily.TelescopeBetaFamily.
Module UR := UniformTelescopeRecovery.UniformTelescopeRecovery.

Definition law p d {n} (C l r e : Term nat n) :=
  Π (IE.motive_type p C) (Π (app (var fzero) (shift l))
    (DE.graph_eq d (shift (shift C)) (var (fsucc fzero))
      (shift (shift l)) (var fzero) (shift (shift r))
      (IE.transport (shift (shift e)) (var (fsucc fzero)) (var fzero)))).
Definition law_rank c p d := Nat.max (c+2) (Nat.max (p+2) (d+1)).
Definition reflexive_type p d {n} (C l : Term nat n) :=
  Π (IE.motive_type p C) (Π (app (var fzero) (shift l))
    (DE.graph_eq d (shift (shift C)) (var (fsucc fzero))
      (shift (shift l)) (var fzero) (shift (shift l)) (var fzero))).
Definition reflexivity p d {n} (C l : Term nat n) :=
  lam (IE.motive_type p C) (lam (app (var fzero) (shift l))
    (DE.graph_refl d (shift (shift C)) (var (fsucc fzero)) (shift (shift l)) (var fzero))).

Lemma law_replace p d m n (sigma : Fin m -> Term nat n) C l r e :
  replace sigma (law p d C l r e) = law p d
    (replace sigma C) (replace sigma l) (replace sigma r) (replace sigma e).
Proof.
  unfold law; cbn [replace]; rewrite IE.motive_type_replace, DE.graph_eq_replace.
  cbn [IE.transport replace transpose fin_match]; rewrite !replace_lift_shift; reflexivity.
Qed.
Lemma reflexivity_replace p d m n (sigma : Fin m -> Term nat n) C l :
  replace sigma (reflexivity p d C l) = reflexivity p d (replace sigma C) (replace sigma l).
Proof.
  unfold reflexivity; cbn [replace]; rewrite IE.motive_type_replace, DE.graph_refl_replace.
  cbn [replace transpose fin_match]; rewrite !replace_lift_shift; reflexivity.
Qed.

Theorem law_sort c p d n (G : Ctx nat n) C l r e :
  @typ nat RankSorts n G C (𝓤 c) ->
  @typ nat RankSorts n G l C -> @typ nat RankSorts n G r C ->
  @typ nat RankSorts n G e (IE.eq_type p C l r) ->
  @typ nat RankSorts n G (law p d C l r e) (𝓤 (law_rank c p d)).
Proof.
  intros HC Hl Hr He; set (GP := G & IE.motive_type p C).
  set (Gz := GP & app (var fzero) (shift l)).
  unfold law; eapply typ_Π with (ℓₜ := S c) (ℓᵤ := law_rank c p d).
  - apply IE.motive_type_sort; exact HC.
  - eapply typ_Π with (ℓₜ := p) (ℓᵤ := law_rank c p d).
    + apply IE.bound_motive_application; exact Hl.
    + replace (law_rank c p d) with (DE.rank c p d) by (unfold law_rank, DE.rank; lia).
      eapply DE.graph_eq_sort with (a := c) (b := p).
      * change (typ Gz (shift (shift C)) (shift (shift (𝓤 c)))); apply weakening, weakening; exact HC.
      * change (typ Gz (var (fsucc fzero)) (Gz !! fsucc fzero)); constructor.
      * apply weakening, weakening; exact Hl.
      * change (typ Gz (var fzero) (Gz !! fzero)); constructor.
      * apply weakening, weakening; exact Hr.
      * eapply IE.transport_typed with (A := shift (shift C)) (u := shift (shift l)).
        -- unfold shift; rewrite <- !IE.eq_type_rename; apply weakening, weakening; exact He.
        -- change (typ Gz (var (fsucc fzero)) (Gz !! fsucc fzero)); constructor.
        -- change (typ Gz (var fzero) (Gz !! fzero)); constructor.
    + unfold law_rank; change (Nat.max (c+2) (Nat.max (p+2) (d+1)) =
        Nat.max (S p) (Nat.max (c+2) (Nat.max (p+2) (d+1)))); lia.
  - unfold law_rank; change (Nat.max (c+2) (Nat.max (p+2) (d+1)) =
      Nat.max (S (S c)) (Nat.max (c+2) (Nat.max (p+2) (d+1)))); lia.
Qed.

Theorem reflexivity_plain_typed c p d n (G : Ctx nat n) C l :
  @typ nat RankSorts n G C (𝓤 c) -> @typ nat RankSorts n G l C ->
  @typ nat RankSorts n G (reflexivity p d C l) (reflexive_type p d C l).
Proof.
  intros HC Hl; set (GP := G & IE.motive_type p C).
  set (Gz := GP & app (var fzero) (shift l)).
  unfold reflexivity, reflexive_type; apply typ_λ with (ℓ := S c).
  - apply IE.motive_type_sort; exact HC.
  - apply typ_λ with (ℓ := p); [apply IE.bound_motive_application; exact Hl |].
    apply DE.graph_refl_typed with (a := c) (b := p).
    + change (typ Gz (shift (shift C)) (shift (shift (𝓤 c)))); apply weakening, weakening; exact HC.
    + change (typ Gz (var (fsucc fzero)) (Gz !! fsucc fzero)); constructor.
    + apply weakening, weakening; exact Hl.
    + change (typ Gz (var fzero) (Gz !! fzero)); constructor.
Qed.

Lemma graph_eq_reduces d n (A A' B B' u u' y y' v v' z z' : Term nat n) :
  reduces_to nat n A A' -> reduces_to nat n B B' -> reduces_to nat n u u' ->
  reduces_to nat n y y' -> reduces_to nat n v v' -> reduces_to nat n z z' ->
  reduces_to nat n (DE.graph_eq d A B u y v z) (DE.graph_eq d A' B' u' y' v' z').
Proof.
  intros HA HB Hu Hy Hv Hz; unfold DE.graph_eq, DE.predicate_type, DE.observe.
  apply (@Π_cong_par nat (reduces_to nat) _ _ n).
  - apply (@Π_cong_par nat (reduces_to nat) _ _ n); [exact HA |].
    apply BP.arr_reduces; [| reflexivity]. apply (@app_cong_l nat (reduces_to nat) _ (S n)), rename_rtc; exact HB.
  - apply BP.arr_reduces; apply (@app_cong_par nat (reduces_to nat) _ _ (S n));
      try (apply rename_rtc; assumption);
      apply (@app_cong_r nat (reduces_to nat) _ (S n)), rename_rtc; assumption.
Qed.
Lemma law_reduces p d n (C C' l l' r r' e e' : Term nat n) :
  reduces_to nat n C C' -> reduces_to nat n l l' -> reduces_to nat n r r' -> reduces_to nat n e e' ->
  reduces_to nat n (law p d C l r e) (law p d C' l' r' e').
Proof.
  intros HC Hl Hr He; unfold law; apply (@Π_cong_par nat (reduces_to nat) _ _ n).
  - unfold IE.motive_type; apply BP.arr_reduces; [exact HC | reflexivity].
  - apply (@Π_cong_par nat (reduces_to nat) _ _ (S n)).
    + apply (@app_cong_r nat (reduces_to nat) _ (S n)), rename_rtc; exact Hl.
    + apply graph_eq_reduces; try reflexivity; try (apply rename_rtc, rename_rtc; assumption).
      unfold IE.transport; do 2 apply (@app_cong_l nat (reduces_to nat) _ (S (S n))).
      apply rename_rtc, rename_rtc; exact He.
Qed.
Theorem law_reflexivity_reduces p d n (C l : Term nat n) :
  reduces_to nat n (law p d C l l (IE.refl_case p C l)) (reflexive_type p d C l).
Proof.
  unfold law, reflexive_type; do 2 apply (@Π_cong_r nat (reduces_to nat) _ _).
  apply graph_eq_reduces; try reflexivity.
  unfold shift; rewrite !IE.refl_case_rename; apply IE.transport_refl.
Qed.
Theorem reflexivity_typed c p d n (G : Ctx nat n) C l :
  @typ nat RankSorts n G C (𝓤 c) -> @typ nat RankSorts n G l C ->
  @typ nat RankSorts n G (reflexivity p d C l) (law p d C l l (IE.refl_case p C l)).
Proof.
  intros HC Hl; eapply TI.convert_to_reduct with (r := law_rank c p d).
  - apply reflexivity_plain_typed with (c := c); assumption.
  - apply law_sort with (c := c); try assumption; apply IE.refl_case_typed with (a := c); assumption.
  - apply law_reflexivity_reduces.
Qed.
Theorem reflexivity_specializes p d n (C l P z : Term nat n) :
  reduces_to nat n (app (app (reflexivity p d C l) P) z) (DE.graph_refl d C P l z).
Proof.
  unfold reflexivity; eapply rtc_step; [apply step_app_left, step_beta |].
  unfold subst; cbn [replace]; rewrite DE.graph_refl_replace, !replace_lift_shift; syntax_simp.
  eapply rtc_step; [apply step_beta |]. unfold subst; rewrite DE.graph_refl_replace; syntax_simp; reflexivity.
Qed.
Theorem law_normal p d n (C l r e : Term nat n) :
  normalb C = true -> normalb l = true -> normalb r = true ->
  normalb e = true -> isLambda e = false -> normalb (law p d C l r e) = true.
Proof.
  intros HC Hl Hr He Ne; unfold law, IE.motive_type, IE.transport,
    DE.graph_eq, DE.predicate_type, DE.observe, BP.arr, shift.
  repeat progress (cbn [normalb isLambda]; rewrite ?UT.normalb_rename, ?UT.isLambda_rename).
  rewrite ?HC, ?Hl, ?Hr, ?He, ?Ne; reflexivity.
Qed.
Theorem reflexivity_normal p d n (C l : Term nat n) :
  normalb C = true -> normalb l = true -> normalb (reflexivity p d C l) = true.
Proof.
  intros HC Hl; unfold reflexivity, IE.motive_type, DE.graph_refl,
    DE.predicate_type, DE.observe, BP.arr, shift.
  repeat progress (cbn [normalb isLambda]; rewrite ?UT.normalb_rename, ?UT.isLambda_rename).
  rewrite ?HC, ?Hl; reflexivity.
Qed.

Definition carrier {n rs} (D : CT.telescope n rs) (Eb B u : Term nat n) :=
  CT.close_type D (app (BF.lift rs Eb) (app (UT.apply_under D B) (UT.apply_under D u))).
Definition left_side a b {n rs} (D : CT.telescope n rs) (Ea Eb ell A B f u : Term nat n) :=
  let e := app (app (BF.lift rs ell) (UT.apply_under D A)) (UT.apply_under D B) in
  CT.close_term D (TC.cast_app a b (BF.lift rs Ea) (BF.lift rs Eb)
    (UT.apply_under D A) (UT.apply_under D B) e
    (TC.cast_abs a b (BF.lift rs Ea) (BF.lift rs Eb)
      (UT.apply_under D A) (UT.apply_under D B) e (UT.apply_under D f)) (UT.apply_under D u)).
Definition applied {n} (q A B f u : Term nat n) := app (app (app (app q A) B) f) u.
Definition instance_type a b p d {n rs} (D : CT.telescope n rs) (Ea Eb ell q A B f u : Term nat n) :=
  law p d (carrier D Eb B u) (left_side a b D Ea Eb ell A B f u) (BF.right_side D f u) (applied q A B f u).
Definition instance_rank rs b p d := law_rank (CT.rank rs b) p d.

Lemma contextual_endpoints_typed a b n rs (D : CT.telescope n rs) G Ca Cb Cc Ea Eb Ec P ell A B f u :
  CT.formed G D ->
  @typ nat RankSorts n G Ea (BP.arr Ca (𝓤 a)) ->
  @typ nat RankSorts n G Eb (BP.arr Cb (𝓤 b)) ->
  @typ nat RankSorts n G Ec (BP.arr Cc (𝓤 (Nat.max (S a) b))) ->
  @typ nat RankSorts n G P (TP.product_type Ca Cb Cc Ea) ->
  @typ nat RankSorts n G ell (LF.family_type a b Ca Cb Ea Eb Ec P) ->
  @typ nat RankSorts n G A (BF.carrier_family D Ca) ->
  @typ nat RankSorts n G B (BF.code_family D Cb Ea A) ->
  @typ nat RankSorts n G f (BF.function_family D Ea Eb A B) ->
  @typ nat RankSorts n G u (BF.domain_family D Ea A) ->
  typ G (carrier D Eb B u) (𝓤 (CT.rank rs b)) /\
  typ G (left_side a b D Ea Eb ell A B f u) (carrier D Eb B u) /\
  typ G (BF.right_side D f u) (carrier D Eb B u).
Proof.
  intros HD HEa HEb HEc HP Hell HA HB Hf Hu.
  set (H := CT.context D G).
  assert (HA' : typ H (UT.apply_under D A) (BF.lift rs Ca)) by (apply UT.apply_under_typed; exact HA).
  assert (HB' : typ H (UT.apply_under D B)
    (TP.code_family (BF.lift rs Cb) (BF.lift rs Ea) (UT.apply_under D A)))
    by (apply UT.apply_under_typed; exact HB).
  assert (Hf' : typ H (UT.apply_under D f)
    (TP.decoded_product (BF.lift rs Ea) (BF.lift rs Eb) (UT.apply_under D A) (UT.apply_under D B)))
    by (apply UT.apply_under_typed; exact Hf).
  assert (Hu' : typ H (UT.apply_under D u) (app (BF.lift rs Ea) (UT.apply_under D A)))
    by (apply UT.apply_under_typed; exact Hu).
  assert (He : typ H (app (app (BF.lift rs ell) (UT.apply_under D A)) (UT.apply_under D B))
    (TC.product_law a b (BF.lift rs Ea) (BF.lift rs Eb) (BF.lift rs Ec) (BF.lift rs P)
      (UT.apply_under D A) (UT.apply_under D B))).
  { eapply LF.family_specialize; [| exact HA' | exact HB'].
    unfold BF.lift; rewrite <- LF.family_type_rename; apply UT.base_typing; exact Hell. }
  split.
  - apply CT.close_type_sort; [exact HD |].
    eapply BP.arr_apply with (A := BF.lift rs Cb); [apply BF.lift_decoder; exact HEb |].
    eapply BP.arr_apply; eassumption.
  - split; apply CT.close_typing; try exact HD.
    + eapply TC.cast_app_typed with (Ca := BF.lift rs Ca) (Cb := BF.lift rs Cb)
        (Cc := BF.lift rs Cc) (Ec := BF.lift rs Ec) (p := BF.lift rs P); try eassumption.
      * apply BF.lift_decoder; exact HEa.
      * apply BF.lift_decoder; exact HEb.
      * apply BF.lift_decoder; exact HEc.
      * unfold BF.lift; rewrite <- TarskiSignature.TarskiSignature.product_type_rename; apply UT.base_typing; exact HP.
      * eapply TC.cast_abs_typed with (Ca := BF.lift rs Ca) (Cb := BF.lift rs Cb)
          (Cc := BF.lift rs Cc) (Ec := BF.lift rs Ec) (p := BF.lift rs P); try eassumption.
        -- apply BF.lift_decoder; exact HEa.
        -- apply BF.lift_decoder; exact HEb.
        -- apply BF.lift_decoder; exact HEc.
        -- unfold BF.lift; rewrite <- TarskiSignature.TarskiSignature.product_type_rename; apply UT.base_typing; exact HP.
    + eapply TB.decoded_apply; eassumption.
Qed.

Theorem instance_type_sort a b p d n rs (D : CT.telescope n rs) G Ca Cb Cc Ea Eb Ec P ell q A B f u :
  CT.formed G D ->
  @typ nat RankSorts n G Ea (BP.arr Ca (𝓤 a)) ->
  @typ nat RankSorts n G Eb (BP.arr Cb (𝓤 b)) ->
  @typ nat RankSorts n G Ec (BP.arr Cc (𝓤 (Nat.max (S a) b))) ->
  @typ nat RankSorts n G P (TP.product_type Ca Cb Cc Ea) ->
  @typ nat RankSorts n G ell (LF.family_type a b Ca Cb Ea Eb Ec P) ->
  @typ nat RankSorts n G q (BF.family_type a b p D Ca Cb Ea Eb ell) ->
  @typ nat RankSorts n G A (BF.carrier_family D Ca) ->
  @typ nat RankSorts n G B (BF.code_family D Cb Ea A) ->
  @typ nat RankSorts n G f (BF.function_family D Ea Eb A B) ->
  @typ nat RankSorts n G u (BF.domain_family D Ea A) ->
  @typ nat RankSorts n G (instance_type a b p d D Ea Eb ell q A B f u) (𝓤 (instance_rank rs b p d)).
Proof.
  intros HD HEa HEb HEc HP Hell Hq HA HB Hf Hu.
  destruct (contextual_endpoints_typed a b n rs D G Ca Cb Cc Ea Eb Ec P ell A B f u
    HD HEa HEb HEc HP Hell HA HB Hf Hu) as [HC [Hl Hr]].
  unfold instance_type, instance_rank; apply law_sort with (c := CT.rank rs b); try assumption.
  change (typ G (applied q A B f u) (BF.conclusion a b p D Ea Eb ell A B f u)).
  eapply BF.family_specialize; eassumption.
Qed.

Lemma carrier_identity_recovers b n rs (D : CT.telescope n rs) B u :
  reduces_to nat n (carrier D (BP.type_identity b) B u) (BF.identity_carrier D B u).
Proof. unfold carrier, BF.identity_carrier; apply CT.close_type_reduces, rtc_in, BP.type_identity_beta. Qed.
Lemma left_identity_recovers a b n rs (D : CT.telescope n rs) A B f u :
  reduces_to nat n (left_side a b D (BP.type_identity a) (BP.type_identity b) (LF.identity_family a b) A B f u)
    (BF.right_side D f u).
Proof.
  unfold left_side, BF.right_side; apply CT.close_term_reduces.
  eapply TB.cast_beta_recovers with (V := DependentPHOAS.DependentPHOAS.plain_product
    (UT.apply_under D A) (UT.apply_under D B)).
  apply LF.identity_family_specializes.
Qed.
Theorem identity_instance_type_recovers a b p d n rs (D : CT.telescope n rs) A B f u :
  reduces_to nat n (instance_type a b p d D (BP.type_identity a) (BP.type_identity b)
    (LF.identity_family a b) (BF.identity_family a b p D) A B f u)
    (reflexive_type p d (BF.identity_carrier D B u) (BF.right_side D f u)).
Proof.
  unfold instance_type; eapply rtc_trans; [apply law_reduces | apply law_reflexivity_reduces].
  - apply carrier_identity_recovers.
  - apply left_identity_recovers.
  - reflexivity.
  - apply BF.identity_family_specializes.
Qed.

Definition arguments_type a b p d {n rs} (D : CT.telescope n rs) (Ea Eb ell q A B : Term nat n) :=
  Π (BF.function_family D Ea Eb A B)
    (Π (BF.domain_family (BF.weaken D) (shift Ea) (shift A))
      (instance_type a b p d (BF.weaken (BF.weaken D))
        (shift (shift Ea)) (shift (shift Eb)) (shift (shift ell)) (shift (shift q))
        (shift (shift A)) (shift (shift B)) (var (fsucc fzero)) (var fzero))).
Definition families_type a b p d {n rs} (D : CT.telescope n rs) (Cb Ea Eb ell q A : Term nat n) :=
  Π (BF.code_family D Cb Ea A)
    (arguments_type a b p d (BF.weaken D) (shift Ea) (shift Eb) (shift ell) (shift q) (shift A) (var fzero)).
Definition family_type a b p d {n rs} (D : CT.telescope n rs) (Ca Cb Ea Eb ell q : Term nat n) :=
  Π (BF.carrier_family D Ca)
    (families_type a b p d (BF.weaken D) (shift Cb) (shift Ea) (shift Eb) (shift ell) (shift q) (var fzero)).
Definition rank rs a b p d := Nat.max (CT.ceiling rs+2)
  (Nat.max (a+2) (Nat.max (b+2) (Nat.max (p+2) (d+1)))).

Lemma beta_family_shift a b p n rs (D : CT.telescope n rs) Ca Cb Ea Eb ell :
  shift (BF.family_type a b p D Ca Cb Ea Eb ell) =
    BF.family_type a b p (BF.weaken D) (shift Ca) (shift Cb) (shift Ea) (shift Eb) (shift ell).
Proof. apply BF.family_type_rename. Qed.

Lemma arguments_type_sort a b p d n rs (D : CT.telescope n rs) G Ca Cb Cc Ea Eb Ec P ell q A B :
  CT.formed G D ->
  @typ nat RankSorts n G Ea (BP.arr Ca (𝓤 a)) ->
  @typ nat RankSorts n G Eb (BP.arr Cb (𝓤 b)) ->
  @typ nat RankSorts n G Ec (BP.arr Cc (𝓤 (Nat.max (S a) b))) ->
  @typ nat RankSorts n G P (TP.product_type Ca Cb Cc Ea) ->
  @typ nat RankSorts n G ell (LF.family_type a b Ca Cb Ea Eb Ec P) ->
  @typ nat RankSorts n G q (BF.family_type a b p D Ca Cb Ea Eb ell) ->
  @typ nat RankSorts n G A (BF.carrier_family D Ca) ->
  @typ nat RankSorts n G B (BF.code_family D Cb Ea A) ->
  @typ nat RankSorts n G (arguments_type a b p d D Ea Eb ell q A B) (𝓤 (rank rs a b p d)).
Proof.
  intros HD HEa HEb HEc HP Hell Hq HA HB.
  set (GF := G & BF.function_family D Ea Eb A B).
  set (GU := GF & BF.domain_family (BF.weaken D) (shift Ea) (shift A)).
  unfold arguments_type.
  eapply typ_Π with (ℓₜ := CT.rank rs (Nat.max (S a) b))
    (ℓᵤ := Nat.max (S (CT.rank rs a)) (instance_rank rs b p d)).
  - eapply BF.function_family_sort; eassumption.
  - eapply typ_Π with (ℓₜ := CT.rank rs a) (ℓᵤ := instance_rank rs b p d); [| | reflexivity].
    + rewrite <- BF.domain_family_shift.
      change (typ GF (shift (BF.domain_family D Ea A)) (shift (𝓤 (CT.rank rs a)))).
      apply weakening; eapply BF.domain_family_sort; eassumption.
    + eapply instance_type_sort with (Ca := shift (shift Ca)) (Cb := shift (shift Cb))
        (Cc := shift (shift Cc)) (Ec := shift (shift Ec)) (P := shift (shift P)).
      * apply BF.weaken_formed, BF.weaken_formed; exact HD.
      * change (typ GU (shift (shift Ea)) (shift (shift (BP.arr Ca (𝓤 a))))); apply weakening, weakening; exact HEa.
      * change (typ GU (shift (shift Eb)) (shift (shift (BP.arr Cb (𝓤 b))))); apply weakening, weakening; exact HEb.
      * change (typ GU (shift (shift Ec)) (shift (shift (BP.arr Cc (𝓤 (Nat.max (S a) b)))))); apply weakening, weakening; exact HEc.
      * rewrite <- !TB.product_type_shift; apply weakening, weakening; exact HP.
      * rewrite <- !TB.law_family_shift; apply weakening, weakening; exact Hell.
      * rewrite <- !beta_family_shift; apply weakening, weakening; exact Hq.
      * rewrite <- !BF.carrier_family_shift; apply weakening, weakening; exact HA.
      * rewrite <- !BF.code_family_shift; apply weakening, weakening; exact HB.
      * rewrite <- !BF.function_family_shift; change (typ GU (var (fsucc fzero)) (GU !! fsucc fzero)); constructor.
      * rewrite <- (BF.domain_family_shift _ _ (BF.weaken D) (shift Ea) (shift A)).
        change (typ GU (var fzero) (GU !! fzero)); constructor.
  - unfold rank, instance_rank, law_rank; rewrite !CT.rank_exact; change
      (Nat.max (CT.ceiling rs+2) (Nat.max (a+2) (Nat.max (b+2) (Nat.max (p+2) (d+1)))) =
       Nat.max (S (Nat.max (CT.ceiling rs) (Nat.max (S a) b)))
        (Nat.max (S (Nat.max (CT.ceiling rs) a))
          (Nat.max (Nat.max (CT.ceiling rs) b+2) (Nat.max (p+2) (d+1))))); lia.
Qed.

Lemma families_type_sort a b p d n rs (D : CT.telescope n rs) G Ca Cb Cc Ea Eb Ec P ell q A :
  CT.formed G D -> @typ nat RankSorts n G Cb (𝓤 0) ->
  @typ nat RankSorts n G Ea (BP.arr Ca (𝓤 a)) ->
  @typ nat RankSorts n G Eb (BP.arr Cb (𝓤 b)) ->
  @typ nat RankSorts n G Ec (BP.arr Cc (𝓤 (Nat.max (S a) b))) ->
  @typ nat RankSorts n G P (TP.product_type Ca Cb Cc Ea) ->
  @typ nat RankSorts n G ell (LF.family_type a b Ca Cb Ea Eb Ec P) ->
  @typ nat RankSorts n G q (BF.family_type a b p D Ca Cb Ea Eb ell) ->
  @typ nat RankSorts n G A (BF.carrier_family D Ca) ->
  @typ nat RankSorts n G (families_type a b p d D Cb Ea Eb ell q A) (𝓤 (rank rs a b p d)).
Proof.
  intros HD HC HEa HEb HEc HP Hell Hq HA; set (GB := G & BF.code_family D Cb Ea A).
  unfold families_type; eapply typ_Π with (ℓₜ := CT.rank rs (S a)) (ℓᵤ := rank rs a b p d).
  - eapply BF.code_family_sort; eassumption.
  - eapply arguments_type_sort with (Ca := shift Ca) (Cb := shift Cb)
      (Cc := shift Cc) (Ec := shift Ec) (P := shift P).
    + apply BF.weaken_formed; exact HD.
    + change (typ GB (shift Ea) (shift (BP.arr Ca (𝓤 a)))); apply weakening; exact HEa.
    + change (typ GB (shift Eb) (shift (BP.arr Cb (𝓤 b)))); apply weakening; exact HEb.
    + change (typ GB (shift Ec) (shift (BP.arr Cc (𝓤 (Nat.max (S a) b))))); apply weakening; exact HEc.
    + rewrite <- TB.product_type_shift; apply weakening; exact HP.
    + rewrite <- TB.law_family_shift; apply weakening; exact Hell.
    + rewrite <- beta_family_shift; apply weakening; exact Hq.
    + rewrite <- BF.carrier_family_shift; apply weakening; exact HA.
    + rewrite <- BF.code_family_shift; change (typ GB (var fzero) (GB !! fzero)); constructor.
  - unfold rank; rewrite CT.rank_exact; change
      (Nat.max (CT.ceiling rs+2) (Nat.max (a+2) (Nat.max (b+2) (Nat.max (p+2) (d+1)))) =
       Nat.max (S (Nat.max (CT.ceiling rs) (S a)))
        (Nat.max (CT.ceiling rs+2) (Nat.max (a+2) (Nat.max (b+2) (Nat.max (p+2) (d+1)))))); lia.
Qed.

Theorem family_type_sort a b p d n rs (D : CT.telescope n rs) G Ca Cb Cc Ea Eb Ec P ell q :
  CT.formed G D ->
  @typ nat RankSorts n G Ca (𝓤 0) -> @typ nat RankSorts n G Cb (𝓤 0) ->
  @typ nat RankSorts n G Ea (BP.arr Ca (𝓤 a)) ->
  @typ nat RankSorts n G Eb (BP.arr Cb (𝓤 b)) ->
  @typ nat RankSorts n G Ec (BP.arr Cc (𝓤 (Nat.max (S a) b))) ->
  @typ nat RankSorts n G P (TP.product_type Ca Cb Cc Ea) ->
  @typ nat RankSorts n G ell (LF.family_type a b Ca Cb Ea Eb Ec P) ->
  @typ nat RankSorts n G q (BF.family_type a b p D Ca Cb Ea Eb ell) ->
  @typ nat RankSorts n G (family_type a b p d D Ca Cb Ea Eb ell q) (𝓤 (rank rs a b p d)).
Proof.
  intros HD HCa HCb HEa HEb HEc HP Hell Hq; set (GA := G & BF.carrier_family D Ca).
  unfold family_type; eapply typ_Π with (ℓₜ := CT.rank rs 0) (ℓᵤ := rank rs a b p d).
  - apply BF.carrier_family_sort; assumption.
  - eapply families_type_sort with (Ca := shift Ca) (Cc := shift Cc) (Ec := shift Ec) (P := shift P).
    + apply BF.weaken_formed; exact HD.
    + change (typ GA (shift Cb) (shift (𝓤 0))); apply weakening; exact HCb.
    + change (typ GA (shift Ea) (shift (BP.arr Ca (𝓤 a)))); apply weakening; exact HEa.
    + change (typ GA (shift Eb) (shift (BP.arr Cb (𝓤 b)))); apply weakening; exact HEb.
    + change (typ GA (shift Ec) (shift (BP.arr Cc (𝓤 (Nat.max (S a) b))))); apply weakening; exact HEc.
    + rewrite <- TB.product_type_shift; apply weakening; exact HP.
    + rewrite <- TB.law_family_shift; apply weakening; exact Hell.
    + rewrite <- beta_family_shift; apply weakening; exact Hq.
    + rewrite <- BF.carrier_family_shift; change (typ GA (var fzero) (GA !! fzero)); constructor.
  - unfold rank; change
      (Nat.max (CT.ceiling rs+2) (Nat.max (a+2) (Nat.max (b+2) (Nat.max (p+2) (d+1)))) =
       Nat.max (S (CT.ceiling rs))
        (Nat.max (CT.ceiling rs+2) (Nat.max (a+2) (Nat.max (b+2) (Nat.max (p+2) (d+1)))))); lia.
Qed.

Definition identity_body p d {n rs} (D : CT.telescope n rs) (B f u : Term nat n) :=
  reflexivity p d (BF.identity_carrier D B u) (BF.right_side D f u).
Definition plain_conclusion p d {n rs} (D : CT.telescope n rs) (B f u : Term nat n) :=
  reflexive_type p d (BF.identity_carrier D B u) (BF.right_side D f u).
Definition plain_arguments_type p d {n rs} (D : CT.telescope n rs) (A B : Term nat n) :=
  Π (BF.plain_function D A B) (Π (BF.plain_domain (BF.weaken D) (shift A))
    (plain_conclusion p d (BF.weaken (BF.weaken D)) (shift (shift B)) (var (fsucc fzero)) (var fzero))).
Definition identity_arguments p d {n rs} (D : CT.telescope n rs) (A B : Term nat n) :=
  lam (BF.plain_function D A B) (lam (BF.plain_domain (BF.weaken D) (shift A))
    (identity_body p d (BF.weaken (BF.weaken D)) (shift (shift B)) (var (fsucc fzero)) (var fzero))).
Definition plain_families_type b p d {n rs} (D : CT.telescope n rs) (A : Term nat n) :=
  Π (BF.plain_code b D A) (plain_arguments_type p d (BF.weaken D) (shift A) (var fzero)).
Definition identity_families b p d {n rs} (D : CT.telescope n rs) (A : Term nat n) :=
  lam (BF.plain_code b D A) (identity_arguments p d (BF.weaken D) (shift A) (var fzero)).
Definition identity_type a b p d {n rs} (D : CT.telescope n rs) :=
  Π (BF.carrier_family D (𝓤 a)) (plain_families_type b p d (BF.weaken D) (var fzero)).
Definition identity_family a b p d {n rs} (D : CT.telescope n rs) :=
  lam (BF.carrier_family D (𝓤 a)) (identity_families b p d (BF.weaken D) (var fzero)).

Lemma identity_arguments_typed a b p d n rs (D : CT.telescope n rs) G A B :
  CT.formed G D -> @typ nat RankSorts n G A (BF.carrier_family D (𝓤 a)) ->
  @typ nat RankSorts n G B (BF.plain_code b D A) ->
  @typ nat RankSorts n G (identity_arguments p d D A B) (plain_arguments_type p d D A B).
Proof.
  intros HD HA HB; set (GF := G & BF.plain_function D A B).
  set (GU := GF & BF.plain_domain (BF.weaken D) (shift A)).
  assert (HD' : CT.formed GU (BF.weaken (BF.weaken D))) by (apply BF.weaken_formed, BF.weaken_formed; exact HD).
  assert (HB' : typ GU (shift (shift B)) (BF.plain_code b (BF.weaken (BF.weaken D)) (shift (shift A)))).
  { rewrite <- !BF.plain_code_shift; apply weakening, weakening; exact HB. }
  assert (Hf : typ GU (var (fsucc fzero)) (BF.plain_function (BF.weaken (BF.weaken D)) (shift (shift A)) (shift (shift B)))).
  { rewrite <- !BF.plain_function_shift; change (typ GU (var (fsucc fzero)) (GU !! fsucc fzero)); constructor. }
  assert (Hu : typ GU (var fzero) (BF.plain_domain (BF.weaken (BF.weaken D)) (shift (shift A)))).
  { rewrite <- (BF.plain_domain_shift _ _ (BF.weaken D) (shift A)); change (typ GU (var fzero) (GU !! fzero)); constructor. }
  unfold identity_arguments, plain_arguments_type.
  apply typ_λ with (ℓ := CT.rank rs (Nat.max (S a) b)); [eapply BF.plain_function_sort; eassumption |].
  apply typ_λ with (ℓ := CT.rank rs a).
  - rewrite <- BF.plain_domain_shift; change (typ GF (shift (BF.plain_domain D A)) (shift (𝓤 (CT.rank rs a)))).
    apply weakening; eapply BF.plain_domain_sort; eassumption.
  - unfold identity_body, plain_conclusion; apply reflexivity_plain_typed with (c := CT.rank rs b).
    + eapply BF.identity_carrier_sort; eassumption.
    + eapply BF.right_side_typed; eassumption.
Qed.
Lemma identity_families_typed a b p d n rs (D : CT.telescope n rs) G A :
  CT.formed G D -> @typ nat RankSorts n G A (BF.carrier_family D (𝓤 a)) ->
  @typ nat RankSorts n G (identity_families b p d D A) (plain_families_type b p d D A).
Proof.
  intros HD HA; set (GB := G & BF.plain_code b D A); unfold identity_families, plain_families_type.
  apply typ_λ with (ℓ := CT.rank rs (S a)); [eapply BF.plain_code_sort; eassumption |].
  eapply identity_arguments_typed with (a := a) (b := b).
  - apply BF.weaken_formed; exact HD.
  - change (typ GB (shift A) (BF.carrier_family (BF.weaken D) (shift (𝓤 a)))).
    rewrite <- BF.carrier_family_shift; apply weakening; exact HA.
  - rewrite <- BF.plain_code_shift; change (typ GB (var fzero) (GB !! fzero)); constructor.
Qed.
Theorem identity_family_plain_typed a b p d n rs (D : CT.telescope n rs) G :
  CT.formed G D -> @typ nat RankSorts n G (identity_family a b p d D) (identity_type a b p d D).
Proof.
  intro HD; set (GA := G & BF.carrier_family D (𝓤 a)); unfold identity_family, identity_type.
  apply typ_λ with (ℓ := CT.rank rs 0); [apply BF.carrier_family_sort; [exact HD | constructor; reflexivity] |].
  eapply identity_families_typed with (a := a).
  - apply BF.weaken_formed; exact HD.
  - change (typ GA (var fzero) (BF.carrier_family (BF.weaken D) (shift (𝓤 a)))).
    rewrite <- BF.carrier_family_shift; change (typ GA (var fzero) (GA !! fzero)); constructor.
Qed.

Lemma beta_identity_shift a b p n rs (D : CT.telescope n rs) :
  shift (BF.identity_family a b p D) = BF.identity_family a b p (BF.weaken D).
Proof.
  pose proof (BF.identity_family_replace a b p n rs D (S n) (fun i => var (fsucc i))) as H.
  rewrite replace_as_rename, UR.telescope_replace_as_rename in H; exact H.
Qed.
Lemma arguments_identity_recovers a b p d n rs (D : CT.telescope n rs) A B :
  reduces_to nat n (arguments_type a b p d D (BP.type_identity a) (BP.type_identity b)
    (LF.identity_family a b) (BF.identity_family a b p D) A B) (plain_arguments_type p d D A B).
Proof.
  unfold arguments_type, plain_arguments_type.
  apply (@Π_cong_par nat (reduces_to nat) _ _ n); [apply BF.function_identity_recovers |].
  apply (@Π_cong_par nat (reduces_to nat) _ _ (S n)).
  - change (reduces_to nat (S n) (BF.domain_family (BF.weaken D) (BP.type_identity a) (shift A))
      (BF.plain_domain (BF.weaken D) (shift A))); apply BF.domain_identity_recovers.
  - rewrite !beta_identity_shift.
    change (reduces_to nat (S (S n))
      (instance_type a b p d (BF.weaken (BF.weaken D)) (BP.type_identity a) (BP.type_identity b)
        (LF.identity_family a b) (BF.identity_family a b p (BF.weaken (BF.weaken D)))
        (shift (shift A)) (shift (shift B)) (var (fsucc fzero)) (var fzero))
      (reflexive_type p d (BF.identity_carrier (BF.weaken (BF.weaken D)) (shift (shift B)) (var fzero))
        (BF.right_side (BF.weaken (BF.weaken D)) (var (fsucc fzero)) (var fzero)))).
    apply identity_instance_type_recovers.
Qed.
Theorem identity_type_recovers a b p d n rs (D : CT.telescope n rs) :
  reduces_to nat n (family_type a b p d D (𝓤 a) (𝓤 b) (BP.type_identity a)
    (BP.type_identity b) (LF.identity_family a b) (BF.identity_family a b p D)) (identity_type a b p d D).
Proof.
  unfold family_type, families_type, identity_type, plain_families_type.
  apply (@Π_cong_par nat (reduces_to nat) _ _ n); [reflexivity |].
  apply (@Π_cong_par nat (reduces_to nat) _ _ (S n)).
  - change (reduces_to nat (S n) (BF.code_family (BF.weaken D) (𝓤 b) (BP.type_identity a) (var fzero))
      (BF.plain_code b (BF.weaken D) (var fzero))); apply BF.code_identity_recovers.
  - rewrite !beta_identity_shift.
    change (reduces_to nat (S (S n))
      (arguments_type a b p d (BF.weaken (BF.weaken D)) (BP.type_identity a) (BP.type_identity b)
        (LF.identity_family a b) (BF.identity_family a b p (BF.weaken (BF.weaken D))) (var (fsucc fzero)) (var fzero))
      (plain_arguments_type p d (BF.weaken (BF.weaken D)) (var (fsucc fzero)) (var fzero))).
    apply arguments_identity_recovers.
Qed.
Theorem identity_family_typed a b p d n rs (D : CT.telescope n rs) G :
  CT.formed G D -> @typ nat RankSorts n G (identity_family a b p d D)
    (family_type a b p d D (𝓤 a) (𝓤 b) (BP.type_identity a) (BP.type_identity b)
      (LF.identity_family a b) (BF.identity_family a b p D)).
Proof.
  intro HD; eapply typ_conv with (T := identity_type a b p d D) (ℓ := rank rs a b p d).
  - apply identity_family_plain_typed; exact HD.
  - eapply family_type_sort with (Cc := 𝓤 (Nat.max (S a) b))
      (Ec := BP.type_identity (Nat.max (S a) b)) (P := TP.identity_product a b);
      try exact HD; try (constructor; reflexivity); try apply BP.type_identity_typing.
    + apply TP.identity_product_typed.
    + apply LF.identity_family_typed.
    + apply BF.identity_family_typed; exact HD.
  - apply def_equiv_prop; exists (identity_type a b p d D); split;
      [reflexivity | apply identity_type_recovers].
Qed.

Lemma carrier_replace m rs (D : CT.telescope m rs) n sigma Eb B u :
  replace sigma (carrier D Eb B u) = carrier (CT.replace_telescope D n sigma)
    (replace sigma Eb) (replace sigma B) (replace sigma u).
Proof.
  unfold carrier, BF.lift; rewrite CT.close_type_replace; cbn [replace].
  rewrite UT.lift_sub_base, !UT.apply_under_replace; reflexivity.
Qed.
Lemma left_side_replace a b m rs (D : CT.telescope m rs) n sigma Ea Eb ell A B f u :
  replace sigma (left_side a b D Ea Eb ell A B f u) =
    left_side a b (CT.replace_telescope D n sigma) (replace sigma Ea) (replace sigma Eb)
      (replace sigma ell) (replace sigma A) (replace sigma B) (replace sigma f) (replace sigma u).
Proof.
  unfold left_side, BF.lift; rewrite CT.close_term_replace,
    TarskiOperations.TarskiOperations.cast_app_replace, TarskiOperations.TarskiOperations.cast_abs_replace.
  cbn [replace]; rewrite !UT.lift_sub_base, !UT.apply_under_replace; reflexivity.
Qed.
Lemma instance_type_replace a b p d m rs (D : CT.telescope m rs) n sigma Ea Eb ell q A B f u :
  replace sigma (instance_type a b p d D Ea Eb ell q A B f u) =
    instance_type a b p d (CT.replace_telescope D n sigma) (replace sigma Ea) (replace sigma Eb)
      (replace sigma ell) (replace sigma q) (replace sigma A) (replace sigma B) (replace sigma f) (replace sigma u).
Proof.
  unfold instance_type; rewrite law_replace, carrier_replace, left_side_replace, BF.right_side_replace; reflexivity.
Qed.
Lemma arguments_type_replace a b p d m rs (D : CT.telescope m rs) n sigma Ea Eb ell q A B :
  replace sigma (arguments_type a b p d D Ea Eb ell q A B) =
    arguments_type a b p d (CT.replace_telescope D n sigma) (replace sigma Ea) (replace sigma Eb)
      (replace sigma ell) (replace sigma q) (replace sigma A) (replace sigma B).
Proof.
  unfold arguments_type; cbn [replace]; rewrite BF.function_family_replace, BF.domain_family_replace, instance_type_replace.
  unfold BF.weaken; rewrite !UR.telescope_shift_replace, !replace_lift_shift; reflexivity.
Qed.
Lemma families_type_replace a b p d m rs (D : CT.telescope m rs) n sigma Cb Ea Eb ell q A :
  replace sigma (families_type a b p d D Cb Ea Eb ell q A) =
    families_type a b p d (CT.replace_telescope D n sigma) (replace sigma Cb) (replace sigma Ea)
      (replace sigma Eb) (replace sigma ell) (replace sigma q) (replace sigma A).
Proof.
  unfold families_type; cbn [replace]; rewrite BF.code_family_replace, arguments_type_replace.
  unfold BF.weaken; rewrite UR.telescope_shift_replace, !replace_lift_shift; reflexivity.
Qed.
Theorem family_type_replace a b p d m rs (D : CT.telescope m rs) n sigma Ca Cb Ea Eb ell q :
  replace sigma (family_type a b p d D Ca Cb Ea Eb ell q) =
    family_type a b p d (CT.replace_telescope D n sigma) (replace sigma Ca) (replace sigma Cb)
      (replace sigma Ea) (replace sigma Eb) (replace sigma ell) (replace sigma q).
Proof.
  unfold family_type; cbn [replace]; rewrite BF.carrier_family_replace, families_type_replace.
  unfold BF.weaken; rewrite UR.telescope_shift_replace, !replace_lift_shift; reflexivity.
Qed.
Theorem family_type_rename a b p d m rs (D : CT.telescope m rs) n rho Ca Cb Ea Eb ell q :
  rename rho (family_type a b p d D Ca Cb Ea Eb ell q) =
    family_type a b p d (CT.rename_telescope D n rho) (rename rho Ca) (rename rho Cb)
      (rename rho Ea) (rename rho Eb) (rename rho ell) (rename rho q).
Proof.
  pose proof (family_type_replace a b p d m rs D n (fun i => var (rho i)) Ca Cb Ea Eb ell q) as H.
  rewrite !replace_as_rename, UR.telescope_replace_as_rename in H; exact H.
Qed.

Lemma identity_body_replace p d m rs (D : CT.telescope m rs) n sigma B f u :
  replace sigma (identity_body p d D B f u) = identity_body p d (CT.replace_telescope D n sigma)
    (replace sigma B) (replace sigma f) (replace sigma u).
Proof. unfold identity_body; rewrite reflexivity_replace, BF.identity_carrier_replace, BF.right_side_replace; reflexivity. Qed.
Lemma identity_arguments_replace p d m rs (D : CT.telescope m rs) n sigma A B :
  replace sigma (identity_arguments p d D A B) = identity_arguments p d (CT.replace_telescope D n sigma)
    (replace sigma A) (replace sigma B).
Proof.
  unfold identity_arguments; cbn [replace]; rewrite BF.plain_function_replace, BF.plain_domain_replace, identity_body_replace.
  unfold BF.weaken; rewrite !UR.telescope_shift_replace, !replace_lift_shift; reflexivity.
Qed.
Lemma identity_families_replace b p d m rs (D : CT.telescope m rs) n sigma A :
  replace sigma (identity_families b p d D A) = identity_families b p d (CT.replace_telescope D n sigma) (replace sigma A).
Proof.
  unfold identity_families; cbn [replace]; rewrite BF.plain_code_replace, identity_arguments_replace.
  unfold BF.weaken; rewrite UR.telescope_shift_replace, !replace_lift_shift; reflexivity.
Qed.
Theorem identity_family_replace a b p d m rs (D : CT.telescope m rs) n sigma :
  replace sigma (identity_family a b p d D) = identity_family a b p d (CT.replace_telescope D n sigma).
Proof.
  unfold identity_family; cbn [replace]; rewrite BF.carrier_family_replace, identity_families_replace.
  unfold BF.weaken; rewrite UR.telescope_shift_replace; reflexivity.
Qed.

Lemma arguments_specialize a b p d n rs (D : CT.telescope n rs) G Ea Eb ell q A B h f u :
  @typ nat RankSorts n G h (arguments_type a b p d D Ea Eb ell q A B) ->
  @typ nat RankSorts n G f (BF.function_family D Ea Eb A B) ->
  @typ nat RankSorts n G u (BF.domain_family D Ea A) ->
  @typ nat RankSorts n G (app (app h f) u) (instance_type a b p d D Ea Eb ell q A B f u).
Proof.
  intros Hh Hf Hu; unfold arguments_type in Hh.
  pose proof (typ_app (BF.function_family D Ea Eb A B) Hh Hf) as H1.
  assert (Hs : subst (Π (BF.domain_family (BF.weaken D) (shift Ea) (shift A))
    (instance_type a b p d (BF.weaken (BF.weaken D)) (shift (shift Ea)) (shift (shift Eb))
      (shift (shift ell)) (shift (shift q)) (shift (shift A)) (shift (shift B)) (var (fsucc fzero)) (var fzero))) f =
    Π (BF.domain_family D Ea A) (instance_type a b p d (BF.weaken D) (shift Ea) (shift Eb)
      (shift ell) (shift q) (shift A) (shift B) (shift f) (var fzero))).
  { unfold subst; cbn [replace]; rewrite BF.domain_family_replace, instance_type_replace.
    unfold BF.weaken; rewrite UR.telescope_shift_replace, !UR.telescope_subst_shift.
    rewrite !replace_lift_shift; syntax_simp; cbn [transpose fin_match]; rewrite !BP.replace_fsucc; reflexivity. }
  rewrite Hs in H1; pose proof (typ_app (BF.domain_family D Ea A) H1 Hu) as H2.
  assert (Hs2 : subst (instance_type a b p d (BF.weaken D) (shift Ea) (shift Eb) (shift ell)
    (shift q) (shift A) (shift B) (shift f) (var fzero)) u = instance_type a b p d D Ea Eb ell q A B f u).
  { unfold subst; rewrite instance_type_replace; unfold BF.weaken; rewrite UR.telescope_subst_shift; syntax_simp. }
  rewrite Hs2 in H2; exact H2.
Qed.
Theorem family_specialize a b p d n rs (D : CT.telescope n rs) G Ca Cb Ea Eb ell q h A B f u :
  @typ nat RankSorts n G h (family_type a b p d D Ca Cb Ea Eb ell q) ->
  @typ nat RankSorts n G A (BF.carrier_family D Ca) ->
  @typ nat RankSorts n G B (BF.code_family D Cb Ea A) ->
  @typ nat RankSorts n G f (BF.function_family D Ea Eb A B) ->
  @typ nat RankSorts n G u (BF.domain_family D Ea A) ->
  @typ nat RankSorts n G (applied h A B f u) (instance_type a b p d D Ea Eb ell q A B f u).
Proof.
  intros Hh HA HB Hf Hu; unfold family_type in Hh.
  pose proof (typ_app (BF.carrier_family D Ca) Hh HA) as H1.
  assert (H1s : subst (families_type a b p d (BF.weaken D) (shift Cb) (shift Ea) (shift Eb) (shift ell) (shift q) (var fzero)) A =
    families_type a b p d D Cb Ea Eb ell q A).
  { unfold subst; rewrite families_type_replace; unfold BF.weaken; rewrite UR.telescope_subst_shift; syntax_simp. }
  rewrite H1s in H1; unfold families_type in H1.
  pose proof (typ_app (BF.code_family D Cb Ea A) H1 HB) as H2.
  assert (H2s : subst (arguments_type a b p d (BF.weaken D) (shift Ea) (shift Eb) (shift ell) (shift q) (shift A) (var fzero)) B =
    arguments_type a b p d D Ea Eb ell q A B).
  { unfold subst; rewrite arguments_type_replace; unfold BF.weaken; rewrite UR.telescope_subst_shift; syntax_simp. }
  rewrite H2s in H2; eapply arguments_specialize; eassumption.
Qed.

Lemma identity_arguments_specializes p d n rs (D : CT.telescope n rs) A B f u :
  reduces_to nat n (app (app (identity_arguments p d D A B) f) u) (identity_body p d D B f u).
Proof.
  unfold identity_arguments; eapply rtc_step; [apply step_app_left, step_beta |].
  unfold subst; cbn [replace]; rewrite BF.plain_domain_replace, identity_body_replace.
  unfold BF.weaken; rewrite UR.telescope_shift_replace, !UR.telescope_subst_shift.
  rewrite !replace_lift_shift; syntax_simp; cbn [transpose fin_match]; rewrite !BP.replace_fsucc.
  eapply rtc_step; [apply step_beta |].
  unfold subst; rewrite identity_body_replace, UR.telescope_subst_shift; syntax_simp.
  reflexivity.
Qed.
Theorem identity_family_specializes a b p d n rs (D : CT.telescope n rs) A B f u :
  reduces_to nat n (applied (identity_family a b p d D) A B f u)
    (reflexivity p d (BF.identity_carrier D B u) (BF.right_side D f u)).
Proof.
  unfold applied, identity_family; eapply rtc_step; [apply step_app_left, step_app_left, step_app_left, step_beta |].
  unfold subst; rewrite identity_families_replace; unfold BF.weaken; rewrite UR.telescope_subst_shift; syntax_simp.
  unfold identity_families; eapply rtc_step; [apply step_app_left, step_app_left, step_beta |].
  unfold subst; rewrite identity_arguments_replace; unfold BF.weaken; rewrite UR.telescope_subst_shift; syntax_simp.
  apply identity_arguments_specializes.
Qed.
Theorem identity_transport_recovers a b p d n rs (D : CT.telescope n rs) A B f u P z :
  reduces_to nat n (app (app (applied (identity_family a b p d D) A B f u) P) z)
    (DE.graph_refl d (BF.identity_carrier D B u) P (BF.right_side D f u) z).
Proof.
  eapply rtc_trans; [apply (@app_cong_l nat (reduces_to nat) _ n), (@app_cong_l nat (reduces_to nat) _ n), identity_family_specializes |].
  apply reflexivity_specializes.
Qed.

Theorem law_specialize p d n (G : Ctx nat n) C l r e h P z :
  @typ nat RankSorts n G h (law p d C l r e) ->
  @typ nat RankSorts n G P (IE.motive_type p C) ->
  @typ nat RankSorts n G z (app P l) ->
  @typ nat RankSorts n G (app (app h P) z)
    (DE.graph_eq d C P l z r (IE.transport e P z)).
Proof.
  intros Hh HP Hz; unfold law in Hh.
  pose proof (typ_app (IE.motive_type p C) Hh HP) as H1.
  unfold subst in H1; cbn [replace] in H1; rewrite DE.graph_eq_replace in H1.
  cbn [IE.transport replace transpose fin_match] in H1.
  rewrite !replace_lift_shift in H1; revert H1; syntax_simp; intro H1.
  pose proof (typ_app (app P l) H1 Hz) as H2.
  unfold subst in H2; rewrite DE.graph_eq_replace in H2.
  cbn [IE.transport replace transpose fin_match] in H2; revert H2; syntax_simp; intro H2; exact H2.
Qed.

Lemma carrier_normal n rs (D : CT.telescope n rs) (Eb B u : Fin n) :
  CT.normal_annotations D = true -> normalb (carrier D (var Eb) (var B) (var u)) = true.
Proof.
  intro HD; unfold carrier, BF.lift; rewrite CT.close_type_normal, HD; cbn [rename normalb isLambda].
  rewrite !UT.apply_under_normal, !UT.apply_under_neutral by reflexivity; reflexivity.
Qed.
Lemma left_side_normal a b n rs (D : CT.telescope n rs) (Ea Eb ell A B f u : Fin n) :
  CT.normal_annotations D = true -> normalb (left_side a b D (var Ea) (var Eb) (var ell) (var A) (var B) (var f) (var u)) = true.
Proof.
  intro HD; pose proof (BF.conclusion_normal a b 0 n rs D Ea Eb ell A B f u HD) as H.
  change (normalb (IE.eq_type 0 (carrier D (var Eb) (var B) (var u))
    (left_side a b D (var Ea) (var Eb) (var ell) (var A) (var B) (var f) (var u))
    (BF.right_side D (var f) (var u))) = true) in H.
  unfold IE.eq_type, IE.motive_type, BP.arr, shift in H.
  repeat progress (cbn [normalb isLambda] in H; rewrite ?UT.normalb_rename in H).
  repeat rewrite andb_true_iff in H; tauto.
Qed.
Lemma right_side_normal n rs (D : CT.telescope n rs) (f u : Fin n) :
  CT.normal_annotations D = true -> normalb (BF.right_side D (var f) (var u)) = true.
Proof.
  intro HD; unfold BF.right_side; rewrite CT.close_term_normal, HD; cbn [normalb isLambda].
  rewrite !UT.apply_under_normal, !UT.apply_under_neutral by reflexivity; reflexivity.
Qed.
Lemma instance_type_normal a b p d n rs (D : CT.telescope n rs) (Ea Eb ell q A B f u : Fin n) :
  CT.normal_annotations D = true ->
  normalb (instance_type a b p d D (var Ea) (var Eb) (var ell) (var q) (var A) (var B) (var f) (var u)) = true.
Proof.
  intro HD; apply law_normal; try (apply carrier_normal || apply left_side_normal || apply right_side_normal);
    try exact HD; reflexivity.
Qed.
Theorem family_type_normal a b p d n rs (D : CT.telescope n rs) (Ca Cb Ea Eb ell q : Fin n) :
  CT.normal_annotations D = true -> normalb (family_type a b p d D (var Ca) (var Cb) (var Ea) (var Eb) (var ell) (var q)) = true.
Proof.
  intro HD; unfold family_type, families_type, arguments_type; cbn [normalb shift rename].
  rewrite BF.carrier_family_normal by assumption || reflexivity.
  rewrite BF.code_family_normal, BF.function_family_normal, BF.domain_family_normal, instance_type_normal;
    rewrite ?BF.weaken_normal; assumption || reflexivity.
Qed.
Lemma identity_body_normal p d n rs (D : CT.telescope n rs) (B f u : Fin n) :
  CT.normal_annotations D = true -> normalb (identity_body p d D (var B) (var f) (var u)) = true.
Proof.
  intro HD; apply reflexivity_normal; [| apply right_side_normal; exact HD].
  unfold BF.identity_carrier; rewrite CT.close_type_normal, HD; cbn [normalb isLambda].
  rewrite !UT.apply_under_normal, !UT.apply_under_neutral by reflexivity; reflexivity.
Qed.
Theorem identity_family_normal a b p d n rs (D : CT.telescope n rs) :
  CT.normal_annotations D = true -> normalb (identity_family a b p d D) = true.
Proof.
  intro HD; unfold identity_family, identity_families, identity_arguments; cbn [normalb shift rename].
  rewrite BF.carrier_family_normal by assumption || reflexivity.
  rewrite BF.plain_code_normal, BF.plain_function_normal, BF.plain_domain_normal, identity_body_normal;
    rewrite ?BF.weaken_normal; assumption || reflexivity.
Qed.
Theorem rank_bounded k rs a b p d :
  Forall (fun r => r <= k) rs -> a <= k -> b <= k -> p <= k -> d <= k -> rank rs a b p d <= k+3.
Proof.
  intros Hrs Ha Hb Hp Hd; pose proof (CT.rank_bounded rs k 0 Hrs).
  unfold rank, CT.ceiling; lia.
Qed.

Print Assumptions family_specialize.
Print Assumptions law_specialize.
Print Assumptions identity_transport_recovers.
Print Assumptions identity_family_specializes.
Print Assumptions family_type_normal.
Print Assumptions family_type_replace.
Print Assumptions family_type_rename.
Print Assumptions identity_family_normal.
Print Assumptions identity_family_replace.
Print Assumptions rank_bounded.
Print Assumptions identity_family_plain_typed.
Print Assumptions identity_type_recovers.
Print Assumptions identity_family_typed.
Print Assumptions family_type_sort.
Print Assumptions instance_type_sort.
Print Assumptions identity_instance_type_recovers.
Print Assumptions law_sort.
Print Assumptions law_replace.
Print Assumptions law_reflexivity_reduces.
Print Assumptions reflexivity_typed.
Print Assumptions reflexivity_specializes.
Print Assumptions law_normal.
Print Assumptions reflexivity_normal.
End ContextualTransportLaw.
