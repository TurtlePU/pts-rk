From Stdlib Require Import Bool.Bool Lists.List Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting Congruence DefEq.
From PTSrk.NormalizationComplexity Require Import Greedy Morphisms.
From PTSrk.SelfInterpreter Require Import BrownPalsberg IndexedEquality ChurchSyntaxFaithful
  TarskiProducts TarskiOperations TarskiLawFamily ContextualTelescope UniformTelescope
  UniformTelescopeRecovery OpenTelescopeRecovery ContextualTelescopeRun
  TelescopeBetaFamily UniformContextualBeta TelescopeBetaSignature.
Import Context ListNotations.

(** Direct original application of a uniform contextual-beta field to
    independently formed concrete domains and supplied typed payloads. *)
Module ConcreteContextualBeta.
Module BP := BrownPalsberg.BrownPalsberg.
Module IE := IndexedEquality.IndexedEquality.
Module TP := TarskiProducts.TarskiProducts.
Module TO := TarskiOperations.TarskiOperations.
Module LF := TarskiLawFamily.TarskiLawFamily.
Module CT := ContextualTelescope.ContextualTelescope.
Module UT := UniformTelescope.UniformTelescope.
Module UR := UniformTelescopeRecovery.UniformTelescopeRecovery.
Module OR := OpenTelescopeRecovery.OpenTelescopeRecovery.
Module TR := ContextualTelescopeRun.ContextualTelescopeRun.
Module BF := TelescopeBetaFamily.TelescopeBetaFamily.
Module UC := UniformContextualBeta.UniformContextualBeta.
Module TS := TelescopeBetaSignature.TelescopeBetaSignature.

Definition instantiate {n rs} (W : CT.telescope n rs) (q : Term nat n) :=
  TR.run (UT.parameters n rs) (UR.realize W) q.

Lemma base_replace n rs (W : CT.telescope n rs) t :
  replace (@TR.base n (UT.parameter_ranks [] rs) n (UR.realize W)) t = t.
Proof.
  rewrite <- (replace_var t) at 2; apply replace_ext; intro i; apply OR.realize_base.
Qed.

Lemma lifted_replace n rs (W : CT.telescope n rs) t :
  replace (UR.realize W) (BF.lift (UT.parameter_ranks [] rs) t) = t.
Proof. unfold BF.lift; rewrite replace_rename; apply base_replace. Qed.

Theorem instantiate_typed a b d n rs (W : CT.telescope n rs) G q Ca Cb Ea Eb ell :
  CT.formed G W ->
  @typ nat RankSorts n G q (UC.family_type a b d rs Ca Cb Ea Eb ell) ->
  @typ nat RankSorts n G (instantiate W q)
    (BF.family_type a b d (OR.realized_domains W) Ca Cb Ea Eb ell).
Proof.
  intros HW Hq.
  assert (Hq' : typ G q (replace (@TR.base n (UT.parameter_ranks [] rs) n (UR.realize W))
    (UC.family_type a b d rs Ca Cb Ea Eb ell))) by (rewrite base_replace; exact Hq).
  unfold UC.family_type in Hq'; unfold instantiate.
  pose proof (TR.run_typing n (UT.parameter_ranks [] rs) (UT.parameters n rs)
    n G G (UR.realize W) q _ (proj1 (UR.realize_correct n rs W G HW)) Hq') as H.
  rewrite BF.family_type_replace, !lifted_replace in H; exact H.
Qed.

Theorem instantiate_identity_recovers a b d n rs (W : CT.telescope n rs) :
  reduces_to nat n (instantiate W (UC.identity_family a b d rs))
    (BF.identity_family a b d (OR.realized_domains W)).
Proof.
  pose proof (TR.run_closure n (UT.parameter_ranks [] rs) (UT.parameters n rs)
    n (UR.realize W) (BF.identity_family a b d (UT.domains n rs))) as H.
  rewrite base_replace, BF.identity_family_replace in H; exact H.
Qed.

Theorem instantiated_identity_typed a b d n rs (W : CT.telescope n rs) G :
  CT.formed G W ->
  @typ nat RankSorts n G (instantiate W (UC.identity_family a b d rs))
    (BF.family_type a b d (OR.realized_domains W) (𝓤 a) (𝓤 b)
      (BP.type_identity a) (BP.type_identity b) (LF.identity_family a b)).
Proof. intro HW; apply instantiate_typed; [exact HW | apply UC.identity_family_typed]. Qed.

Definition apply_family {n rs} (W : CT.telescope n rs) (q A B f u : Term nat n) :=
  app (app (app (app (instantiate W q) A) B) f) u.

Theorem apply_family_typed a b d n rs (W : CT.telescope n rs) G q Ca Cb Ea Eb ell A B f u :
  CT.formed G W ->
  @typ nat RankSorts n G q (UC.family_type a b d rs Ca Cb Ea Eb ell) ->
  @typ nat RankSorts n G A (BF.carrier_family (OR.realized_domains W) Ca) ->
  @typ nat RankSorts n G B (BF.code_family (OR.realized_domains W) Cb Ea A) ->
  @typ nat RankSorts n G f (BF.function_family (OR.realized_domains W) Ea Eb A B) ->
  @typ nat RankSorts n G u (BF.domain_family (OR.realized_domains W) Ea A) ->
  @typ nat RankSorts n G (apply_family W q A B f u)
    (BF.conclusion a b d (OR.realized_domains W) Ea Eb ell A B f u).
Proof.
  intros HW Hq HA HB Hf Hu; unfold apply_family.
  eapply BF.family_specialize; try eassumption; apply instantiate_typed; assumption.
Qed.

Theorem apply_identity_recovers a b d n rs (W : CT.telescope n rs) A B f u :
  reduces_to nat n (apply_family W (UC.identity_family a b d rs) A B f u)
    (IE.refl_case d (BF.identity_carrier (OR.realized_domains W) B u)
      (BF.right_side (OR.realized_domains W) f u)).
Proof.
  unfold apply_family; eapply rtc_trans; [| apply BF.identity_family_specializes].
  repeat apply (@app_cong_l nat (reduces_to nat) _ n); apply instantiate_identity_recovers.
Qed.

Lemma refl_case_reduces d n (C C' t t' : Term nat n) :
  reduces_to nat n C C' -> reduces_to nat n t t' ->
  reduces_to nat n (IE.refl_case d C t) (IE.refl_case d C' t').
Proof.
  intros HC Ht; unfold IE.refl_case, IE.motive_type.
  apply (@λ_cong_par nat (reduces_to nat) _ _ n).
  - apply BP.arr_reduces; [exact HC | reflexivity].
  - apply (@λ_cong_par nat (reduces_to nat) _ _ (S n)); [| reflexivity].
    apply (@app_cong_r nat (reduces_to nat) _ (S n)), rename_rtc; exact Ht.
Qed.

Theorem concrete_identity_recovers a b d n rs (W : CT.telescope n rs) G A B f u :
  CT.formed G W ->
  reduces_to nat n
    (apply_family W (UC.identity_family a b d rs)
      (CT.close_term W A) (CT.close_term W B) (CT.close_term W f) (CT.close_term W u))
    (IE.refl_case d (CT.close_type W (app B u)) (CT.close_term W (app f u))).
Proof.
  intro HW; eapply rtc_trans; [apply apply_identity_recovers |].
  apply refl_case_reduces.
  - unfold BF.identity_carrier; eapply rtc_trans; [apply CT.close_type_reduces |].
    + apply (@app_cong_par nat (reduces_to nat) _ _ _); apply OR.realized_spine_recovers.
    + rewrite <- OR.realized_body_app; apply OR.realize_type_recovers with (G := G); exact HW.
  - unfold BF.right_side; eapply rtc_trans; [apply CT.close_term_reduces |].
    + apply (@app_cong_par nat (reduces_to nat) _ _ _); apply OR.realized_spine_recovers.
    + rewrite <- OR.realized_body_app; apply OR.realize_term_recovers with (G := G); exact HW.
Qed.

Lemma realized_code_family n rs (C E A : Term nat (CT.scope rs n)) :
  OR.realized_body rs (TP.code_family C E A) = TP.code_family
    (OR.realized_body rs C) (OR.realized_body rs E) (OR.realized_body rs A).
Proof.
  rewrite !OR.realized_body_as_rename; unfold TP.code_family, BP.arr; syntax_simp.
Qed.

Lemma realized_decoded_product n rs (Ea Eb A B : Term nat (CT.scope rs n)) :
  OR.realized_body rs (TP.decoded_product Ea Eb A B) = TP.decoded_product
    (OR.realized_body rs Ea) (OR.realized_body rs Eb)
    (OR.realized_body rs A) (OR.realized_body rs B).
Proof.
  rewrite !OR.realized_body_as_rename.
  pose proof (TO.decoded_product_replace _ _ (fun i => var (OR.realized_ren n rs i)) Ea Eb A B) as H.
  rewrite !replace_as_rename in H; exact H.
Qed.

Lemma decoded_product_reduces n (Ea Eb A A' B B' : Term nat n) :
  reduces_to nat n A A' -> reduces_to nat n B B' ->
  reduces_to nat n (TP.decoded_product Ea Eb A B) (TP.decoded_product Ea Eb A' B').
Proof.
  intros HA HB; unfold TP.decoded_product, DependentPHOAS.DependentPHOAS.product.
  apply (@Π_cong_par nat (reduces_to nat) _ _ n).
  - apply (@app_cong_r nat (reduces_to nat) _ n); exact HA.
  - apply (@app_cong_r nat (reduces_to nat) _ (S n)),
      (@app_cong_l nat (reduces_to nat) _ (S n)), rename_rtc; exact HB.
Qed.

Theorem carrier_argument_typed n rs (W : CT.telescope n rs) G Ca A :
  CT.formed G W -> @typ nat RankSorts n G Ca (𝓤 0) ->
  @typ nat RankSorts _ (CT.context W G) A (BF.lift rs Ca) ->
  @typ nat RankSorts n G (CT.close_term W A) (BF.carrier_family (OR.realized_domains W) Ca).
Proof.
  intros HW HC HA.
  pose proof (OR.concrete_argument_typed n rs W G A (BF.lift rs Ca) 0 HW
    (BF.lift_sort n rs W G Ca 0 HC) HA) as H.
  unfold BF.lift in H; rewrite OR.realized_body_base in H; exact H.
Qed.

Theorem code_argument_typed a n rs (W : CT.telescope n rs) G Ca Cb Ea A B :
  CT.formed G W -> @typ nat RankSorts n G Ca (𝓤 0) -> @typ nat RankSorts n G Cb (𝓤 0) ->
  @typ nat RankSorts n G Ea (BP.arr Ca (𝓤 a)) ->
  @typ nat RankSorts _ (CT.context W G) A (BF.lift rs Ca) ->
  @typ nat RankSorts _ (CT.context W G) B (TP.code_family (BF.lift rs Cb) (BF.lift rs Ea) A) ->
  @typ nat RankSorts n G (CT.close_term W B)
    (BF.code_family (OR.realized_domains W) Cb Ea (CT.close_term W A)).
Proof.
  intros HW HCa HCb HEa HA HB.
  assert (HT : typ (CT.context W G) (TP.code_family (BF.lift rs Cb) (BF.lift rs Ea) A) (𝓤 (S a))).
  { eapply TP.code_family_sort; [apply BF.lift_sort; exact HCb | apply BF.lift_decoder; exact HEa | exact HA]. }
  pose proof (OR.concrete_argument_typed n rs W G B _ (S a) HW HT HB) as H.
  eapply typ_conv with (T := CT.close_type (OR.realized_domains W)
    (OR.realized_body rs (TP.code_family (BF.lift rs Cb) (BF.lift rs Ea) A)))
    (ℓ := CT.rank (UT.extend_ranks [] rs) (S a)); [exact H | |].
  - eapply BF.code_family_sort with (Ca := Ca).
    + apply OR.realized_domains_formed; exact HW.
    + exact HCb.
    + exact HEa.
    + apply carrier_argument_typed; assumption.
  - apply def_equiv_prop; eexists; split; [reflexivity |].
    unfold BF.code_family; rewrite realized_code_family; unfold BF.lift; rewrite !OR.realized_body_base.
    apply CT.close_type_reduces; unfold TP.code_family; apply BP.arr_reduces; [| reflexivity].
    apply (@app_cong_r nat (reduces_to nat) _ _), OR.realized_spine_recovers.
Qed.

Theorem function_argument_typed a b n rs (W : CT.telescope n rs) G Ca Cb Ea Eb A B f :
  CT.formed G W -> @typ nat RankSorts n G Ca (𝓤 0) -> @typ nat RankSorts n G Cb (𝓤 0) ->
  @typ nat RankSorts n G Ea (BP.arr Ca (𝓤 a)) ->
  @typ nat RankSorts n G Eb (BP.arr Cb (𝓤 b)) ->
  @typ nat RankSorts _ (CT.context W G) A (BF.lift rs Ca) ->
  @typ nat RankSorts _ (CT.context W G) B (TP.code_family (BF.lift rs Cb) (BF.lift rs Ea) A) ->
  @typ nat RankSorts _ (CT.context W G) f
    (TP.decoded_product (BF.lift rs Ea) (BF.lift rs Eb) A B) ->
  @typ nat RankSorts n G (CT.close_term W f)
    (BF.function_family (OR.realized_domains W) Ea Eb (CT.close_term W A) (CT.close_term W B)).
Proof.
  intros HW HCa HCb HEa HEb HA HB Hf.
  assert (HT : typ (CT.context W G)
    (TP.decoded_product (BF.lift rs Ea) (BF.lift rs Eb) A B) (𝓤 (Nat.max (S a) b))).
  { eapply TP.decoded_product_sort.
    - apply BF.lift_decoder; exact HEa.
    - apply BF.lift_decoder; exact HEb.
    - exact HA.
    - exact HB. }
  pose proof (OR.concrete_argument_typed n rs W G f _ (Nat.max (S a) b) HW HT Hf) as H.
  eapply typ_conv with (T := CT.close_type (OR.realized_domains W)
    (OR.realized_body rs (TP.decoded_product (BF.lift rs Ea) (BF.lift rs Eb) A B)))
    (ℓ := CT.rank (UT.extend_ranks [] rs) (Nat.max (S a) b)); [exact H | |].
  - eapply BF.function_family_sort with (Ca := Ca) (Cb := Cb).
    + apply OR.realized_domains_formed; exact HW.
    + exact HEa.
    + exact HEb.
    + apply carrier_argument_typed; assumption.
    + eapply code_argument_typed with (a := a) (Ca := Ca); eassumption.
  - apply def_equiv_prop; eexists; split; [reflexivity |].
    unfold BF.function_family; rewrite realized_decoded_product; unfold BF.lift;
      rewrite !OR.realized_body_base.
    apply CT.close_type_reduces, decoded_product_reduces; apply OR.realized_spine_recovers.
Qed.

Theorem domain_argument_typed a n rs (W : CT.telescope n rs) G Ca Ea A u :
  CT.formed G W -> @typ nat RankSorts n G Ca (𝓤 0) ->
  @typ nat RankSorts n G Ea (BP.arr Ca (𝓤 a)) ->
  @typ nat RankSorts _ (CT.context W G) A (BF.lift rs Ca) ->
  @typ nat RankSorts _ (CT.context W G) u (app (BF.lift rs Ea) A) ->
  @typ nat RankSorts n G (CT.close_term W u)
    (BF.domain_family (OR.realized_domains W) Ea (CT.close_term W A)).
Proof.
  intros HW HCa HEa HA Hu.
  assert (HT : typ (CT.context W G) (app (BF.lift rs Ea) A) (𝓤 a)).
  { eapply BP.arr_apply; [apply BF.lift_decoder; exact HEa | exact HA]. }
  pose proof (OR.concrete_argument_typed n rs W G u _ a HW HT Hu) as H.
  eapply typ_conv with (T := CT.close_type (OR.realized_domains W)
    (OR.realized_body rs (app (BF.lift rs Ea) A)))
    (ℓ := CT.rank (UT.extend_ranks [] rs) a); [exact H | |].
  - eapply BF.domain_family_sort with (Ca := Ca).
    + apply OR.realized_domains_formed; exact HW.
    + exact HEa.
    + apply carrier_argument_typed; assumption.
  - apply def_equiv_prop; eexists; split; [reflexivity |].
    unfold BF.domain_family; rewrite OR.realized_body_app; unfold BF.lift;
      rewrite OR.realized_body_base.
    apply CT.close_type_reduces, (@app_cong_r nat (reduces_to nat) _ _), OR.realized_spine_recovers.
Qed.

(** The arguments below are ORIGINAL open judgments, not assumptions that
    their closures already have the desired generated family types. *)
Theorem concrete_apply_typed a b d n rs (W : CT.telescope n rs) G q Ca Cb Ea Eb ell A B f u :
  CT.formed G W -> @typ nat RankSorts n G Ca (𝓤 0) -> @typ nat RankSorts n G Cb (𝓤 0) ->
  @typ nat RankSorts n G Ea (BP.arr Ca (𝓤 a)) ->
  @typ nat RankSorts n G Eb (BP.arr Cb (𝓤 b)) ->
  @typ nat RankSorts n G q (UC.family_type a b d rs Ca Cb Ea Eb ell) ->
  @typ nat RankSorts _ (CT.context W G) A (BF.lift rs Ca) ->
  @typ nat RankSorts _ (CT.context W G) B (TP.code_family (BF.lift rs Cb) (BF.lift rs Ea) A) ->
  @typ nat RankSorts _ (CT.context W G) f (TP.decoded_product (BF.lift rs Ea) (BF.lift rs Eb) A B) ->
  @typ nat RankSorts _ (CT.context W G) u (app (BF.lift rs Ea) A) ->
  @typ nat RankSorts n G
    (apply_family W q (CT.close_term W A) (CT.close_term W B) (CT.close_term W f) (CT.close_term W u))
    (BF.conclusion a b d (OR.realized_domains W) Ea Eb ell
      (CT.close_term W A) (CT.close_term W B) (CT.close_term W f) (CT.close_term W u)).
Proof.
  intros HW HCa HCb HEa HEb Hq HA HB Hf Hu.
  apply apply_family_typed with (Ca := Ca) (Cb := Cb); try assumption.
  - apply carrier_argument_typed; assumption.
  - eapply code_argument_typed with (a := a) (Ca := Ca); eassumption.
  - eapply function_argument_typed with (a := a) (b := b) (Ca := Ca) (Cb := Cb); eassumption.
  - eapply domain_argument_typed with (a := a) (Ca := Ca); eassumption.
Qed.

Lemma snoc_tail_normal n rs (E : CT.telescope n rs) : forall r todo
    (W : CT.telescope (S (CT.scope rs n)) todo),
  CT.normal_annotations (UR.rebase (eq_sym (UR.scope_snoc rs n r)) W) =
  CT.normal_annotations W.
Proof.
  induction E; intros r0 todo W; cbn [UR.scope_snoc UR.rebase]; [reflexivity | apply IHE].
Qed.

Theorem parameter_values_normal todo : forall n rs (E : CT.telescope n rs)
    (W : CT.telescope (CT.scope rs n) todo) m sigma,
  CT.normal_annotations E = true -> CT.normal_annotations W = true ->
  (forall i, normalb (sigma i) = true) ->
  forall i, normalb (UR.instantiate todo n rs E W m sigma i) = true.
Proof.
  induction todo as [|r todo IH]; intros n rs E W m sigma HE HW HS i.
  - exact (HS i).
  - dependent elimination W as [CT.tcons r A W0].
    cbn [CT.normal_annotations] in HW; apply andb_true_iff in HW; destruct HW as [HA HW].
    cbn [UR.instantiate UR.first_domain UR.remaining_domains].
    apply IH.
    + rewrite UT.snoc_normal, HE; exact HA.
    + rewrite (snoc_tail_normal n rs E r _ _); exact HW.
    + intro j; dependent elimination j as [fzero | fsucc j]; cbn [UR.parameter_step fin_match].
      * unfold UR.parameter_argument; rewrite CT.close_term_normal, HE; exact HA.
      * exact (HS j).
Qed.

Theorem realize_normal n rs (W : CT.telescope n rs) :
  CT.normal_annotations W = true -> forall i, normalb (UR.realize W i) = true.
Proof.
  intros HW i; apply parameter_values_normal; [reflexivity | exact HW | intro j; reflexivity].
Qed.

Theorem instantiate_normal n rs (W : CT.telescope n rs) q :
  CT.normal_annotations W = true -> normalb q = true -> isLambda q = false ->
  normalb (instantiate W q) = true.
Proof. intros HW HQ HL; apply TR.run_normal; [apply realize_normal; exact HW | exact HQ | exact HL]. Qed.

Theorem concrete_apply_normal n rs (W : CT.telescope n rs) q A B f u :
  CT.normal_annotations W = true -> normalb q = true -> isLambda q = false ->
  normalb A = true -> normalb B = true -> normalb f = true -> normalb u = true ->
  normalb (apply_family W q
    (CT.close_term W A) (CT.close_term W B) (CT.close_term W f) (CT.close_term W u)) = true.
Proof.
  intros HW HQ HL HA HB Hf Hu.
  assert (HN : normalb (instantiate W q) = true) by (apply instantiate_normal; assumption).
  assert (Hneutral : isLambda (instantiate W q) = false) by (apply TR.run_neutral; exact HL).
  unfold apply_family; cbn [normalb isLambda].
  rewrite HN, Hneutral, !CT.close_term_normal, HW, HA, HB, Hf, Hu; reflexivity.
Qed.

Definition field_apply l k rs a b d (W : CT.telescope (TS.width l k) rs) A B f u :=
  apply_family W (TS.contextual l k rs a b d)
    (CT.close_term W A) (CT.close_term W B) (CT.close_term W f) (CT.close_term W u).

Theorem field_apply_typed l k rs a b d (W : CT.telescope (TS.width l k) rs) A B f u :
  CT.bounded l k rs -> a <= k -> b <= k -> d <= k ->
  CT.formed (TS.context l k) W ->
  @typ nat RankSorts _ (CT.context W (TS.context l k)) A (BF.lift rs (TS.carrier l k a)) ->
  @typ nat RankSorts _ (CT.context W (TS.context l k)) B
    (TP.code_family (BF.lift rs (TS.carrier l k b)) (BF.lift rs (TS.decoder l k a)) A) ->
  @typ nat RankSorts _ (CT.context W (TS.context l k)) f
    (TP.decoded_product (BF.lift rs (TS.decoder l k a)) (BF.lift rs (TS.decoder l k b)) A B) ->
  @typ nat RankSorts _ (CT.context W (TS.context l k)) u (app (BF.lift rs (TS.decoder l k a)) A) ->
  @typ nat RankSorts _ (TS.context l k) (field_apply l k rs a b d W A B f u)
    (BF.conclusion a b d (OR.realized_domains W) (TS.decoder l k a) (TS.decoder l k b)
      (TS.law l k a b) (CT.close_term W A) (CT.close_term W B) (CT.close_term W f) (CT.close_term W u)).
Proof.
  intros Hr Ha Hb Hd HW HA HB Hf Hu; unfold field_apply.
  eapply concrete_apply_typed with (Ca := TS.carrier l k a) (Cb := TS.carrier l k b);
    try eassumption.
  - apply TS.carrier_typed; lia.
  - apply TS.carrier_typed; lia.
  - apply TS.decoder_typed; lia.
  - apply TS.decoder_typed; lia.
  - apply TS.contextual_typed; assumption.
Qed.

Theorem field_apply_normal l k rs a b d (W : CT.telescope (TS.width l k) rs) A B f u :
  CT.normal_annotations W = true ->
  normalb A = true -> normalb B = true -> normalb f = true -> normalb u = true ->
  normalb (field_apply l k rs a b d W A B f u) = true.
Proof. intros; apply concrete_apply_normal; try assumption; reflexivity. Qed.

Lemma apply_family_replace_head m n rs (W : CT.telescope m rs)
    (sigma : Fin m -> Term nat n) q q' A B f u :
  replace sigma q = replace sigma q' ->
  replace sigma (apply_family W q A B f u) = replace sigma (apply_family W q' A B f u).
Proof.
  intro H; unfold apply_family, instantiate; cbn [replace]; rewrite !TR.run_replace, H; reflexivity.
Qed.

(** The finite field is the ACTUAL lookup, not a separately postulated law.
    The output retains every filled concrete declaration and body literally. *)
Theorem field_apply_recovers l k n rs a b d (W : CT.telescope (TS.width l k) rs) A B f u :
  CT.bounded l k rs -> a <= k -> b <= k -> d <= k ->
  CT.formed (TS.context l k) W ->
  reduces_to nat n (replace (@TS.fill l k n) (field_apply l k rs a b d W A B f u))
    (IE.refl_case d (replace (TS.fill l k) (CT.close_type W (app B u)))
      (replace (TS.fill l k) (CT.close_term W (app f u)))).
Proof.
  intros Hr Ha Hb Hd HW; unfold field_apply.
  erewrite apply_family_replace_head with (q' := UC.identity_family a b d rs).
  - rewrite <- IE.refl_case_replace.
    apply replace_rtc; apply concrete_identity_recovers with (G := TS.context l k); exact HW.
  - rewrite UC.identity_family_replace; apply TS.fill_contextual; assumption.
Qed.

Lemma close_term_injective n rs (W : CT.telescope n rs) : forall t u,
  CT.close_term W t = CT.close_term W u -> t = u.
Proof. induction W; intros t u H; cbn [CT.close_term] in H; [exact H | apply IHW; congruence]. Qed.

Theorem concrete_apply_inputs_injective n rs (W : CT.telescope n rs) q A B f u A' B' f' u' :
  apply_family W q (CT.close_term W A) (CT.close_term W B) (CT.close_term W f) (CT.close_term W u) =
  apply_family W q (CT.close_term W A') (CT.close_term W B') (CT.close_term W f') (CT.close_term W u') ->
  A = A' /\ B = B' /\ f = f' /\ u = u'.
Proof.
  intro H; unfold apply_family in H; inversion H; repeat split; apply close_term_injective with (W := W); congruence.
Qed.

Theorem concrete_apply_conversion_injective n rs (W : CT.telescope n rs) q A B f u A' B' f' u' :
  CT.normal_annotations W = true -> normalb q = true -> isLambda q = false ->
  normalb A = true -> normalb B = true -> normalb f = true -> normalb u = true ->
  normalb A' = true -> normalb B' = true -> normalb f' = true -> normalb u' = true ->
  def_equiv nat n
    (apply_family W q (CT.close_term W A) (CT.close_term W B) (CT.close_term W f) (CT.close_term W u))
    (apply_family W q (CT.close_term W A') (CT.close_term W B') (CT.close_term W f') (CT.close_term W u')) ->
  A = A' /\ B = B' /\ f = f' /\ u = u'.
Proof.
  intros HW HQ HL HA HB Hf Hu HA' HB' Hf' Hu' Heq.
  apply concrete_apply_inputs_injective with (W := W) (q := q).
  apply normal_conversion_identity; [apply concrete_apply_normal; assumption |
    apply concrete_apply_normal; assumption | exact Heq].
Qed.

Print Assumptions instantiate_typed.
Print Assumptions instantiate_identity_recovers.
Print Assumptions instantiated_identity_typed.
Print Assumptions apply_family_typed.
Print Assumptions apply_identity_recovers.
Print Assumptions concrete_identity_recovers.
Print Assumptions carrier_argument_typed.
Print Assumptions code_argument_typed.
Print Assumptions function_argument_typed.
Print Assumptions domain_argument_typed.
Print Assumptions concrete_apply_typed.
Print Assumptions parameter_values_normal.
Print Assumptions realize_normal.
Print Assumptions instantiate_normal.
Print Assumptions concrete_apply_normal.
Print Assumptions field_apply_typed.
Print Assumptions field_apply_normal.
Print Assumptions field_apply_recovers.
Print Assumptions concrete_apply_inputs_injective.
Print Assumptions concrete_apply_conversion_injective.
End ConcreteContextualBeta.
