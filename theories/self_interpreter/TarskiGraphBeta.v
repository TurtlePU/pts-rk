From Stdlib Require Import Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  DefEq Reduction AbstractRewriting Congruence.
From PTSrk.NormalizationComplexity Require Import Morphisms Greedy.
From PTSrk.SelfInterpreter Require Import BrownPalsberg DependentPHOAS IndexedEquality
  IndexedCoherence TarskiProducts TarskiCasts TarskiBeta TarskiBetaSignature DependentEquality.
Import Context.

(** The ACTUAL finite beta-law fields yield synchronized dependent graph
    equality. This local construction adds no coherence assumption. Its
    explicit lambda-valued decoded family introduces administrative redexes;
    no normality, eta conversion or whole-source quotation is asserted. *)
Module TarskiGraphBeta.
Module BP := BrownPalsberg.BrownPalsberg.
Module DP := DependentPHOAS.DependentPHOAS.
Module IE := IndexedEquality.IndexedEquality.
Module IC := IndexedCoherence.IndexedCoherence.
Module TP := TarskiProducts.TarskiProducts.
Module TC := TarskiCasts.TarskiCasts.
Module TB := TarskiBeta.TarskiBeta.
Module BS := TarskiBetaSignature.TarskiBetaSignature.
Module DE := DependentEquality.DependentEquality.

Definition decoded_family {n} (Ea Eb A B : Term nat n) :=
  lam (app Ea A) (app (shift Eb) (app (shift B) (var fzero))).

Theorem decoded_family_typed a b n (G : Ctx nat n) Ca Cb Ea Eb A B :
  @typ nat RankSorts n G Ea (BP.arr Ca (𝓤 a)) ->
  @typ nat RankSorts n G Eb (BP.arr Cb (𝓤 b)) ->
  @typ nat RankSorts n G A Ca ->
  @typ nat RankSorts n G B (TP.code_family Cb Ea A) ->
  @typ nat RankSorts n G (decoded_family Ea Eb A B) (BP.arr (app Ea A) (𝓤 b)).
Proof.
  intros HEa HEb HA HB; unfold decoded_family, BP.arr at 1.
  apply typ_λ with (ℓ := a); [eapply BP.arr_apply; eassumption |].
  eapply BP.arr_apply with (A := shift Cb).
  - change (typ (G & app Ea A) (shift Eb) (BP.arr (shift Cb) (shift (𝓤 b)))).
    rewrite <- BP.arr_shift; apply weakening; exact HEb.
  - eapply BP.arr_apply with (A := shift (app Ea A)).
    + change (typ (G & app Ea A) (shift B) (BP.arr (shift (app Ea A)) (shift Cb))).
      rewrite <- BP.arr_shift; apply weakening; exact HB.
    + change (typ (G & app Ea A) (var fzero) ((G & app Ea A) !! fzero)); constructor.
Qed.

Theorem decoded_family_beta n (Ea Eb A B u : Term nat n) :
  step nat n (app (decoded_family Ea Eb A B) u) (app Eb (app B u)).
Proof.
  unfold decoded_family.
  replace (app Eb (app B u)) with
    (subst (app (shift Eb) (app (shift B) (var fzero))) u) by syntax_simp.
  apply step_beta.
Qed.

Theorem decoded_family_replace m n (sigma : Fin m -> Term nat n) Ea Eb A B :
  replace sigma (decoded_family Ea Eb A B) =
    decoded_family (replace sigma Ea) (replace sigma Eb) (replace sigma A) (replace sigma B).
Proof. unfold decoded_family; cbn [replace]; rewrite !replace_lift_shift; reflexivity. Qed.

(** Retype the predicate application, rather than extracting endpoint typing
    from an equality witness. Only an actual forward fiber reduction is used. *)
Theorem fiber_congruence_convertible a b d n (G : Ctx nat n) A F C u y z e :
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G F (BP.arr A (𝓤 b)) ->
  @typ nat RankSorts n G C (𝓤 b) ->
  @typ nat RankSorts n G u A ->
  reduces_to nat n (app F u) C ->
  @typ nat RankSorts n G e (IE.eq_type d C y z) ->
  @typ nat RankSorts n G (DE.fiber_congruence d A F u e)
    (DE.graph_eq d A F u y u z).
Proof.
  intros HA HF HC Hu Hred He; set (GP := G & DE.predicate_type d A F).
  assert (HE : typ GP (shift e) (IE.eq_type d (shift C) (shift y) (shift z))).
  { rewrite <- IC.eq_type_shift; apply weakening; exact He. }
  assert (HM : typ GP (app (var fzero) (shift u)) (IE.motive_type d (shift C))).
  { eapply typ_conv with (T := IE.motive_type d (shift (app F u))) (ℓ := S b).
    - change (typ GP (app (var fzero) (shift u))
        (IE.motive_type d (app (shift F) (shift u)))).
      eapply DE.predicate_specialize_typed with (A := shift A).
      + rewrite <- DE.predicate_type_shift; change (typ GP (var fzero) (GP !! fzero)); constructor.
      + apply weakening; exact Hu.
    - apply IE.motive_type_sort; change (typ GP (shift C) (shift (𝓤 b))).
      apply weakening; exact HC.
    - apply def_equiv_prop; exists (IE.motive_type d (shift C)); split; [| reflexivity].
      unfold IE.motive_type; apply BP.arr_reduces; [apply rename_rtc; exact Hred | reflexivity]. }
  unfold DE.fiber_congruence, DE.graph_eq.
  apply typ_λ with (ℓ := Nat.max (S a) (S b)); [eapply DE.predicate_type_sort; eassumption |].
  change (typ GP (app (shift e) (app (var fzero) (shift u)))
    (BP.arr (DE.observe (var fzero) (shift u) (shift y))
      (DE.observe (var fzero) (shift u) (shift z)))).
  eapply IE.eq_specialize; eassumption.
Qed.

Definition beta_graph k a b d (A B f u : Term nat (BS.width k)) :=
  DE.fiber_congruence d (app (BS.decoder k a) A)
    (decoded_family (BS.decoder k a) (BS.decoder k b) A B) u
    (BS.apply_beta k a b d A B f u).

Definition beta_graph_type k a b d (A B f u : Term nat (BS.width k)) :=
  DE.graph_eq d (app (BS.decoder k a) A)
    (decoded_family (BS.decoder k a) (BS.decoder k b) A B)
    u (TC.cast_app a b (BS.decoder k a) (BS.decoder k b) A B
      (app (app (BS.law k a b) A) B)
      (TC.cast_abs a b (BS.decoder k a) (BS.decoder k b) A B
        (app (app (BS.law k a b) A) B) f) u)
    u (app f u).

Theorem beta_graph_typed k a b d A B f u : a <= k -> b <= k -> d <= k ->
  @typ nat RankSorts _ (BS.context k) A (BS.carrier k a) ->
  @typ nat RankSorts _ (BS.context k) B
    (TP.code_family (BS.carrier k b) (BS.decoder k a) A) ->
  @typ nat RankSorts _ (BS.context k) f
    (TP.decoded_product (BS.decoder k a) (BS.decoder k b) A B) ->
  @typ nat RankSorts _ (BS.context k) u (app (BS.decoder k a) A) ->
  @typ nat RankSorts _ (BS.context k) (beta_graph k a b d A B f u)
    (beta_graph_type k a b d A B f u).
Proof.
  intros Ha Hb Hd HA HB Hf Hu; unfold beta_graph, beta_graph_type.
  eapply fiber_congruence_convertible with (a := a) (b := b)
    (C := app (BS.decoder k b) (app B u)).
  - eapply BP.arr_apply; [apply BS.decoder_typed; lia | exact HA].
  - eapply decoded_family_typed; [apply BS.decoder_typed; lia |
      apply BS.decoder_typed; lia | exact HA | exact HB].
  - eapply BP.arr_apply; [apply BS.decoder_typed; lia |].
    eapply BP.arr_apply; [exact HB | exact Hu].
  - exact Hu.
  - apply rtc_in, decoded_family_beta.
  - exact (BS.apply_beta_typed k a b d A B f u Ha Hb Hd HA HB Hf Hu).
Qed.

Lemma fiber_evidence_reduces d n (A F u e e' : Term nat n) :
  reduces_to nat n e e' ->
  reduces_to nat n (DE.fiber_congruence d A F u e) (DE.fiber_congruence d A F u e').
Proof.
  intro H; unfold DE.fiber_congruence; apply (@λ_cong_r nat (reduces_to nat) _ n).
  apply (@app_cong_l nat (reduces_to nat) _ (S n)), rename_rtc; exact H.
Qed.

(** The filled family and domain stay LITERALLY substituted in this result.
    In particular the lambda family is not eta-contracted to its body map. *)
Theorem beta_graph_recovers k a b d n (A B f u : Term nat (BS.width k)) :
  a <= k -> b <= k -> d <= k ->
  reduces_to nat n (replace (@BS.fill k n) (beta_graph k a b d A B f u))
    (DE.graph_refl d
      (replace (BS.fill k) (app (BS.decoder k a) A))
      (replace (BS.fill k) (decoded_family (BS.decoder k a) (BS.decoder k b) A B))
      (replace (BS.fill k) u) (app (replace (BS.fill k) f) (replace (BS.fill k) u))).
Proof.
  intros Ha Hb Hd; unfold beta_graph; rewrite DE.fiber_congruence_replace.
  eapply rtc_trans; [apply fiber_evidence_reduces, BS.apply_beta_recovers; assumption |].
  apply DE.fiber_congruence_reflexivity.
Qed.

Theorem filled_beta_graph_typed k a b d n (G : Ctx nat n) A B f u :
  a <= k -> b <= k -> d <= k ->
  @typ nat RankSorts _ (BS.context k) A (BS.carrier k a) ->
  @typ nat RankSorts _ (BS.context k) B
    (TP.code_family (BS.carrier k b) (BS.decoder k a) A) ->
  @typ nat RankSorts _ (BS.context k) f
    (TP.decoded_product (BS.decoder k a) (BS.decoder k b) A B) ->
  @typ nat RankSorts _ (BS.context k) u (app (BS.decoder k a) A) ->
  @typ nat RankSorts n G (replace (BS.fill k) (beta_graph k a b d A B f u))
    (replace (BS.fill k) (beta_graph_type k a b d A B f u)).
Proof.
  intros; eapply typing_replace; [apply beta_graph_typed; eassumption | apply BS.fill_typed].
Qed.

Print Assumptions decoded_family_typed.
Print Assumptions decoded_family_beta.
Print Assumptions decoded_family_replace.
Print Assumptions fiber_congruence_convertible.
Print Assumptions beta_graph_typed.
Print Assumptions beta_graph_recovers.
Print Assumptions filled_beta_graph_typed.
End TarskiGraphBeta.
