(** Normalization of unrestricted ORIGINAL denotation, retaining its actual
    semantic value. The environment evidence is later derived from original
    validity, rather than added to the final soundness theorem. *)
From Equations Require Import Equations.
From ZFC Require Import Sets Axioms.
From PTSrk Require Import Syntax Context Typing Ranks Reduction DefEq
  Preservation Inversions AbstractRewriting Congruence.
From PTSrkModel Require Import SetFunctions CodeUniverses CountableCodes
  CardinalHierarchy HierarchyBounds SuppliedHierarchy CardinalClassification
  CountableDichotomy GlobalOperations Denotation InterpretedContexts
  DenotationInversion ContextTransport CanonicalTypeWitnesses CanonicalDenotation
  RankedDenotation RankedTransport RankedSubstitution RankedHereditary.
Import CodeUniverses.CodeUniverses.

Module RankedNormalization.
Module OD := Denotation.
Module RD := RankedDenotation.RankedDenotation.
Module RS := RankedSubstitution.RankedSubstitution.
Module RT := RankedTransport.RankedTransport.
Module RH := RankedHereditary.RankedHereditary.
Module CD := CanonicalDenotation.CanonicalDenotation.

Lemma normal_target_reduction {n} (t N : Term nat n) :
  t =ᵝ N -> beta_normal N -> t ↠ᵝ N.
Proof.
  intros E NN; apply def_equiv_prop in E as [K [RK RN]].
  pose proof (normal_reductions_equal N K NN RN) as EK; subst K; exact RK.
Qed.

Section Normalization.
Variables W H s : Ens.
Hypothesis HW : transitive_set W.
Hypothesis HO : INC omega_codes W.
Hypothesis HH : tower_envelope W H.
Variable classical_logic : forall P : Prop, P \/ ~ P.
Hypothesis comparison : cardinal_comparability.
Hypothesis gap : infinite_powerset_gap.
Hypothesis choice : family_choice.
Hypothesis selector : selects_global_witnesses H s.

Definition certifies {n} (G : Ctx nat n) rho t T v :=
  exists a, RH.normalizes H s G rho t T v a.

Definition normalization_result {n} (G : Ctx nat n) rho t v :=
  forall T, @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
    RS.certified_variables H s G rho -> certifies G rho t T v.

Lemma certifies_sort {n} (G : Ctx nat n) rho t k v :
  certifies G rho t (𝓤 k) v ->
  RH.normalizes H s G rho t (𝓤 k) v (repr (sort k)).
Proof.
  intros [a DN].
  destruct (RH.normalizes_sort H s G rho t k v a DN) as [N [RN DC]].
  exists N, (𝓤 k); split; [exact RN |]. split; [reflexivity |].
  eapply RD.certificate_equal; [exact DC |apply EQ_refl |].
  apply (CD.sort_value H s n G rho k a).
  exact (proj2 (RD.canonical_denotations H s _ _ _ _ _ _ _ DC)).
Qed.

Lemma certifies_from_normal {n} (G : Ctx nat n) rho t T N C v a :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T -> t ↠ᵝ N ->
  RD.certificate H s n G rho N C v a -> certifies G rho t T v.
Proof.
  intros HG HT RN DC; exists a, N, C; split; [exact RN |]. split; [|exact DC].
  apply normal_target_reduction; [|exact (proj2 (RD.normality H s _ _ _ _ _ _ _ DC))].
  eapply uniqueness_of_typing; [eapply subject_reduction'; eassumption |
    eapply RD.original_typing; exact DC].
Qed.

Lemma certificate_at_type {n} (G : Ctx nat n) rho t T v C c :
  certifies G rho t T v -> @wf nat RankSorts n G ->
  @typ nat RankSorts n G t C -> beta_normal C -> CD.denotes H s n G rho C c ->
  exists N, t ↠ᵝ N /\ RD.certificate H s n G rho N C v c.
Proof.
  intros [a [N [C0 [RN [RC DC]]]]] HG TC NC Dc.
  exists N; split; [exact RN |].
  eapply RT.certificate_type_alignment; [exact DC | |exact NC |exact Dc].
  eapply subject_reduction'; eassumption.
Qed.

Lemma certifies_context_transport {n} (G D : Ctx nat n) rho t T v :
  context_typing_morphism G D -> certifies G rho t T v -> certifies D rho t T v.
Proof.
  intros HM [a [N [C [RN [RC DC]]]]]; exists a, N, C.
  split; [exact RN |]. split; [exact RC |].
  eapply RT.certificate_context_transport; eassumption.
Qed.

Lemma normalized_binder_morphisms {n} (G : Ctx nat n) A A' k :
  @wf nat RankSorts n G -> @typ nat RankSorts n G A (𝓤 k) -> A ↠ᵝ A' ->
  context_typing_morphism (G & A) (G & A') /\
  context_typing_morphism (G & A') (G & A).
Proof.
  intros HG TA RA; split; apply context_conversion_morphism.
  - constructor; [apply contexts_convertible_refl |apply RH.reduction_equiv; exact RA].
  - eapply wf_cons; eassumption.
  - constructor; [apply contexts_convertible_refl |symmetry; apply RH.reduction_equiv; exact RA].
  - eapply wf_cons; [exact HG |eapply subject_reduction'; eassumption].
Qed.

Lemma certified_variables_normalized_extension {n} (G : Ctx nat n) rho A A' k a x :
  @wf nat RankSorts n G -> @typ nat RankSorts n G A (𝓤 k) -> A ↠ᵝ A' ->
  RS.certified_variables H s G rho ->
  RD.certificate H s n G rho A' (𝓤 k) a (repr (sort k)) -> IN x (decode a) ->
  RS.certified_variables H s (G & A) (fin_match x rho).
Proof.
  intros HG TA RA HV DA Hx.
  destruct (normalized_binder_morphisms G A A' k HG TA RA) as [_ HM].
  pose proof (RS.certified_variables_extend H s _ G rho A' k a x HV DA Hx) as HV'.
  intro i; destruct (HV' i) as [T [c DC]]; exists T, c.
  eapply RT.certificate_context_transport; eassumption.
Qed.

Lemma normalize_binder {n} (G : Ctx nat n) rho A B m k a b :
  @wf nat RankSorts n G -> RS.certified_variables H s G rho ->
  @typ nat RankSorts n G A (𝓤 m) -> @typ nat RankSorts (S n) (G & A) B (𝓤 k) ->
  certifies G rho A (𝓤 m) a ->
  (forall x, IN x (decode a) -> normalization_result (G & A) (fin_match x rho) B (b x)) ->
  exists A' B', A ↠ᵝ A' /\ B ↠ᵝ B' /\
    @typ nat RankSorts (S n) (G & A') B' (𝓤 k) /\ beta_normal B' /\
    RD.certificate H s n G rho A' (𝓤 m) a (repr (sort m)) /\
    forall x, IN x (decode a) ->
      RD.certificate H s (S n) (G & A') (fin_match x rho) B' (𝓤 k) (b x) (repr (sort k)).
Proof.
  intros HG HV TA TB IA IB.
  destruct (RH.normalizes_sort H s G rho A m a (repr (sort m)) (certifies_sort G rho A m a IA))
    as [A' [RA DA]].
  destruct (normalized_binder_morphisms G A A' m HG TA RA) as [HM _].
  assert (HG' : @wf nat RankSorts (S n) (G & A')) by
    (eapply wf_cons; [exact HG |eapply RD.original_typing; exact DA]).
  assert (TBraw : @typ nat RankSorts (S n) (G & A') B (𝓤 k)) by
    (eapply typing_context_transport; eassumption).
  assert (PB : forall x, IN x (decode a) ->
    RH.normalizes H s (G & A') (fin_match x rho) B (𝓤 k) (b x) (repr (sort k))).
  { intros x Hx.
    assert (HX : RS.certified_variables H s (G & A) (fin_match x rho)).
    { eapply certified_variables_normalized_extension; eassumption. }
    assert (HGA : @wf nat RankSorts (S n) (G & A)) by (eapply wf_cons; eassumption).
    destruct (certifies_sort (G & A) (fin_match x rho) B k (b x) (IB x Hx (𝓤 k) HGA TB HX))
      as [N [C [RN [RC DC]]]].
    exists N, C; split; [exact RN |]. split; [exact RC |].
    eapply RT.certificate_context_transport; eassumption. }
  destruct (RH.uniform_normalization H s (G & A') B (𝓤 k) (𝓤 k) (decode a)
    (fun x => fin_match x rho) b (fun _ => repr (sort k)) HG' TBraw (RH.normal_sort k) PB)
    as [B' [RB [NB [TB' DB']]]].
  exists A', B'; split; [exact RA |]. split; [exact RB |]. split; [exact TB' |].
  split; [exact NB |]. split; [exact DA |exact DB'].
Qed.
Theorem original_denotation_normalizes n G rho t v :
  OD.denotes H s n G rho t v -> normalization_result G rho t v.
Proof.
  intro DD; induction DD as
    [n G rho i | n G rho i |
     n G rho A B a b DA IHDA DB IHDB EB |
     n G rho A B t a b body Tt DA IHDA DB IHDB Dt IHDt EB Et |
     n G rho A B t u a b f x Tf DA IHDA DB IHDB EB Df IHDf Du IHDu |
     n G rho t v v' DD IHDD EV]; intros T HG HT HV.
  - eapply certifies_from_normal; [exact HG |exact HT |reflexivity |apply RD.certificate_sort].
  - destruct (HV i) as [C [c DC]].
    eapply certifies_from_normal; [exact HG |exact HT |reflexivity |exact DC].
  - destruct (Π_inversion RankSorts A T B HT) as [m [k [l [R [TA [TB ET]]]]]].
    destruct (normalize_binder G rho A B m k a b HG HV TA TB
      (IHDA (𝓤 m) HG TA HV) IHDB) as [A' [B' [RA [RB [TB' [NB' [DA' DB']]]]]]].
    eapply certifies_from_normal with (N := Π A' B'); [exact HG |exact HT | |].
    + cong_par; try assumption; typeclasses eauto.
    + eapply RD.certificate_product; eassumption.
  - destruct (λ_inversion RankSorts A T t HT) as [m [B0 [TA [Tt0 ET]]]].
    assert (HGA : @wf nat RankSorts (S n) (G & A)) by (eapply wf_cons; eassumption).
    destruct (type_is_correct t B Tt HGA) as [k TB].
    destruct (normalize_binder G rho A B m k a b HG HV TA TB
      (IHDA (𝓤 m) HG TA HV) IHDB) as [A' [B' [RA [RB [TB' [NB' [DA' DB']]]]]]].
    destruct (normalized_binder_morphisms G A A' m HG TA RA) as [HM _].
    assert (HGA' : @wf nat RankSorts (S n) (G & A')) by
      (eapply wf_cons; [exact HG |eapply RD.original_typing; exact DA']).
    assert (Tt' : @typ nat RankSorts (S n) (G & A') t B').
    { eapply typ_conv; [eapply typing_context_transport; [exact HM |exact Tt] |
        exact TB' |apply RH.reduction_equiv; exact RB]. }
    destruct (typed_normal_form (G & A') t B' HGA' Tt') as [t' [Rt [Nt' Tt'']]].
    assert (Dt' : forall x, IN x (decode a) ->
      RD.certificate H s (S n) (G & A') (fin_match x rho) t' B' (body x) (b x)).
    { intros x Hx.
      assert (HX : RS.certified_variables H s (G & A) (fin_match x rho)).
      { eapply certified_variables_normalized_extension; eassumption. }
      assert (HC : certifies (G & A') (fin_match x rho) t B (body x)).
      { eapply certifies_context_transport; [exact HM |apply IHDt; eassumption]. }
      destruct (certificate_at_type (G & A') (fin_match x rho) t B (body x) B' (b x)
        HC HGA' Tt' NB' (proj1 (RD.canonical_denotations H s _ _ _ _ _ _ _ (DB' x Hx))))
        as [N [RN DN]].
      assert (E : N = t').
      { eapply RH.normal_outputs_unique; [exact RN |exact Rt |
          exact (proj1 (RD.normality H s _ _ _ _ _ _ _ DN)) |exact Nt']. }
      subst N; exact DN. }
    eapply certifies_from_normal with (N := lam A' t'); [exact HG |exact HT | |].
    + cong_par; try assumption; typeclasses eauto.
    + eapply RD.certificate_lambda with (m := m) (k := k); eassumption.
  - destruct (type_is_correct t (Π A B) Tf HG) as [q TP].
    destruct (Π_inversion RankSorts A (𝓤 q) B TP) as [m [k [l [R [TA [TB EP]]]]]].
    destruct (app_inversion RankSorts t u T HT) as [A0 [B0 [Tf0 [Tu0 ET]]]].
    assert (EA : A0 =ᵝ A).
    { apply (proj1 (equiv_Π_inversion A0 A B0 B (uniqueness_of_typing G t _ _ Tf0 Tf))). }
    assert (Tu : @typ nat RankSorts n G u A) by (eapply typ_conv; eassumption).
    destruct (normalize_binder G rho A B m k a b HG HV TA TB
      (IHDA (𝓤 m) HG TA HV) IHDB) as [A' [B' [RA [RB [TB' [NB' [DA' DB']]]]]]].
    assert (NA' : beta_normal A') by (exact (proj1 (RD.normality H s _ _ _ _ _ _ _ DA'))).
    assert (NP : beta_normal (Π A' B')) by (apply beta_normal_product; auto).
    assert (TP' : @typ nat RankSorts n G (Π A' B') (𝓤 (Nat.max (S m) k))).
    { eapply typ_Π; [eapply RD.original_typing; exact DA' |exact TB' |reflexivity]. }
    assert (Tf' : @typ nat RankSorts n G t (Π A' B')).
    { eapply typ_conv; [exact Tf |exact TP' |]. apply RH.reduction_equiv.
      cong_par; try assumption; typeclasses eauto. }
    assert (Tu' : @typ nat RankSorts n G u A').
    { eapply typ_conv; [exact Tu |eapply RD.original_typing; exact DA' |apply RH.reduction_equiv; exact RA]. }
    assert (DP : CD.denotes H s n G rho (Π A' B') (semantic_product H s a b)).
    { eapply CD.denotes_product.
      - exact (proj1 (RD.canonical_denotations H s _ _ _ _ _ _ _ DA')).
      - intros y Hy; exact (proj1 (RD.canonical_denotations H s _ _ _ _ _ _ _ (DB' y Hy))).
      - exact EB. }
    destruct (certificate_at_type G rho t (Π A B) f (Π A' B') (semantic_product H s a b)
      (IHDf (Π A B) HG Tf HV) HG Tf' NP DP) as [f' [Rf Df']].
    destruct (certificate_at_type G rho u A x A' a (IHDu A HG Tu HV) HG Tu' NA'
      (proj1 (RD.canonical_denotations H s _ _ _ _ _ _ _ DA'))) as [u' [Ru Du']].
    destruct (RH.certified_application W H s HW HO HH classical_logic comparison gap choice selector
      n G rho A' B' f' u' m k a b f x HG HV TB' NB' DA' DB' Df' Du' EB)
      as [N [C [RN [RC DN]]]].
    eapply certifies_from_normal; [exact HG |exact HT | |exact DN].
    transitivity (app f' u'); [cong_par; try assumption; typeclasses eauto |exact RN].
  - destruct (IHDD T HG HT HV) as [a [N [C [RN [RC DN]]]]].
    exists a, N, C; split; [exact RN |]. split; [exact RC |].
    eapply RD.certificate_equal; [exact DN |exact EV |apply EQ_refl].
Qed.
Theorem original_valid_variable_certificates n (G : Ctx nat n) :
  @wf nat RankSorts n G -> forall rho,
  valid_valuation H s G rho -> RS.certified_variables H s G rho.
Proof.
  intro HG; induction HG as [|n G A k HG IH TA]; intros rho HV.
  - intro i; dependent elimination i.
  - destruct HV as [HV [a [DA Hx]]].
    pose proof (IH (fun i => rho (fsucc i)) HV) as HC.
    pose proof (original_denotation_normalizes n G (fun i => rho (fsucc i)) A a DA
      (𝓤 k) HG TA HC) as HA.
    destruct (RH.normalizes_sort H s G (fun i => rho (fsucc i)) A k a (repr (sort k))
      (certifies_sort G (fun i => rho (fsucc i)) A k a HA)) as [A' [RA DA']].
    pose proof (certified_variables_normalized_extension G (fun i => rho (fsucc i))
      A A' k a (rho fzero) HG TA RA HC DA' Hx) as HX.
    intro i; destruct (HX i) as [T [c DC]]; exists T, c.
    assert (Ei : fin_match (rho fzero) (fun j => rho (fsucc j)) i = rho i)
      by (dependent elimination i; reflexivity).
    rewrite Ei in DC.
    eapply RD.valuation_extensional; [exact DC |].
    intro j; dependent elimination j; cbn [fin_match]; apply EQ_refl.
Qed.

Theorem original_typed_normalization n (G : Ctx nat n) rho t T v :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
  valid_valuation H s G rho -> OD.denotes H s n G rho t v -> certifies G rho t T v.
Proof.
  intros HG HT HV DD; apply (original_denotation_normalizes n G rho t v DD T HG HT).
  apply original_valid_variable_certificates; assumption.
Qed.

(** Equality of the actual values, not merely their decoded memberships. *)
Theorem original_typed_conversion_values n (G : Ctx nat n) rho t T u U v w :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T -> @typ nat RankSorts n G u U ->
  valid_valuation H s G rho -> t =ᵝ u ->
  OD.denotes H s n G rho t v -> OD.denotes H s n G rho u w -> EQ v w.
Proof.
  intros HG HT HU HV ET DT DU.
  destruct (original_typed_normalization n G rho t T v HG HT HV DT)
    as [a [N [C [RN [RC DN]]]]].
  destruct (original_typed_normalization n G rho u U w HG HU HV DU)
    as [b [M [D [RM [RD0 DM]]]]].
  assert (E : N = M).
  { apply normal_convertible_equal.
    - exact (proj1 (RD.normality H s _ _ _ _ _ _ _ DN)).
    - exact (proj1 (RD.normality H s _ _ _ _ _ _ _ DM)).
    - transitivity t; [symmetry; apply RH.reduction_equiv; exact RN |].
      transitivity u; [exact ET |apply RH.reduction_equiv; exact RM]. }
  subst M; eapply CD.coherent.
  - exact (proj1 (RD.canonical_denotations H s _ _ _ _ _ _ _ DN)).
  - exact (proj1 (RD.canonical_denotations H s _ _ _ _ _ _ _ DM)).
Qed.

Theorem original_typed_decoded_conversion n (G : Ctx nat n) rho A B m k :
  @wf nat RankSorts n G -> valid_valuation H s G rho ->
  @typ nat RankSorts n G A (𝓤 m) -> @typ nat RankSorts n G B (𝓤 k) -> A =ᵝ B ->
  forall a b, OD.denotes H s n G rho A a -> OD.denotes H s n G rho B b ->
    EQ (decode a) (decode b).
Proof.
  intros HG HV TA TB E a b DA DB; apply decoding_extensional.
  exact (original_typed_conversion_values n G rho A (𝓤 m) B (𝓤 k) a b HG TA TB HV E DA DB).
Qed.
End Normalization.
End RankedNormalization.

Print Assumptions RankedNormalization.original_denotation_normalizes.
Check RankedNormalization.original_denotation_normalizes.
Print Assumptions RankedNormalization.original_valid_variable_certificates.
Print Assumptions RankedNormalization.original_typed_normalization.
Print Assumptions RankedNormalization.original_typed_conversion_values.
Print Assumptions RankedNormalization.original_typed_decoded_conversion.
Check RankedNormalization.original_typed_decoded_conversion.
