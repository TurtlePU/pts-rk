(** Full original-typing realization REDUCED TO typed decoded conversion.
    The conversion premise is unproved, explicit, and not a model axiom.
    This conditional theorem must not be called unconditional soundness. *)
From ZFC Require Import Sets Axioms.
From PTSrk Require Import Syntax Context Typing Ranks DefEq Preservation AbstractRewriting Inversions.
From PTSrkModel Require Import SetFunctions CodeUniverses CountableCodes
  CardinalHierarchy HierarchyBounds SuppliedHierarchy CardinalClassification
  CountableDichotomy GlobalOperations Denotation InterpretedContexts
  DenotationChoice LambdaRealization ApplicationRealization RegularTyping
  DenotationInversion ContextTransport.
Import CodeUniverses.CodeUniverses.

Section Realization.
Variables W H s : Ens.
Hypothesis HW : transitive_set W.
Hypothesis HO : INC omega_codes W.
Hypothesis HH : tower_envelope W H.
Variable classical_logic : forall P : Prop, P \/ ~ P.
Hypothesis comparison : cardinal_comparability.
Hypothesis gap : infinite_powerset_gap.
Hypothesis choice : family_choice.
Hypothesis HS : selects_global_witnesses H s.

(** Open obligation. It asserts equality of decoded types, not existence
    of term inhabitants. No constant implementing it is declared. *)
Variable conversion : forall n (G : Ctx nat n) rho A B m k,
  @wf nat RankSorts n G -> valid_valuation H s G rho ->
  @typ nat RankSorts n G A (𝓤 m) -> @typ nat RankSorts n G B (𝓤 k) -> A =ᵝ B ->
  forall a b, denotes H s n G rho A a -> denotes H s n G rho B b ->
    EQ (decode a) (decode b).

Theorem regular_realization_from_conversion n (G : Ctx nat n) t T :
  regular_typ G t T -> @wf nat RankSorts n G ->
  forall rho, valid_valuation H s G rho -> realizes H s G rho t T.
Proof.
  intro HT; induction HT; intros HG rho HV.
  - change (j = 0) in H0; subst j. apply sort_realization.
  - change (l = Nat.max (S m) k) in H0; subst l.
    eapply (product_realization_in_context W H s HW HO HH classical_logic comparison gap choice HS).
    + intros rho' HV'; apply IHHT1; assumption.
    + intros rho' HV'; apply IHHT2; [eapply wf_cons; [exact HG | apply regular_typ_original; exact HT1] | exact HV'].
    + exact HV.
  - apply variable_realization; exact HV.
  - assert (HGA : @wf nat RankSorts _ (G & A)) by
      (eapply wf_cons; [exact HG | apply regular_typ_original; exact HT1]).
    eapply (lambda_realization_from_induction W H s HW HO HH classical_logic comparison gap choice HS).
    + apply regular_typ_original; exact HT3.
    + intros rho' HV'; apply IHHT1; assumption.
    + intros rho' HV'; apply IHHT3; assumption.
    + intros rho' HV'; apply IHHT2; assumption.
    + intros rho' HV' c c' DC DC'.
      eapply conversion; [exact HGA | exact HV' | apply regular_typ_original; exact HT2 |
        apply regular_typ_original; exact HT2 | reflexivity | exact DC | exact DC'].
    + exact HV.
  - assert (HGA : @wf nat RankSorts _ (G & A)) by
      (eapply wf_cons; [exact HG | apply regular_typ_original; exact HT1]).
    eapply (application_realization_from_induction W H s HW HO HH classical_logic comparison gap choice HS).
    + apply regular_typ_original; exact HT3.
    + apply regular_typ_original; exact HT4.
    + exact HV.
    + apply IHHT3; assumption.
    + apply IHHT4; assumption.
    + apply IHHT1; assumption.
    + intros rho' HV'; apply IHHT2; assumption.
    + intros a a' DA DA'. eapply conversion; [exact HG | exact HV |
        apply regular_typ_original; exact HT1 | apply regular_typ_original; exact HT1 |
        reflexivity | exact DA | exact DA'].
    + intros rho' HV' b b' DB DB'. eapply conversion; [exact HGA | exact HV' |
        apply regular_typ_original; exact HT2 | apply regular_typ_original; exact HT2 |
        reflexivity | exact DB | exact DB'].
  - destruct (IHHT1 HG rho HV) as [v [a [Dt [DT Hv]]]].
    destruct (IHHT3 HG rho HV) as [b [q [DT' _]]].
    exists v, b. split; [exact Dt |]. split; [exact DT' |].
    eapply IN_sound_right; [| exact Hv].
    eapply conversion; [exact HG | exact HV | apply regular_typ_original; exact HT2 |
      apply regular_typ_original; exact HT3 | exact H0 | exact DT | exact DT'].
Qed.

Theorem original_realization_from_conversion n (G : Ctx nat n) t T :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
  forall rho, valid_valuation H s G rho -> realizes H s G rho t T.
Proof.
  intros HG HT. apply regular_realization_from_conversion; [| exact HG].
  apply (proj1 (regular_typ_equivalence n G t T HG)); exact HT.
Qed.
Theorem typed_coherence_from_conversion n (t : Term nat n) :
  forall (G : Ctx nat n) T rho, @wf nat RankSorts n G ->
  @typ nat RankSorts n G t T -> valid_valuation H s G rho ->
  forall v v', denotes H s n G rho t v -> denotes H s n G rho t v' -> EQ v v'.
Proof.
  induction t as [n i | n A IHA B IHB | n i | n A IHA t IHt | n t IHt u IHu];
    intros G T rho HG HT HV.
  - intros v v' D D'. eapply EQ_tran; [eapply denotes_sort_value; exact D |].
    apply EQ_sym; eapply denotes_sort_value; exact D'.
  - destruct (Π_inversion RankSorts A T B HT) as [m [k [l [R [TA [TB E]]]]]].
    assert (HGA : @wf nat RankSorts _ (G & A)) by (eapply wf_cons; eassumption).
    apply denotes_product_coherence.
    + intros a a' DA DA'. eapply conversion; [exact HG | exact HV | exact TA | exact TA |
        reflexivity | exact DA | exact DA'].
    + intros a x DA Hx b b' DB DB'. eapply conversion; [exact HGA |
        eapply valid_valuation_extend; eassumption | exact TB | exact TB |
        reflexivity | exact DB | exact DB'].
  - intros v v' D D'. eapply EQ_tran; [eapply denotes_variable_value; exact D |].
    apply EQ_sym; eapply denotes_variable_value; exact D'.
  - destruct (λ_inversion RankSorts A T t HT) as [m [B [TA [Tt E]]]].
    assert (HGA : @wf nat RankSorts _ (G & A)) by (eapply wf_cons; eassumption).
    apply denotes_lambda_coherence.
    + intros a a' DA DA'. eapply conversion; [exact HG | exact HV | exact TA | exact TA |
        reflexivity | exact DA | exact DA'].
    + intros a x DA Hx. eapply IHt; [exact HGA | exact Tt |].
      eapply valid_valuation_extend; eassumption.
    + intros a x DA Hx C C' TC TC' EC c c' DC DC'.
      destruct (type_is_correct t C TC HGA) as [k HC].
      destruct (type_is_correct t C' TC' HGA) as [k' HC'].
      eapply conversion; [exact HGA | eapply valid_valuation_extend; eassumption |
        exact HC | exact HC' | exact EC | exact DC | exact DC'].
  - destruct (app_inversion RankSorts t u T HT) as [A [B [Tt [Tu E]]]].
    apply denotes_application_coherence.
    + exact HG.
    + eapply IHt; eassumption.
    + eapply IHu; eassumption.
    + intros A0 A1 B0 B1 T0 T1 EA a a' DA DA'.
      destruct (typed_product_domain n G t A0 B0 HG T0) as [m0 TA0].
      destruct (typed_product_domain n G t A1 B1 HG T1) as [m1 TA1].
      eapply conversion; [exact HG | exact HV | exact TA0 | exact TA1 | exact EA | exact DA | exact DA'].
    + intros A0 A1 B0 B1 T0 T1 EB a y DA Hy b b' DB DB'.
      destruct (type_is_correct t (Π A0 B0) T0 HG) as [q0 TP0].
      destruct (type_is_correct t (Π A1 B1) T1 HG) as [q1 TP1].
      destruct (Π_inversion RankSorts A0 (𝓤 q0) B0 TP0)
        as [m0 [k0 [l0 [R0 [TA0 [TB0 E0]]]]]].
      destruct (Π_inversion RankSorts A1 (𝓤 q1) B1 TP1)
        as [m1 [k1 [l1 [R1 [TA1 [TB1 E1]]]]]].
      assert (EP : Π A1 B1 =ᵝ Π A0 B0) by (eapply uniqueness_of_typing; [exact T1 | exact T0]).
      destruct (equiv_Π_inversion A1 A0 B1 B0 EP) as [EA _].
      assert (HM : context_typing_morphism (G & A1) (G & A0)).
      { apply context_conversion_morphism.
        - constructor; [apply contexts_convertible_refl | exact EA].
        - eapply wf_cons; eassumption. }
      assert (TB1' : @typ nat RankSorts _ (G & A0) B1 (𝓤 k1)) by
        (eapply typing_context_transport; [exact HM | exact TB1]).
      eapply conversion; [eapply wf_cons; [exact HG | exact TA0] |
        eapply valid_valuation_extend; eassumption | exact TB0 | exact TB1' |
        exact EB | exact DB | exact DB'].
Qed.

Theorem typed_membership_from_conversion n (G : Ctx nat n) rho t T v a :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T -> valid_valuation H s G rho ->
  denotes H s n G rho t v -> denotes H s n G rho T a -> IN v (decode a).
Proof.
  intros HG HT HV Dt DT.
  destruct (original_realization_from_conversion n G t T HG HT rho HV)
    as [w [b [Dw [DB Hw]]]].
  assert (E : EQ w v) by (eapply typed_coherence_from_conversion; eassumption).
  destruct (type_is_correct t T HT HG) as [k TT].
  assert (EB : EQ (decode b) (decode a)).
  { eapply conversion; [exact HG | exact HV | exact TT | exact TT | reflexivity | exact DB | exact DT]. }
  eapply IN_sound_right; [exact EB |]. eapply IN_sound_left; eassumption.
Qed.

Theorem typed_rank_from_conversion n (G : Ctx nat n) rho t k v :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t (𝓤 k) ->
  valid_valuation H s G rho -> denotes H s n G rho t v -> IN v (U k).
Proof.
  intros HG HT HV Dt.
  assert (Hv : IN v (decode (repr (sort k)))).
  { eapply typed_membership_from_conversion; [exact HG | exact HT | exact HV | exact Dt | apply denotes_sort]. }
  exact (IN_sound_right v _ _ (decode_sort carrier k) Hv).
Qed.
End Realization.
Print Assumptions regular_realization_from_conversion.
Print Assumptions original_realization_from_conversion.
Check original_realization_from_conversion.
Print Assumptions typed_coherence_from_conversion.
Print Assumptions typed_membership_from_conversion.
Print Assumptions typed_rank_from_conversion.
Check typed_membership_from_conversion.
