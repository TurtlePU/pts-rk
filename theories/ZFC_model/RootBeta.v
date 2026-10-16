(** Root beta from denotation inversion and local semantic induction facts.
    The local conversion/rank/membership premises remain to be discharged by
    the fundamental proof; no global preservation or soundness is assumed. *)
From ZFC Require Import Sets Axioms.
From PTSrk Require Import Syntax Context Typing Ranks Inversions DefEq Preservation AbstractRewriting.
From PTSrkModel Require Import SetFunctions CodeUniverses CountableCodes
  CardinalHierarchy HierarchyBounds SuppliedHierarchy CardinalClassification
  CountableDichotomy GlobalOperations Denotation DenotationInversion
  ContextTransport BetaWitnessTransport InterpretedContexts DenotationBeta.
Import CodeUniverses.CodeUniverses.

Section RootBeta.
Variables W H s : Ens.
Hypothesis HW : transitive_set W.
Hypothesis HO : INC omega_codes W.
Hypothesis HH : tower_envelope W H.
Variable classical_logic : forall P : Prop, P \/ ~ P.
Hypothesis comparison : cardinal_comparability.
Hypothesis gap : infinite_powerset_gap.
Hypothesis choice : family_choice.
Hypothesis HS : selects_global_witnesses H s.

Theorem denotes_root_beta n (G : Ctx nat n) rho A t u T :
  @wf nat RankSorts n G ->
  @typ nat RankSorts n G (app (lam A t) u) T ->
  (forall U l a a', @typ nat RankSorts n G U (𝓤 l) ->
    U =ᵝ A -> denotes H s n G rho U a ->
    denotes H s n G rho A a' -> EQ (decode a) (decode a')) ->
  (forall B C j k a y b c,
    @typ nat RankSorts (S n) (G & A) B (𝓤 j) ->
    @typ nat RankSorts (S n) (G & A) C (𝓤 k) ->
    B =ᵝ C ->
    denotes H s n G rho A a -> IN y (decode a) ->
    denotes H s (S n) (G & A) (fin_match y rho) B b ->
    denotes H s (S n) (G & A) (fin_match y rho) C c ->
    EQ (decode b) (decode c)) ->
  (forall l a, @typ nat RankSorts n G A (𝓤 l) ->
    denotes H s n G rho A a -> IN a (U l)) ->
  (forall C k a y c, @typ nat RankSorts (S n) (G & A) C (𝓤 k) ->
    denotes H s n G rho A a -> IN y (decode a) ->
    denotes H s (S n) (G & A) (fin_match y rho) C c -> IN c (U k)) ->
  (forall C a y c v, @typ nat RankSorts (S n) (G & A) t C ->
    denotes H s n G rho A a -> IN y (decode a) ->
    denotes H s (S n) (G & A) (fin_match y rho) C c ->
    denotes H s (S n) (G & A) (fin_match y rho) t v -> IN v (decode c)) ->
  (forall a x, @typ nat RankSorts n G u A ->
    denotes H s n G rho A a -> denotes H s n G rho u x ->
    IN x (decode a)) ->
  forall v, denotes H s n G rho (app (lam A t) u) v ->
    denotes H s n G rho (t ◁ u) v.
Proof.
  intros HG HT CA CB RA RC Mt Mu v D.
  destruct (denotes_application_inversion H s n G rho (lam A t) u v D)
    as [U0 [B [a [b [f [x [Tf [DA [DB [EB [Df [Du Ev]]]]]]]]]]]].
  destruct (denotes_lambda_inversion H s n G rho A t f Df)
    as [C [a' [c [body [Tt [DA' [DC [Dt [EC [Ebody Ef]]]]]]]]]].
  destruct (λ_inversion RankSorts A (Π U0 B) t Tf)
    as [l [C0 [TA [Tt0 EP]]]].
  assert (Tf' : @typ nat RankSorts n G (lam A t) (Π A C)) by
    (eapply typ_λ; eassumption).
  assert (ET : Π U0 B =ᵝ Π A C) by (eapply uniqueness_of_typing; eassumption).
  destruct (equiv_Π_inversion U0 A B C ET) as [EU EBt].
  assert (HGA : @wf nat RankSorts (S n) (G & A)) by (eapply wf_cons; eassumption).
  destruct (type_is_correct t C Tt HGA) as [k TC].
  destruct (type_is_correct (lam A t) (Π U0 B) Tf HG) as [q TP].
  destruct (Π_inversion RankSorts U0 (𝓤 q) B TP)
    as [m [j [r [R [TU [TB EQr]]]]]].
  assert (EA : EQ (decode a) (decode a')) by (eapply CA; eassumption).
  assert (HM : context_typing_morphism (G & U0) (G & A)).
  { apply context_conversion_morphism.
    - constructor; [apply contexts_convertible_refl | exact EU].
    - eapply wf_cons; eassumption. }
  assert (TB' : @typ nat RankSorts (S n) (G & A) B (𝓤 j)) by
    (eapply typing_context_transport; [exact HM | exact TB]).
  eapply (denotes_beta_across_products W H s HW HO HH classical_logic comparison gap choice HS
    n G rho A t u T a a' b c body f x v l k).
  - exact HT.
  - exact Dt.
  - exact Du.
  - exact Ev.
  - exact EA.
  - exact EB.
  - exact EC.
  - intros y Hy. eapply CB; [exact TB' | exact TC | exact EBt | exact DA' | | |].
    + exact (IN_sound_right y _ _ EA Hy).
    + eapply denotes_context_transport; [exact HM | apply DB; exact Hy].
    + apply DC. exact (IN_sound_right y _ _ EA Hy).
  - exact Ef.
  - eapply RA; eassumption.
  - intros y Hy. eapply RC; [exact TC | exact DA' | exact Hy | apply DC; exact Hy].
  - exact Ebody.
  - intros y Hy. eapply Mt; [exact Tt | exact DA' | exact Hy | apply DC; exact Hy | apply Dt; exact Hy].
  - eapply Mu; [eapply beta_argument_typing; exact HT | exact DA' | exact Du].
Qed.
(** The alternative route needs ranked realizations only, not universal rank
    or membership assertions about arbitrary denotations. Coherence of the
    redex is derived from constituent coherence and local type conversion. *)
Theorem realized_root_beta n (G : Ctx nat n) rho A B t u m k :
  @wf nat RankSorts n G ->
  @typ nat RankSorts n G A (𝓤 m) ->
  @typ nat RankSorts (S n) (G & A) t B ->
  @typ nat RankSorts n G u A -> valid_valuation H s G rho ->
  realizes H s G rho A (𝓤 m) -> realizes H s G rho u A ->
  (forall rho', valid_valuation H s (G & A) rho' -> realizes H s (G & A) rho' t B) ->
  (forall rho', valid_valuation H s (G & A) rho' -> realizes H s (G & A) rho' B (𝓤 k)) ->
  (forall C l a a', @typ nat RankSorts n G C (𝓤 l) -> C =ᵝ A ->
    denotes H s n G rho C a -> denotes H s n G rho A a' ->
    EQ (decode a) (decode a')) ->
  (forall rho', valid_valuation H s (G & A) rho' -> forall v v',
    denotes H s (S n) (G & A) rho' t v ->
    denotes H s (S n) (G & A) rho' t v' -> EQ v v') ->
  (forall x x', denotes H s n G rho u x -> denotes H s n G rho u x' -> EQ x x') ->
  (forall rho', valid_valuation H s (G & A) rho' -> forall C C',
    @typ nat RankSorts (S n) (G & A) t C ->
    @typ nat RankSorts (S n) (G & A) t C' -> C =ᵝ C' ->
    forall c c', denotes H s (S n) (G & A) rho' C c ->
      denotes H s (S n) (G & A) rho' C' c' -> EQ (decode c) (decode c')) ->
  forall v, denotes H s n G rho (app (lam A t) u) v ->
    exists c, denotes H s n G rho (t ◁ u) v /\
      denotes H s n G rho (B ◁ u) c /\ IN v (decode c) /\ IN c (U k).
Proof.
  intros HG TA Tt Tu HV HA HU Ht HB CA Ct Cu CB v Dv.
  assert (CA0 : forall a a', denotes H s n G rho A a ->
    denotes H s n G rho A a' -> EQ (decode a) (decode a')).
  { intros a a' DA DA'. eapply CA; [exact TA | reflexivity | exact DA | exact DA']. }
  pose proof HA as HA0. destruct HA0 as [a0 [q0 [DA0 _]]].
  assert (CL : forall f f', denotes H s n G rho (lam A t) f ->
    denotes H s n G rho (lam A t) f' -> EQ f f').
  { apply denotes_lambda_coherence; [exact CA0 | |].
    - intros a x DA Hx. apply Ct. eapply valid_valuation_extend; eassumption.
    - intros a x DA Hx. apply CB. eapply valid_valuation_extend; eassumption. }
  assert (CR : forall w w', denotes H s n G rho (app (lam A t) u) w ->
    denotes H s n G rho (app (lam A t) u) w' -> EQ w w').
  { apply denotes_application_coherence; [exact HG | exact CL | exact Cu | |].
    - intros A0 A1 B0 B1 T0 T1 E a a' DA DA'.
      destruct (lambda_product_body n G A t A0 B0 HG T0) as [E0 _].
      destruct (lambda_product_body n G A t A1 B1 HG T1) as [E1 _].
      destruct (typed_product_domain n G (lam A t) A0 B0 HG T0) as [l0 TA0].
      destruct (typed_product_domain n G (lam A t) A1 B1 HG T1) as [l1 TA1].
      eapply EQ_tran with (E2 := decode a0).
      + exact (CA A0 l0 a a0 TA0 E0 DA DA0).
      + apply EQ_sym. exact (CA A1 l1 a' a0 TA1 E1 DA' DA0).
    - intros A0 A1 B0 B1 T0 T1 E a y DA Hy b b' DB DB'.
      destruct (lambda_product_body n G A t A0 B0 HG T0) as [E0 [TB0 _]].
      destruct (lambda_product_body n G A t A1 B1 HG T1) as [E1 [TB1 _]].
      destruct (typed_product_domain n G (lam A t) A0 B0 HG T0) as [l0 TA0].
      assert (EA : EQ (decode a) (decode a0)) by
        (exact (CA A0 l0 a a0 TA0 E0 DA DA0)).
      assert (HY : valid_valuation H s (G & A) (fin_match y rho)).
      { eapply valid_valuation_extend; [exact HV | exact DA0 |].
        exact (IN_sound_right y _ _ EA Hy). }
      eapply CB; [exact HY | exact TB0 | exact TB1 | exact E | |].
      + apply (proj1 (denotes_binder_context_conversion H s n G A0 A l0 m
          (fin_match y rho) B0 b HG TA0 TA E0)); exact DB.
      + apply (proj1 (denotes_binder_context_conversion H s n G A0 A l0 m
          (fin_match y rho) B1 b' HG TA0 TA E0)); exact DB'. }
  assert (CB0 : forall rho', valid_valuation H s (G & A) rho' -> forall b b',
    denotes H s (S n) (G & A) rho' B b ->
    denotes H s (S n) (G & A) rho' B b' -> EQ (decode b) (decode b')).
  { intros rho' HV'. apply CB; [exact HV' | exact Tt | exact Tt | reflexivity]. }
  destruct (realized_beta W H s HW HO HH classical_logic comparison gap choice HS
    n G rho A B t u m k TA Tt Tu HV HA HU Ht HB CA0 CB0)
    as [w [c [Dw [Dr [Dc [Hw Hc]]]]]].
  assert (E : EQ w v) by (apply CR; assumption).
  exists c. split; [eapply denotes_equal; eassumption |].
  split; [exact Dc |]. split; [eapply IN_sound_left; eassumption | exact Hc].
Qed.
End RootBeta.
Print Assumptions denotes_root_beta.
Check denotes_root_beta.
Print Assumptions realized_root_beta.
Check realized_root_beta.
