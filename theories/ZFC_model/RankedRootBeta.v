(** Root reduction from actual structural lambda/argument certificates.
    Body membership and formation ranks are DERIVED from the inductive
    certificate, not supplied as semantic soundness hypotheses. The proven
    substitution case has a normal nonlambda argument. General lambda
    arguments still require hereditary substitution at a smaller cut rank. *)
From ZFC Require Import Sets Axioms.
From PTSrk Require Import Syntax Context Typing Ranks Reduction.
From PTSrkModel Require Import SetFunctions CodeUniverses CountableCodes
  CardinalHierarchy HierarchyBounds SuppliedHierarchy CardinalClassification
  CountableDichotomy GlobalOperations CanonicalTypeWitnesses CanonicalDenotation
  CanonicalRenaming RankedDenotation RankedTransport RankedSubstitution.
Import CodeUniverses.CodeUniverses.

Module RankedRootBeta.
Module RD := RankedDenotation.RankedDenotation.
Module RT := RankedTransport.RankedTransport.
Module RS := RankedSubstitution.RankedSubstitution.
Module CD := CanonicalDenotation.CanonicalDenotation.
Section Beta.
Variables W H s : Ens.
Hypothesis HW : transitive_set W.
Hypothesis HO : INC omega_codes W.
Hypothesis HH : tower_envelope W H.
Variable classical_logic : forall P : Prop, P \/ ~ P.
Hypothesis comparison : cardinal_comparability.
Hypothesis gap : infinite_powerset_gap.
Hypothesis choice : family_choice.
Hypothesis HS : selects_global_witnesses H s.

(** Identify the actual body value for ANY certified argument, including a
    lambda. This lemma does not assert normalization/substitution closure. *)
Theorem certified_root_body n (G : Ctx nat n) rho A t u T f c x a v :
  RD.certificate H s n G rho (lam A t) T f c ->
  RD.certificate H s n G rho u A x a ->
  CD.denotes H s n G rho (app (lam A t) u) v ->
  exists B w b, T = Π A B /\
    RD.certificate H s (S n) (G & A) (fin_match x rho) t B w b /\ EQ w v.
Proof.
  intros DF DU Dredex.
  destruct (RD.lambda_inversion H s n G rho A t T f c DF)
    as [B [m [k [a0 [b [body HI]]]]]].
  destruct HI as [ET [TB [Tt [NB [Nt [DA [DB [Dt [EB [Ebody [Ef Ec]]]]]]]]]]].
  assert (DA0 : CD.denotes H s n G rho A a0) by
    (exact (proj1 (RD.canonical_denotations H s _ _ _ _ _ _ _ DA))).
  assert (DUp : RD.certificate H s n G rho u A x a0).
  { eapply RT.certificate_type_alignment; [exact DU |
      eapply RD.original_typing; exact DU |
      exact (proj2 (RD.normality H s _ _ _ _ _ _ _ DU)) |exact DA0]. }
  assert (Ha : IN a0 (U m)).
  { eapply IN_sound_right; [apply decode_sort |].
    eapply (RD.membership W H s HW HO HH classical_logic comparison gap choice HS); exact DA. }
  assert (Hb : forall y, IN y (decode a0) -> IN (b y) (U k)).
  { intros y Hy; eapply IN_sound_right; [apply decode_sort |].
    eapply (RD.membership W H s HW HO HH classical_logic comparison gap choice HS); apply DB; exact Hy. }
  assert (Hbody : forall y, IN y (decode a0) -> IN (body y) (decode (b y))).
  { intros y Hy; eapply (RD.membership W H s HW HO HH classical_logic comparison gap choice HS).
    apply Dt; exact Hy. }
  assert (Hx : IN x (decode a0)).
  { eapply (RD.membership W H s HW HO HH classical_logic comparison gap choice HS); exact DUp. }
  assert (Dbodyredex : CD.denotes H s n G rho (app (lam A t) u) (body x)).
  { eapply CD.denotes_equal.
    - eapply CD.denotes_application with (A := A) (B := B) (a := a0) (b := b)
        (f := semantic_lambda H s a0 b body) (x := x).
      + rewrite <- ET; eapply RD.original_typing; exact DF.
      + rewrite <- ET; exact (proj2 (RD.normality H s _ _ _ _ _ _ _ DF)).
      + exact DA0.
      + intros y Hy; exact (proj1 (RD.canonical_denotations H s _ _ _ _ _ _ _ (DB y Hy))).
      + exact EB.
      + eapply CD.denotes_equal; [|exact Ef].
        exact (proj1 (RD.canonical_denotations H s _ _ _ _ _ _ _ DF)).
      + exact (proj1 (RD.canonical_denotations H s _ _ _ _ _ _ _ DU)).
    - exact (semantic_beta W H s HW HO HH classical_logic comparison gap choice HS
        m k a0 b body x Ha Hb Ebody Hbody Hx). }
  exists B, (body x), (b x); split; [exact ET |]. split.
  - apply Dt; exact Hx.
  - eapply CD.coherent; [exact Dbodyredex |exact Dredex].
Qed.

Theorem certified_root_beta_nonlambda n (G : Ctx nat n) rho A t u T f c x a v :
  RD.certificate H s n G rho (lam A t) T f c ->
  RD.certificate H s n G rho u A x a -> not_lambda u ->
  RS.certified_variables H s G rho ->
  CD.denotes H s n G rho (app (lam A t) u) v ->
  exists B b, T = Π A B /\ app (lam A t) u →ᵝ t ◁ u /\
    RD.certificate H s n G rho (t ◁ u) (B ◁ u) v b.
Proof.
  intros DF DU Lu HV DR.
  destruct (certified_root_body n G rho A t u T f c x a v DF DU DR)
    as [B [w [b [ET [DT EV]]]]].
  exists B, b; split; [exact ET |]. split; [apply step_beta |].
  eapply RD.certificate_equal; [|exact EV |apply EQ_refl].
  eapply RS.certificate_single_substitution; [eapply RD.original_typing; exact DU |
    exact Lu |exact HV |exact DU |exact DT].
Qed.
End Beta.
End RankedRootBeta.

Print Assumptions RankedRootBeta.certified_root_beta_nonlambda.
Print Assumptions RankedRootBeta.certified_root_body.
Check RankedRootBeta.certified_root_beta_nonlambda.
