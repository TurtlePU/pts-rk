(** Beta with different but semantically equal product witnesses. The
    equalities/typing facts below remain obligations for general soundness. *)
From ZFC Require Import Sets Axioms.
From PTSrk Require Import Syntax Context Typing Ranks Inversions DefEq.
From PTSrkModel Require Import SetFunctions CodeUniverses CountableCodes
  CardinalHierarchy HierarchyBounds SuppliedHierarchy CardinalClassification
  CountableDichotomy GlobalOperations Denotation.
Import CodeUniverses.CodeUniverses.

Lemma beta_argument_typing n (G : Ctx nat n) A t u T :
  @typ nat RankSorts n G (app (lam A t) u) T -> @typ nat RankSorts n G u A.
Proof.
  intro HT. destruct (app_inversion RankSorts (lam A t) u T HT)
    as [U [B [Tf [Tu ET]]]].
  destruct (λ_inversion RankSorts A (Π U B) t Tf) as [l [C [TA [Tt EP]]]].
  apply equiv_Π_inversion in EP as [EA EB].
  eapply typ_conv; [exact Tu | exact TA | exact EA].
Qed.

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

Theorem semantic_beta_across_products a a' b b' body f x m k :
  EQ (decode a) (decode a') ->
  family_extensional (fun y => decode (b y)) ->
  family_extensional (fun y => decode (b' y)) ->
  (forall y, IN y (decode a) -> EQ (decode (b y)) (decode (b' y))) ->
  EQ f (semantic_lambda H s a' b' body) ->
  IN a' (U m) -> (forall y, IN y (decode a') -> IN (b' y) (U k)) ->
  family_extensional body -> (forall y, IN y (decode a') -> IN (body y) (decode (b' y))) ->
  IN x (decode a') -> EQ (semantic_application H s a b f x) (body x).
Proof.
  intros EA EB EB' EF Ef Ha Hb Ebody Hbody Hx.
  eapply EQ_tran.
  - exact (semantic_application_congruence H s a a' b b' f
      (semantic_lambda H s a' b' body) x x EA EB EB' EF Ef (EQ_refl x)).
  - exact (semantic_beta W H s HW HO HH classical_logic comparison gap choice HS
      m k a' b' body x Ha Hb Ebody Hbody Hx).
Qed.

Theorem denotes_beta_across_products n (G : Ctx nat n) rho A t u T a a' b b' body f x v m k :
  @typ nat RankSorts n G (app (lam A t) u) T ->
  (forall y, IN y (decode a') -> denotes H s (S n) (G & A) (fin_match y rho) t (body y)) ->
  denotes H s n G rho u x ->
  EQ v (semantic_application H s a b f x) ->
  EQ (decode a) (decode a') ->
  family_extensional (fun y => decode (b y)) ->
  family_extensional (fun y => decode (b' y)) ->
  (forall y, IN y (decode a) -> EQ (decode (b y)) (decode (b' y))) ->
  EQ f (semantic_lambda H s a' b' body) ->
  IN a' (U m) -> (forall y, IN y (decode a') -> IN (b' y) (U k)) ->
  family_extensional body -> (forall y, IN y (decode a') -> IN (body y) (decode (b' y))) ->
  IN x (decode a') -> denotes H s n G rho (t ◁ u) v.
Proof.
  intros HT Dt Du Ev EA EB EB' EF Ef Ha Hb Ebody Hbody Hx.
  pose proof (beta_argument_typing n G A t u T HT) as Tu.
  eapply denotes_equal.
  - eapply denotes_subst; [exact Tu | apply Dt; exact Hx | exact Du].
  - apply EQ_sym. eapply EQ_tran; [exact Ev |].
    exact (semantic_beta_across_products a a' b b' body f x m k
      EA EB EB' EF Ef Ha Hb Ebody Hbody Hx).
Qed.
End Beta.
Print Assumptions beta_argument_typing.
Print Assumptions semantic_beta_across_products.
Print Assumptions denotes_beta_across_products.
Check denotes_beta_across_products.
