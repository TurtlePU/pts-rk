(** All five original relational R schemes in the new G15/E7/O15 model.
    The cutoff and both arithmetic indices are arbitrary, not enumerated. *)
From Stdlib Require Import Lists.List Arith.PeanoNat.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRStructural DirectRLogic DirectRFiniteUp DirectRSymbolic.
From Interpretation_of_R.relational Require Import DirectRUnary DirectRUnaryBounded
  DirectRUnaryEvaluation DirectRRelationalSyntax.
From OrderedSemiring Require Import ModelInterface FirstOrderTranslation
  FiniteCuts OrderNumerals OrderCuts BoundedCases.
Import ListNotations.

Module RAxiomRealization.
Import CommonCodes Core Structural NegativeLogic FiniteUp FirstOrderTranslation.

Lemma source_add_schema :
  app (app (lift_closed Model.addition) (@var nat 2 (fsucc fzero))) V0 =ᵝ
    app (app (lift_closed Unary.addition) V0) (shift V0).
Proof. match goal with |- ?A =ᵝ ?B => let p := Symbolic.beta_compare A B in exact p end. Qed.
Lemma source_mul_schema :
  app (app (lift_closed Model.multiplication) (@var nat 2 (fsucc fzero))) V0 =ᵝ
    app (app (lift_closed Unary.multiplication) V0) (shift V0).
Proof. match goal with |- ?A =ᵝ ?B => let p := Symbolic.beta_compare A B in exact p end. Qed.
Lemma source_add_beta {n} (x y : Term nat n) :
  app (app (lift_closed Model.addition) x) y =ᵝ
    app (app (lift_closed Unary.addition) y) x.
Proof.
  pose proof (replace_equiv (fin_match y (fin_match x (fun i : Fin 0 => match i with end)))
    _ _ source_add_schema) as H.
  rewrite !replace_application, !replace_lift_closed in H. exact H.
Qed.
Lemma source_mul_beta {n} (x y : Term nat n) :
  app (app (lift_closed Model.multiplication) x) y =ᵝ
    app (app (lift_closed Unary.multiplication) y) x.
Proof.
  pose proof (replace_equiv (fin_match y (fin_match x (fun i : Fin 0 => match i with end)))
    _ _ source_mul_schema) as H.
  rewrite !replace_application, !replace_lift_closed in H. exact H.
Qed.
Lemma source_add_numerals m k :
  app (app Model.addition (Unary.numeral m)) (Unary.numeral k) =ᵝ Unary.numeral (m+k).
Proof.
  rewrite <- (lift_closed_zero Model.addition).
  eapply beta_trans; [apply source_add_beta |]. rewrite lift_closed_zero, Nat.add_comm.
  apply UnaryEvaluation.addition_numerals.
Qed.
Lemma source_mul_numerals m k :
  app (app Model.multiplication (Unary.numeral m)) (Unary.numeral k) =ᵝ Unary.numeral (m*k).
Proof.
  rewrite <- (lift_closed_zero Model.multiplication).
  eapply beta_trans; [apply source_mul_beta |]. rewrite lift_closed_zero, Nat.mul_comm.
  apply UnaryEvaluation.multiplication_numerals.
Qed.

Definition GraphEquivalence {n} (l r : closed_term) (d : Term nat n) :=
  UnaryBounded.Equivalence (Model.E (lift_closed l) d) (Model.E (lift_closed r) d).
Lemma shift_graph_equivalence {n} l r (d : Term nat n) :
  shift (GraphEquivalence l r d) = GraphEquivalence l r (shift d).
Proof.
  change (shift (UnaryBounded.Equivalence (FiniteCuts.E (lift_closed l) d)
    (FiniteCuts.E (lift_closed r) d)) = UnaryBounded.Equivalence
      (FiniteCuts.E (lift_closed l) (shift d)) (FiniteCuts.E (lift_closed r) (shift d))).
  unfold UnaryBounded.Equivalence, Conj, Neg.
  rewrite !shift_arrow, !FiniteCuts.shift_E, <- !lift_closed_shift. reflexivity.
Qed.
Lemma graph_equivalence_in_context {n} (Γ : Ctx nat n) l r d :
  Typed ε l Unary.Domain -> Typed ε r Unary.Domain ->
  Typed Γ d (lift_closed Unary.Domain) -> l =ᵝ r -> inhabited Γ (GraphEquivalence l r d).
Proof.
  intros Hl Hr Hd Heq.
  pose proof (Model.equality_in_context Γ _ _ (lift_closed_typed Γ _ _ Hl) Hd) as HA.
  pose proof (Model.equality_in_context Γ _ _ (lift_closed_typed Γ _ _ Hr) Hd) as HB.
  assert (HAB : Model.E (lift_closed l) d =ᵝ Model.E (lift_closed r) d).
  { apply beta_app; [|reflexivity]. apply beta_app; [reflexivity |].
    apply rename_equiv. exact Heq. }
  apply UnaryBounded.equivalence_intro; [exists 7; exact HA |exists 7; exact HB | |].
  - eapply inhabited_conversion.
    + apply identity_inhabited. exists 7. exact HA.
    + exact (arrow_formation Γ _ _ _ _ HA HB).
    + apply arrow_beta; [reflexivity |exact HAB].
  - eapply inhabited_conversion.
    + apply identity_inhabited. exists 7. exact HB.
    + exact (arrow_formation Γ _ _ _ _ HB HA).
    + apply arrow_beta; [reflexivity |symmetry; exact HAB].
Qed.
Definition equation_scheme l r : closed_term :=
  Π Unary.Domain (Arrow (Model.admitted V0) (GraphEquivalence l r V0)).
Theorem equation_scheme_realized l r :
  Typed ε l Unary.Domain -> Typed ε r Unary.Domain -> l =ᵝ r -> Realizes (equation_scheme l r).
Proof.
  intros Hl Hr Heq. unfold equation_scheme. apply product_intro.
  - exists 3. exact Unary.domain_formation.
  - apply arrow_intro.
    + exists 17. apply Model.admitted_formation_in_context. exact (tV _ fzero).
    + rewrite shift_graph_equivalence. apply graph_equivalence_in_context; auto.
      exact (tV _ (fsucc fzero)).
Qed.
Definition R1 m k := equation_scheme
  (app (app Model.addition (Unary.numeral m)) (Unary.numeral k)) (Unary.numeral (m+k)).
Definition R2 m k := equation_scheme
  (app (app Model.multiplication (Unary.numeral m)) (Unary.numeral k)) (Unary.numeral (m*k)).
Theorem R1_realized m k : Realizes (R1 m k).
Proof.
  apply equation_scheme_realized; [|apply Unary.numeral_typed |apply source_add_numerals].
  eapply arrow_application; [|apply Unary.numeral_typed].
  eapply arrow_application; [apply Model.addition_typed |apply Unary.numeral_typed].
Qed.
Theorem R2_realized m k : Realizes (R2 m k).
Proof.
  apply equation_scheme_realized; [|apply Unary.numeral_typed |apply source_mul_numerals].
  eapply arrow_application; [|apply Unary.numeral_typed].
  eapply arrow_application; [apply Model.multiplication_typed |apply Unary.numeral_typed].
Qed.

Lemma formula_iff {k n} A B (env : Fin k -> Term nat n) :
  formula (Relational.iff A B) env = UnaryBounded.Equivalence (formula A env) (formula B env).
Proof. reflexivity. Qed.
Lemma formula_disj {k n} xs (env : Fin k -> Term nat n) :
  formula (Relational.disj xs) env = FlatOr (map (fun A => formula A env) xs).
Proof.
  unfold Relational.disj, FlatOr. induction xs; cbn [fold_right map formula Relational.neg];
    [reflexivity |rewrite IHxs; reflexivity].
Qed.
Lemma formula_bounded {k n} cutoff t (env : Fin k -> Term nat n) :
  formula (Relational.disj (map (fun i => Relational.equal t (Relational.numeral i))
    (seq 0 (S cutoff)))) env = BoundedCases.Bounded cutoff (term env t).
Proof.
  rewrite formula_disj. unfold BoundedCases.Bounded, FiniteCuts.atoms.
  rewrite map_map. f_equal. apply map_ext. intro i. cbn [formula]. rewrite numeral_translation. reflexivity.
Qed.
Lemma rename_bounded {m n} (f : Fin m -> Fin n) cutoff d :
  rename f (BoundedCases.Bounded cutoff d) = BoundedCases.Bounded cutoff (rename f d).
Proof.
  rewrite rename_as_replace. unfold BoundedCases.Bounded, FiniteCuts.atoms.
  rewrite replace_flat, map_map. f_equal. apply map_ext. intro i.
  unfold FiniteCuts.E. rewrite !replace_application, !replace_lift_closed, <- rename_as_replace. reflexivity.
Qed.
Lemma rename_equivalence {m n} (f : Fin m -> Fin n) A B :
  rename f (UnaryBounded.Equivalence A B) =
    UnaryBounded.Equivalence (rename f A) (rename f B).
Proof.
  unfold UnaryBounded.Equivalence, Conj, Neg.
  rewrite !rename_arrow, !rename_lift_closed. reflexivity.
Qed.
Theorem source_axiom_realized {k n} (Γ : Ctx nat n) env (A : Relational.formula k) :
  Relational.axiom A -> inhabited Γ (formula A env).
Proof.
  intro HA. destruct HA.
  - cbn [formula]. rewrite formula_iff. cbn [formula term]. rewrite !numeral_translation.
    destruct (R1_realized m k0) as [p Hp]. exists (lift_closed p).
    pose proof (lift_closed_typed Γ _ _ Hp) as H.
    unfold lift_closed at 2 in H. unfold R1, equation_scheme, GraphEquivalence in H.
    rewrite rename_product, rename_arrow, rename_equivalence in H.
    unfold Model.E, Model.admitted in H. rewrite !rename_application, !rename_lift_closed in H. exact H.
  - cbn [formula]. rewrite formula_iff. cbn [formula term]. rewrite !numeral_translation.
    destruct (R2_realized m k0) as [p Hp]. exists (lift_closed p).
    pose proof (lift_closed_typed Γ _ _ Hp) as H.
    unfold lift_closed at 2 in H. unfold R2, equation_scheme, GraphEquivalence in H.
    rewrite rename_product, rename_arrow, rename_equivalence in H.
    unfold Model.E, Model.admitted in H. rewrite !rename_application, !rename_lift_closed in H. exact H.
  - cbn [Relational.neg formula]. rewrite !numeral_translation.
    exact (OrderNumerals.numeral_inequality Γ m k0 H).
  - cbn [formula]. rewrite formula_iff, formula_bounded. cbn [formula term]. rewrite numeral_translation.
    destruct (BoundedCases.R4_realized k0) as [p Hp]. exists (lift_closed p).
    pose proof (lift_closed_typed Γ _ _ Hp) as H.
    unfold lift_closed at 2 in H. unfold BoundedCases.R4, BoundedCases.BoundEquivalence in H.
    rewrite rename_product, rename_arrow, rename_equivalence, rename_bounded in H.
    unfold OrderCuts.O, FiniteCuts.G in H. rewrite !rename_application, !rename_lift_closed in H. exact H.
  - cbn [formula]. rewrite formula_disj. cbn [map formula term]. rewrite !numeral_translation.
    destruct (BoundedCases.R5_realized k0) as [p Hp]. exists (lift_closed p).
    pose proof (lift_closed_typed Γ _ _ Hp) as H.
    unfold lift_closed at 2 in H. unfold BoundedCases.R5, BoundedCases.Compare in H.
    rewrite rename_product, rename_arrow in H.
    rewrite rename_as_replace with (t:=FlatOr _) in H. rewrite replace_flat in H. cbn [map] in H.
    unfold OrderCuts.O, FiniteCuts.G in H.
    rewrite !rename_application, !rename_lift_closed, !replace_application, !replace_lift_closed in H. exact H.
Qed.
Theorem r_axioms_realized A : @Relational.axiom 0 A -> Realizes (sentence A).
Proof. apply (source_axiom_realized ε empty_env A). Qed.

Print Assumptions R1_realized.
Print Assumptions R2_realized.
Print Assumptions r_axioms_realized.
End RAxiomRealization.
