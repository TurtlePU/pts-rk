(** Direct realization of the independent functional ordered-rig axioms.
    Source addition and multiplication are genuine term constructors. *)
From Stdlib Require Import Lists.List Arith.PeanoNat.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRStructural DirectRLogic DirectRFiniteUp DirectRCheck.
From Interpretation_of_R.relational Require Import DirectRUnary DirectRUnaryBounded.
From OrderedSemiring Require Import RigCodes ObservationEquality ArithmeticCongruence
  SemiringLaws Cancellation NaturalOrder OrderLaws RigAxiomRealization
  ModelInterface FiniteCuts OrderNumerals OrderCuts BoundedCases StrictBounded
  GroundFaithfulness.
From OrderedSemiringFunctional Require Import Source Translation.
Import ListNotations.

Module FunctionalAxioms.
Import CommonCodes Core Structural NegativeLogic.
Import ObservationEquality ArithmeticCongruence SemiringLaws.
Import FunctionalTranslation.
Module FS := FunctionalSource.
Module R := RigAxiomRealization.
Definition X := R.X.
Definition G7 := R.G7.
Definition G11 := R.G11.
Definition fields := R.fields.
Definition H := R.H.
Definition statement := sentence.

Definition add_commutative := close (nlams (fields 2)
  (add_comm (X 1) (X 0) (G7 1) (G7 0))) eq_refl.
Definition mul_commutative := close (nlams (fields 2)
  (mul_comm (X 1) (X 0) (G11 1) (G11 0))) eq_refl.
Definition add_associative := close (nlams (fields 3)
  (refl (add (add (X 2) (X 1)) (X 0)))) eq_refl.
Definition mul_associative := close (nlams (fields 3)
  (refl (mul (mul (X 2) (X 1)) (X 0)))) eq_refl.
Definition add_zero := R.add_zero.
Definition mul_zero := R.mul_zero.
Definition mul_one := R.mul_one.
Definition distributivity := close (nlams (fields 3)
  (refl (mul (add (X 2) (X 1)) (X 0)))) eq_refl.
Definition additive_cancellation := close
  (nlams (fields 3 ++ [R.eqarg 0 (add (X 1) (X 0)) (add (X 2) (X 0))])
    (Cancellation.cancel_left (X 0) (X 1) (X 2) (G11 0) (G7 1) (G7 2)
      (trans (add (X 0) (X 1)) (add (X 1) (X 0)) (add (X 0) (X 2))
        (add_comm (X 0) (X 1) (G7 0) (G7 1))
        (trans (add (X 1) (X 0)) (add (X 2) (X 0)) (add (X 0) (X 2))
          (H 0) (add_comm (X 2) (X 0) (G7 2) (G7 0)))))) eq_refl.
Definition order_refl := R.order_refl.
Definition order_trans := R.order_trans.
Definition order_antisym := R.order_antisym.
Definition zero_least := R.zero_least.
Definition nontrivial := R.nontrivial.
Definition monotone_fields := fields 3 ++ [(800,OrderLaws.ord (X 0) (X 1))].
Definition add_monotone := close (nlams monotone_fields
  (napps (NClosed OrderLaws.addition_monotone_left)
    [X 0;X 1;X 2;G11 0;G11 1;G11 2;H 0])) eq_refl.
Definition mul_monotone := close (nlams monotone_fields
  (napps (NClosed OrderLaws.multiplication_monotone_left)
    [X 0;X 1;X 2;G11 0;G11 1;G11 2;H 0])) eq_refl.
Definition add_strict_monotone := close
  (nlams (fields 3 ++ [(800,OrderLaws.strict (X 0) (X 1))])
    (napps (NClosed OrderLaws.addition_strict_monotone_left)
      [X 0;X 1;X 2;G11 0;G11 1;G11 2;H 0])) eq_refl.
Definition mul_strict_monotone := close
  (nlams (fields 3 ++ [(800,OrderLaws.strict (X 0) (X 1));
                      (801,OrderLaws.strict nZ (X 2))])
    (napps (NClosed OrderLaws.multiplication_strict_monotone_left)
      [X 0;X 1;X 2;G11 0;G11 1;G11 2;H 0;H 1])) eq_refl.
Definition successor_add_one := R.successor_add_one.

Lemma add_commutative_typed : Typed ε add_commutative (statement FS.add_commutative).
Proof. RkCheck.certify_with 4096. Qed.
Lemma mul_commutative_typed : Typed ε mul_commutative (statement FS.mul_commutative).
Proof. RkCheck.certify_with 4096. Qed.
Lemma add_associative_typed : Typed ε add_associative (statement FS.add_associative).
Proof. RkCheck.certify_with 4096. Qed.
Lemma mul_associative_typed : Typed ε mul_associative (statement FS.mul_associative).
Proof. RkCheck.certify_with 4096. Qed.
Lemma add_zero_typed : Typed ε add_zero (statement FS.add_zero).
Proof. RkCheck.certify_with 4096. Qed.
Lemma mul_zero_typed : Typed ε mul_zero (statement FS.mul_zero).
Proof. RkCheck.certify_with 4096. Qed.
Lemma mul_one_typed : Typed ε mul_one (statement FS.mul_one).
Proof. RkCheck.certify_with 4096. Qed.
Lemma distributivity_typed : Typed ε distributivity (statement FS.distributivity).
Proof. RkCheck.certify_with 4096. Qed.
Lemma additive_cancellation_typed : Typed ε additive_cancellation (statement FS.additive_cancellation).
Proof. RkCheck.certify_with 4096. Qed.
Lemma order_refl_typed : Typed ε order_refl (statement FS.order_refl).
Proof. RkCheck.certify_with 4096. Qed.
Lemma order_trans_typed : Typed ε order_trans (statement FS.order_trans).
Proof. RkCheck.certify_with 4096. Qed.
Lemma order_antisym_typed : Typed ε order_antisym (statement FS.order_antisym).
Proof. RkCheck.certify_with 4096. Qed.
Lemma zero_least_typed : Typed ε zero_least (statement FS.zero_least).
Proof. RkCheck.certify_with 4096. Qed.
Lemma nontrivial_typed : Typed ε nontrivial (statement FS.nontrivial).
Proof. RkCheck.certify_with 4096. Qed.
Lemma add_monotone_typed : Typed ε add_monotone (statement FS.add_monotone).
Proof. RkCheck.certify_with 4096. Qed.
Lemma mul_monotone_typed : Typed ε mul_monotone (statement FS.mul_monotone).
Proof. RkCheck.certify_with 4096. Qed.
Lemma add_strict_monotone_typed : Typed ε add_strict_monotone (statement FS.addition_strict_monotone).
Proof. RkCheck.certify_with 4096. Qed.
Lemma mul_strict_monotone_typed : Typed ε mul_strict_monotone (statement FS.multiplication_strict_monotone).
Proof. RkCheck.certify_with 4096. Qed.
Lemma successor_add_one_typed : Typed ε successor_add_one (statement FS.successor_add_one).
Proof. RkCheck.certify_with 4096. Qed.

Theorem rig_axioms_realized A : In A FS.rig_laws -> Realizes (statement A).
Proof.
  unfold FS.rig_laws. intro HA.
  repeat (destruct HA as [<-|HA]; [eexists; first
    [exact add_commutative_typed |exact mul_commutative_typed
    |exact add_associative_typed |exact mul_associative_typed
    |exact add_zero_typed |exact mul_zero_typed |exact mul_one_typed
    |exact distributivity_typed |exact additive_cancellation_typed
    |exact order_refl_typed |exact order_trans_typed |exact order_antisym_typed
    |exact zero_least_typed |exact nontrivial_typed
    |exact add_monotone_typed |exact mul_monotone_typed
    |exact add_strict_monotone_typed |exact mul_strict_monotone_typed
    |exact successor_add_one_typed] |]).
  contradiction.
Qed.

Lemma formula_disj {k n} xs (env : Fin k -> Term nat n) :
  formula (FS.disj xs) env = FlatOr (map (fun A => formula A env) xs).
Proof.
  induction xs; cbn [FS.disj fold_right map FlatOr]; [reflexivity |].
  change (Arrow (Neg (formula a env)) (formula (FS.disj xs) env) =
    Arrow (Neg (formula a env)) (FlatOr (map (fun A => formula A env) xs))).
  rewrite IHxs. reflexivity.
Qed.
Lemma formula_bounded {k n} cutoff t (env : Fin k -> Term nat n) :
  formula (FS.disj (map (fun i => FS.equal t (FS.numeral i)) (seq 0 (S cutoff)))) env =
  BoundedCases.Bounded cutoff (term env t).
Proof.
  rewrite formula_disj. unfold BoundedCases.Bounded, FiniteCuts.atoms.
  rewrite map_map. f_equal. apply map_ext. intro i. cbn [formula].
  rewrite numeral_translation. reflexivity.
Qed.

Lemma bound_implication {n} (Γ : Ctx nat n) cutoff d :
  Typed Γ d (lift_closed Model.Domain) -> inhabited Γ (Model.admitted d) ->
  inhabited Γ (Arrow (Model.O d (lift_closed (Model.numeral cutoff)))
    (BoundedCases.Bounded cutoff d)).
Proof.
  intros Hd Hg. apply arrow_intro.
  - exists 15. apply Model.order_in_context; [exact Hd |apply lift_closed_typed, Unary.numeral_typed].
  - rewrite BoundedCases.shift_bounded. apply BoundedCases.order_to_bounded.
    + rewrite lift_closed_shift. apply weakening. exact Hd.
    + pose proof (inhabited_shift _ _ (Model.O d (lift_closed (Model.numeral cutoff))) Hg) as HG.
      change (inhabited (Γ & Model.O d (lift_closed (Model.numeral cutoff)))
        (shift (FiniteCuts.G 15 d))) in HG.
      rewrite BoundedCases.shift_G in HG. exact HG.
    + pose proof (newest Γ (Model.O d (lift_closed (Model.numeral cutoff)))) as HO.
      change (inhabited (Γ & Model.O d (lift_closed (Model.numeral cutoff)))
        (shift (OrderCuts.O d (lift_closed (Unary.numeral cutoff))))) in HO.
      rewrite OrderCuts.shift_O, <- lift_closed_shift in HO. exact HO.
Qed.

Theorem bounded_realized cutoff : Realizes (sentence (FS.bounded cutoff)).
Proof.
  unfold sentence, FS.bounded. apply universal_introduction.
  cbn [formula]. rewrite formula_bounded, numeral_translation.
  apply bound_implication.
  - exact (tV _ (fsucc fzero)).
  - exact (newest (ε & lift_closed Model.Domain) (Model.admitted V0)).
Qed.
Theorem comparison_realized cutoff : Realizes (sentence (FS.comparison cutoff)).
Proof.
  unfold sentence, FS.comparison. apply universal_introduction.
  rewrite formula_disj. cbn [map formula]. rewrite !numeral_translation.
  apply BoundedCases.comparison_in_context.
  - exact (tV _ (fsucc fzero)).
  - exact (newest (ε & lift_closed Model.Domain) (Model.admitted V0)).
Qed.

Theorem r_axioms_realized A : FS.r_axiom A -> Realizes (sentence A).
Proof.
  intro HA. destruct HA.
  - unfold sentence. cbn [formula term]. rewrite !numeral_translation, !lift_closed_zero.
    exact (GroundFaithfulness.ground_addition_true m n (m+n) eq_refl).
  - unfold sentence. cbn [formula term]. rewrite !numeral_translation, !lift_closed_zero.
    exact (GroundFaithfulness.ground_multiplication_true m n (m*n) eq_refl).
  - unfold sentence. cbn [FS.neg formula]. rewrite !numeral_translation.
    match goal with Hne : m <> n |- _ =>
      exact (OrderNumerals.numeral_inequality ε m n Hne) end.
  - apply bounded_realized.
  - apply comparison_realized.
Qed.

Lemma formula_iff {k n} A B (env : Fin k -> Term nat n) :
  formula (FS.iff A B) env =
  UnaryBounded.Equivalence (formula A env) (formula B env).
Proof. reflexivity. Qed.
Lemma formula_lt {k n} d e (env : Fin k -> Term nat n) :
  formula (FS.lt d e) env =
  Conj (OrderCuts.O (term env d) (term env e))
    (Neg (FiniteCuts.E (term env d) (term env e))).
Proof. reflexivity. Qed.
Lemma strict_bounded_translation cutoff :
  StrictBounded.strict_bounded_type cutoff =ᵝ sentence (FS.strict_bounded cutoff).
Proof.
  unfold StrictBounded.strict_bounded_type, sentence, FS.strict_bounded.
  cbn [formula]. rewrite formula_iff, formula_lt, formula_disj, map_map.
  rewrite numeral_translation.
  assert (Hmap : map (fun i => formula (FS.equal FS.x0 (FS.numeral i))
    (transpose empty_env)) (seq 0 cutoff) = StrictBounded.below_atoms cutoff V0).
  { unfold StrictBounded.below_atoms. apply map_ext. intro i.
    cbn [formula]. rewrite numeral_translation. reflexivity. }
  rewrite Hmap. change
    (Π Unary.Domain (Arrow (FiniteCuts.G 15 V0)
      (StrictBounded.StrictBoundEquivalence cutoff V0)) =ᵝ
     Π Unary.Domain (Arrow (FiniteCuts.G 15 V0)
      (UnaryBounded.Equivalence
        (Conj (OrderCuts.O V0 (lift_closed (Unary.numeral cutoff)))
          (Neg (FiniteCuts.E V0 (lift_closed (Unary.numeral cutoff)))))
        (StrictBounded.Below cutoff V0)))).
  apply beta_pi; [reflexivity |]. apply arrow_beta; [reflexivity |].
  unfold StrictBounded.StrictBoundEquivalence, UnaryBounded.Equivalence, Conj, Neg.
  repeat apply arrow_beta; try reflexivity; apply StrictBounded.strict_beta.
Qed.
Theorem strict_bounded_realized cutoff : Realizes (sentence (FS.strict_bounded cutoff)).
Proof.
  eapply FiniteUp.inhabited_conversion.
  - exact (StrictBounded.strict_bounded_realized cutoff).
  - apply formula_typed. intro i. exact (match i with end).
  - apply strict_bounded_translation.
Qed.
Theorem all_axioms_realized A : FS.axiom A -> Realizes (sentence A).
Proof.
  intro HA. destruct HA as [A HA |A HA |cutoff].
  - exact (r_axioms_realized A HA).
  - exact (rig_axioms_realized A HA).
  - exact (strict_bounded_realized cutoff).
Qed.

Print Assumptions rig_axioms_realized.
Print Assumptions r_axioms_realized.
Print Assumptions strict_bounded_realized.
Print Assumptions all_axioms_realized.
End FunctionalAxioms.
