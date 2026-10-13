(** Relational arithmetic schemes, with an arbitrary third argument. *)
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRStructural
  DirectRLogic DirectRFiniteUp.
From Interpretation_of_R.relational Require Import DirectRUnary DirectRUnaryAxioms
  DirectRUnaryBounded DirectRUnaryEvaluation DirectRSeparation.
Module UnaryArithmetic.
Import CommonCodes Core Structural NegativeLogic FiniteUp Unary UnaryAxioms UnaryBounded UnaryEvaluation.

Definition GraphEquivalence {n} (l r : closed_term) (d : Term nat n) :=
  Equivalence (E (lift_closed l) d) (E (lift_closed r) d).
Lemma shift_graph_equivalence {n} l r (d : Term nat n) :
  shift (GraphEquivalence l r d) = GraphEquivalence l r (shift d).
Proof.
  unfold GraphEquivalence, Equivalence, Conj, Neg.
  rewrite !shift_arrow, !shift_E, <- !lift_closed_shift. reflexivity.
Qed.
Lemma graph_equivalence_in_context {n} (Γ : Ctx nat n) l r d :
  Typed ε l Unary.Domain -> Typed ε r Unary.Domain ->
  Typed Γ d (lift_closed Unary.Domain) -> l =ᵝ r -> inhabited Γ (GraphEquivalence l r d).
Proof.
  intros Hl Hr Hd Heq.
  pose proof (equality_in_context Γ _ _ (lift_closed_typed Γ _ _ Hl) Hd) as HA.
  pose proof (equality_in_context Γ _ _ (lift_closed_typed Γ _ _ Hr) Hd) as HB.
  assert (HAB : E (lift_closed l) d =ᵝ E (lift_closed r) d).
  { apply beta_app; [|reflexivity]. apply beta_app; [reflexivity |].
    apply rename_equiv. exact Heq. }
  apply equivalence_intro; [exists 5; exact HA |exists 5; exact HB | |].
  - eapply inhabited_conversion.
    + apply identity_inhabited. exists 5. exact HA.
    + exact (arrow_formation Γ _ _ _ _ HA HB).
    + apply arrow_beta; [reflexivity |exact HAB].
  - eapply inhabited_conversion.
    + apply identity_inhabited. exists 5. exact HB.
    + exact (arrow_formation Γ _ _ _ _ HB HA).
    + apply arrow_beta; [reflexivity |symmetry; exact HAB].
Qed.
Definition equation_scheme l r : closed_term :=
  Π Unary.Domain (Arrow (admitted V0) (GraphEquivalence l r V0)).
Theorem equation_scheme_realized l r :
  Typed ε l Unary.Domain -> Typed ε r Unary.Domain -> l =ᵝ r -> Realizes (equation_scheme l r).
Proof.
  intros Hl Hr Heq.
  assert (Hd : Typed (ε & Unary.Domain) V0 (lift_closed Unary.Domain))
    by exact (tV (ε & Unary.Domain) fzero).
  assert (H : inhabited (ε & Unary.Domain) (Arrow (admitted V0) (GraphEquivalence l r V0))).
  { apply arrow_intro.
    - exists 12. apply admitted_formation_in_context. exact Hd.
    - rewrite shift_graph_equivalence. apply graph_equivalence_in_context; auto.
      rewrite lift_closed_shift. exact (weakening RankSorts _ _ (admitted V0) Hd). }
  destruct H as [p Hp]. exists (lam Unary.Domain p). exact (tLam Unary.domain_formation Hp).
Qed.
Definition R1 m n := equation_scheme
  (app (app Unary.addition (Unary.numeral m)) (Unary.numeral n)) (Unary.numeral (m+n)).
Definition R2 m n := equation_scheme
  (app (app Unary.multiplication (Unary.numeral m)) (Unary.numeral n)) (Unary.numeral (m*n)).
Theorem R1_realized m n : Realizes (R1 m n).
Proof.
  apply equation_scheme_realized; [|apply Unary.numeral_typed |apply addition_numerals].
  eapply arrow_application; [|apply Unary.numeral_typed].
  eapply arrow_application; [apply Unary.addition_typed |apply Unary.numeral_typed].
Qed.
Theorem R2_realized m n : Realizes (R2 m n).
Proof.
  apply equation_scheme_realized; [|apply Unary.numeral_typed |apply multiplication_numerals].
  eapply arrow_application; [|apply Unary.numeral_typed].
  eapply arrow_application; [apply Unary.multiplication_typed |apply Unary.numeral_typed].
Qed.
Lemma ground_equation l v k : Typed ε l Unary.Domain -> l =ᵝ Unary.numeral v -> v = k ->
  Realizes (E l (Unary.numeral k)).
Proof.
  intros Hl Heq <-. eapply inhabited_conversion.
  - exists (app equality_reflexivity (Unary.numeral v)).
    apply equality_reflexivity_application, Unary.numeral_typed.
  - apply equality_in_context; rewrite lift_closed_zero; auto using Unary.numeral_typed.
  - apply beta_app; [|reflexivity]. apply beta_app; [reflexivity |symmetry; exact Heq].
Qed.
Lemma ground_inequation l v k : Typed ε l Unary.Domain -> l =ᵝ Unary.numeral v -> v <> k ->
  Realizes (Neg (E l (Unary.numeral k))).
Proof.
  intros Hl Heq Hneq. eapply inhabited_conversion; [apply Separation.R3_realized; exact Hneq | |].
  - apply neg_formation, equality_in_context; rewrite lift_closed_zero; auto using Unary.numeral_typed.
  - apply neg_beta, beta_app; [|reflexivity]. apply beta_app; [reflexivity |symmetry; exact Heq].
Qed.
Definition AddAtom m n k := E
  (app (app Unary.addition (Unary.numeral m)) (Unary.numeral n)) (Unary.numeral k).
Definition MulAtom m n k := E
  (app (app Unary.multiplication (Unary.numeral m)) (Unary.numeral n)) (Unary.numeral k).
Lemma addition_result_typed m n :
  Typed ε (app (app Unary.addition (Unary.numeral m)) (Unary.numeral n)) Unary.Domain.
Proof.
  eapply arrow_application; [|apply Unary.numeral_typed].
  eapply arrow_application; [apply Unary.addition_typed |apply Unary.numeral_typed].
Qed.
Lemma multiplication_result_typed m n :
  Typed ε (app (app Unary.multiplication (Unary.numeral m)) (Unary.numeral n)) Unary.Domain.
Proof.
  eapply arrow_application; [|apply Unary.numeral_typed].
  eapply arrow_application; [apply Unary.multiplication_typed |apply Unary.numeral_typed].
Qed.
Theorem ground_addition_true m n k : m+n=k -> Realizes (AddAtom m n k).
Proof. apply (ground_equation _ (m+n)); auto using addition_result_typed, addition_numerals. Qed.
Theorem ground_addition_false m n k : m+n<>k -> Realizes (Neg (AddAtom m n k)).
Proof. apply (ground_inequation _ (m+n)); auto using addition_result_typed, addition_numerals. Qed.
Theorem ground_multiplication_true m n k : m*n=k -> Realizes (MulAtom m n k).
Proof. apply (ground_equation _ (m*n)); auto using multiplication_result_typed, multiplication_numerals. Qed.
Theorem ground_multiplication_false m n k : m*n<>k -> Realizes (Neg (MulAtom m n k)).
Proof. apply (ground_inequation _ (m*n)); auto using multiplication_result_typed, multiplication_numerals. Qed.

(** All five schemes, not a preservation theorem for source deductions. *)
Inductive relational_axiom : Type :=
| ax_add (m n : nat)
| ax_mul (m n : nat)
| ax_neq (m n : nat) (distinct : m <> n)
| ax_bound (n : nat)
| ax_compare (n : nat).
Definition axiom_translation a : closed_term :=
  match a with
  | ax_add m n => R1 m n
  | ax_mul m n => R2 m n
  | ax_neq m n _ => Neg (E (Unary.numeral m) (Unary.numeral n))
  | ax_bound n => UnaryBounded.R4 n
  | ax_compare n => UnaryAxioms.R5 n
  end.
Theorem all_axioms_realized a : Realizes (axiom_translation a).
Proof.
  destruct a; cbn [axiom_translation]; auto using R1_realized, R2_realized,
    Separation.R3_realized, UnaryBounded.R4_realized, UnaryAxioms.R5_realized.
Qed.
End UnaryArithmetic.
