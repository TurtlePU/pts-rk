(** Harmonized manuscript, thm:direct-R (Theorem 7). All conclusions use
    the original annotated PTS and independent functional source deduction. *)
From Stdlib Require Import Lists.List Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRKernel DirectRStructural DirectRLogic DirectRWitnessSearch.
From Interpretation_of_R.functional Require Import DirectRCodes DirectRProofs DirectRFirstOrder
  DirectRFunctionalSyntax DirectRFunctionalTerms DirectRFunctionalSeparation
  DirectRFunctionalBounded DirectRFunctionalFormulaLogic DirectRFunctionalAxioms
  DirectRFunctionalSourceAxioms DirectRFunctionalDeduction DirectRFunctionalCountermodel.
Import ListNotations.
Module Theorem7.
Import Codes Core Structural NegativeLogic FirstOrder.
Inductive ground_atom :=
| equality_atom (t u : FirstOrder.term 0)
| order_atom (t u : FirstOrder.term 0).
Definition atom_formula a : FirstOrder.formula 0 :=
  match a with equality_atom t u => equal t u | order_atom t u => less_equal t u end.
Definition atom_truth a : Prop :=
  match a with
  | equality_atom t u => FunctionalTerms.value t = FunctionalTerms.value u
  | order_atom t u => FunctionalTerms.value t <= FunctionalTerms.value u
  end.
Theorem ground_correctness a :
  (atom_truth a -> Realizes (sentence_translation (atom_formula a))) /\
  (~ atom_truth a -> Realizes (Neg (sentence_translation (atom_formula a)))).
Proof.
  destruct a; split; cbn [atom_truth atom_formula].
  - apply FunctionalTerms.ground_equality_true.
  - apply FunctionalSeparation.ground_equality_false.
  - apply FunctionalTerms.ground_order_true.
  - intro H. apply FunctionalSeparation.ground_order_false. lia.
Qed.
Theorem order_reflexivity_realized :
  Realizes (sentence_translation FunctionalCountermodel.order_reflexivity_sentence).
Proof.
  unfold sentence_translation, FunctionalCountermodel.order_reflexivity_sentence.
  apply FunctionalFormulaLogic.universal_introduction.
  cbn [translate_formula translate_term FirstOrder.extend fin_match].
  apply FunctionalBounded.order_reflexivity.
  - exact (tV (ε & Domain & GoodAt V0) (fsucc fzero)).
  - apply FunctionalTerms.admitted_observed.
    + exact (tV (ε & Domain & GoodAt V0) (fsucc fzero)).
    + exact (newest (ε & Domain) (GoodAt V0)).
Qed.
Theorem nonfaithfulness : exists A : FirstOrder.formula 0,
  Realizes (sentence_translation A) /\ ~ FunctionalSyntax.derives [] A.
Proof.
  exists FunctionalCountermodel.order_reflexivity_sentence. split.
  - exact order_reflexivity_realized.
  - exact FunctionalCountermodel.order_reflexivity_underivable.
Qed.
(** Transparent effective interfaces. The certificate enumeration is intentionally
    exhaustive, not an efficient replacement for the native checker. Its
    termination follows from the proved all-index existence/preservation. *)
Definition effective_axiom a : {p : Term nat 0 | @typ nat RankSorts 0 ε p (axiom_type a)} :=
  WitnessSearch.witness (axiom_type a) (FunctionalAxioms.all_axioms_realized a).
Definition theorem5_target : Kernel.Theorem5Target :=
  {| Kernel.axiom_witness := fun a => proj1_sig (effective_axiom a);
     Kernel.axiom_witness_typed := fun a => proj2_sig (effective_axiom a) |}.
Definition effective_source_axiom A (H : FunctionalSyntax.axiom A) :
  {p : Term nat 0 | @typ nat RankSorts 0 ε p (sentence_translation A)} :=
  WitnessSearch.witness (sentence_translation A)
    (FunctionalSourceAxioms.source_axiom_realized ε FunctionalTerms.empty_env A H).
Definition effective_deduction A (H : FunctionalSyntax.derives [] A) :
  {p : Term nat 0 | @typ nat RankSorts 0 ε p (sentence_translation A)} :=
  WitnessSearch.witness (sentence_translation A) (FunctionalDeduction.sentence_preservation A H).
Definition effective_ground_true a (H : atom_truth a) :
  {p : Term nat 0 | @typ nat RankSorts 0 ε p (sentence_translation (atom_formula a))} :=
  WitnessSearch.witness _ (proj1 (ground_correctness a) H).
Definition effective_ground_false a (H : ~ atom_truth a) :
  {p : Term nat 0 | @typ nat RankSorts 0 ε p (Neg (sentence_translation (atom_formula a)))} :=
  WitnessSearch.witness _ (proj2 (ground_correctness a) H).

Theorem theorem7 :
  (forall A : FirstOrder.formula 0, FunctionalSyntax.axiom A ->
    exists p, @typ nat RankSorts 0 ε p (sentence_translation A)) /\
  (forall A : FirstOrder.formula 0, FunctionalSyntax.derives [] A ->
    exists p, @typ nat RankSorts 0 ε p (sentence_translation A)) /\
  (forall a, (atom_truth a -> exists p, @typ nat RankSorts 0 ε p (sentence_translation (atom_formula a))) /\
    (~ atom_truth a -> exists p, @typ nat RankSorts 0 ε p (Neg (sentence_translation (atom_formula a))))) /\
  (exists A : FirstOrder.formula 0,
    (exists p, @typ nat RankSorts 0 ε p (sentence_translation A)) /\ ~ FunctionalSyntax.derives [] A).
Proof.
  split; [intros A HA; exact (FunctionalSourceAxioms.source_axiom_realized ε FunctionalTerms.empty_env A HA) |].
  split; [exact FunctionalDeduction.sentence_preservation |].
  split; [exact ground_correctness |exact nonfaithfulness].
Qed.
End Theorem7.
