(** Harmonized manuscript, theorem [main] (Theorem 4): the unary relational
    interpretation. This is separate from the functional Theorem5Target. *)
From Stdlib Require Import Lists.List Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DirectRCodes DirectRKernel
  DirectRUnary DirectRRelationalSyntax DirectRRelationalTranslation
  DirectRRelationalAxioms DirectRRelationalGround DirectRRelationalDeduction
  DirectRRelationalCountermodel.
Import ListNotations.
Module Theorem4.
Import Codes Core RelationalTranslation.

Inductive ground_atom :=
| equality_atom (t u : Relational.term 0)
| order_atom (t u : Relational.term 0)
| addition_atom (t u v : Relational.term 0)
| multiplication_atom (t u v : Relational.term 0).
Definition atom_formula a : Relational.formula 0 :=
  match a with
  | equality_atom t u => Relational.equal t u
  | order_atom t u => Relational.less_equal t u
  | addition_atom t u v => Relational.add_graph t u v
  | multiplication_atom t u v => Relational.mul_graph t u v
  end.
Definition atom_truth a : Prop :=
  match a with
  | equality_atom t u => value t = value u
  | order_atom t u => value t <= value u
  | addition_atom t u v => value t + value u = value v
  | multiplication_atom t u v => value t * value u = value v
  end.
Theorem ground_correctness a :
  (atom_truth a -> Realizes (sentence (atom_formula a))) /\
  (~ atom_truth a -> Realizes (Neg (sentence (atom_formula a)))).
Proof.
  destruct a; split; cbn [atom_truth atom_formula].
  - apply RelationalGround.equality_true.
  - apply RelationalGround.equality_false.
  - apply RelationalGround.order_true.
  - intro H. apply RelationalGround.order_false. lia.
  - apply RelationalGround.addition_true.
  - apply RelationalGround.addition_false.
  - apply RelationalGround.multiplication_true.
  - apply RelationalGround.multiplication_false.
Qed.
Theorem nonfaithfulness : exists A : Relational.formula 0,
  Realizes (sentence A) /\ ~ Relational.derives [] A.
Proof.
  exists RelationalCountermodel.order_reflexivity_sentence. split.
  - exists Unary.admitted_order_reflexivity. exact Unary.rho_realized.
  - exact RelationalCountermodel.order_reflexivity_underivable.
Qed.

(** Each conclusion concerns the fixed structural translation and the original
    typing judgment. No certificate record or preservation premise is assumed. *)
Theorem theorem4 :
  (forall A : Relational.formula 0, Relational.axiom A ->
    exists p, @typ nat RankSorts 0 ε p (sentence A)) /\
  (forall A : Relational.formula 0, Relational.derives [] A ->
    exists p, @typ nat RankSorts 0 ε p (sentence A)) /\
  (forall a, (atom_truth a -> exists p, @typ nat RankSorts 0 ε p (sentence (atom_formula a))) /\
    (~ atom_truth a -> exists p, @typ nat RankSorts 0 ε p (Neg (sentence (atom_formula a))))) /\
  (exists A : Relational.formula 0,
    (exists p, @typ nat RankSorts 0 ε p (sentence A)) /\ ~ Relational.derives [] A).
Proof.
  split; [intros A HA; exact (RelationalAxioms.source_axiom_realized ε empty_env A HA) |].
  split; [exact RelationalDeduction.sentence_preservation |].
  split; [exact ground_correctness |exact nonfaithfulness].
Qed.
End Theorem4.
