(** Realization of the independently stated relational rig axioms. The
    source graphs use reversed Church arguments, as in the supplied draft. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRCheck.
From Interpretation_of_R.relational Require Import DirectRRelationalSyntax.
From OrderedSemiring Require Import RigCodes DomainClosure ObservationEquality
  ArithmeticCongruence SemiringLaws Cancellation NaturalOrder OrderLaws Graphs
  Source FirstOrderTranslation.
Import ListNotations.
Module RigAxiomRealization.
Import CommonCodes Core ObservationEquality ArithmeticCongruence SemiringLaws.
Definition X i := NVar (600+i).
Definition G15 i := NVar (700+i).
Definition G7 i := napps (NClosed (RigCodes.lowering 15 7)) [X i;G15 i].
Definition G11 i := napps (NClosed (RigCodes.lowering 15 11)) [X i;G15 i].
Definition fields n := flat_map (fun i =>
  [(600+i,nD);(700+i,NApp (RigCodes.nGood 15) (X i))]) (seq 0 n).
Definition eqarg i a b := (800+i,nEq a b).
Definition H i := NVar (800+i).
Definition statement := FirstOrderTranslation.sentence.

Definition add_total := Graphs.addition_totality.
Definition mul_total := Graphs.multiplication_totality.
Lemma add_total_typed : Typed ε add_total (statement (Source.graph_total (@Relational.add_graph))).
Proof. RkCheck.certify_with 4096. Qed.
Lemma mul_total_typed : Typed ε mul_total (statement (Source.graph_total (@Relational.mul_graph))).
Proof. RkCheck.certify_with 4096. Qed.

Definition unique_fields (op : named -> named -> named) := fields 4 ++
  [eqarg 0 (op (X 1) (X 0)) (X 2);eqarg 1 (op (X 1) (X 0)) (X 3)].
Definition nUnique (op : named -> named -> named) := nlams (unique_fields op)
  (trans (X 2) (op (X 1) (X 0)) (X 3)
    (sym (op (X 1) (X 0)) (X 2) (H 0)) (H 1)).
Definition add_unique := close (nUnique add) eq_refl.
Definition mul_unique := close (nUnique mul) eq_refl.
Lemma add_unique_typed : Typed ε add_unique (statement (Source.graph_unique (@Relational.add_graph))).
Proof. RkCheck.certify_with 4096. Qed.
Lemma mul_unique_typed : Typed ε mul_unique (statement (Source.graph_unique (@Relational.mul_graph))).
Proof. RkCheck.certify_with 4096. Qed.

Definition add_commutative := close
  (nlams (fields 3 ++ [eqarg 0 (add (X 1) (X 0)) (X 2)])
    (trans (add (X 0) (X 1)) (add (X 1) (X 0)) (X 2)
      (add_comm (X 0) (X 1) (G7 0) (G7 1)) (H 0))) eq_refl.
Definition mul_commutative := close
  (nlams (fields 3 ++ [eqarg 0 (mul (X 1) (X 0)) (X 2)])
    (trans (mul (X 0) (X 1)) (mul (X 1) (X 0)) (X 2)
      (mul_comm (X 0) (X 1) (G11 0) (G11 1)) (H 0))) eq_refl.
Lemma add_commutative_typed : Typed ε add_commutative
  (statement (Source.graph_commutative (@Relational.add_graph))).
Proof. RkCheck.certify_with 4096. Qed.
Lemma mul_commutative_typed : Typed ε mul_commutative
  (statement (Source.graph_commutative (@Relational.mul_graph))).
Proof. RkCheck.certify_with 4096. Qed.

Definition assoc_fields (op : named -> named -> named) := fields 6 ++
  [eqarg 0 (op (X 1) (X 0)) (X 3);eqarg 1 (op (X 2) (X 3)) (X 5);
   eqarg 2 (op (X 2) (X 1)) (X 4)].
Definition nAssoc (op : named -> named -> named)
  (cf : named -> named -> named -> named -> named -> named)
  (cs : named -> named -> named -> named -> named -> named -> named) :=
  nlams (assoc_fields op)
    (trans (op (X 4) (X 0)) (op (X 2) (X 3)) (X 5)
      (trans (op (X 4) (X 0)) (op (op (X 2) (X 1)) (X 0)) (op (X 2) (X 3))
        (cf (X 4) (op (X 2) (X 1)) (X 0) (G7 0)
          (sym (op (X 2) (X 1)) (X 4) (H 2)))
        (cs (X 2) (op (X 1) (X 0)) (X 3) (G7 2) (G7 3) (H 0))) (H 1)).
Definition add_first_guarded x y z (_ : named) h := add_first x y z h.
Definition add_second_guarded x y z gx (_ : named) h := add_second x y z gx h.
Definition add_associative := close (nAssoc add add_first_guarded add_second_guarded) eq_refl.
Definition mul_associative := close (nAssoc mul mul_first mul_second) eq_refl.
Lemma add_associative_typed : Typed ε add_associative
  (statement (Source.graph_associative (@Relational.add_graph))).
Proof. RkCheck.certify_with 4096. Qed.
Lemma mul_associative_typed : Typed ε mul_associative
  (statement (Source.graph_associative (@Relational.mul_graph))).
Proof. RkCheck.certify_with 4096. Qed.

Definition add_zero := close (nlams (fields 1) (refl (X 0))) eq_refl.
Definition mul_zero := close (nlams (fields 1) (refl nZ)) eq_refl.
Definition mul_one := add_zero.
Lemma add_zero_typed : Typed ε add_zero (statement Source.add_zero).
Proof. RkCheck.certify_with 4096. Qed.
Lemma mul_zero_typed : Typed ε mul_zero (statement Source.mul_zero).
Proof. RkCheck.certify_with 4096. Qed.
Lemma mul_one_typed : Typed ε mul_one (statement Source.mul_one).
Proof. RkCheck.certify_with 4096. Qed.

Definition distributivity := close
  (nlams (fields 7 ++ [eqarg 0 (add (X 2) (X 1)) (X 3);
    eqarg 1 (mul (X 3) (X 0)) (X 4);
    eqarg 2 (mul (X 1) (X 0)) (X 5);eqarg 3 (mul (X 2) (X 0)) (X 6)])
    (trans (add (X 6) (X 5)) (mul (X 3) (X 0)) (X 4)
      (trans (add (X 6) (X 5)) (add (mul (X 2) (X 0)) (mul (X 1) (X 0)))
        (mul (X 3) (X 0))
        (trans (add (X 6) (X 5)) (add (X 6) (mul (X 1) (X 0)))
          (add (mul (X 2) (X 0)) (mul (X 1) (X 0)))
          (add_second (X 6) (X 5) (mul (X 1) (X 0)) (G7 6)
            (sym (mul (X 1) (X 0)) (X 5) (H 2)))
          (add_first (X 6) (mul (X 2) (X 0)) (mul (X 1) (X 0))
            (sym (mul (X 2) (X 0)) (X 6) (H 3))))
        (mul_first (add (X 2) (X 1)) (X 3) (X 0) (G7 0) (H 0))) (H 1))) eq_refl.
Lemma distributivity_typed : Typed ε distributivity (statement Source.distributivity).
Proof. RkCheck.certify_with 4096. Qed.

Definition additive_cancellation := close
  (nlams (fields 4 ++ [eqarg 0 (add (X 1) (X 0)) (X 3);
                      eqarg 1 (add (X 2) (X 0)) (X 3)])
    (Cancellation.cancel_left (X 0) (X 1) (X 2) (G11 0) (G7 1) (G7 2)
      (trans (add (X 0) (X 1)) (add (X 1) (X 0)) (add (X 0) (X 2))
        (add_comm (X 0) (X 1) (G7 0) (G7 1))
        (trans (add (X 1) (X 0)) (X 3) (add (X 0) (X 2)) (H 0)
          (trans (X 3) (add (X 2) (X 0)) (add (X 0) (X 2))
            (sym (add (X 2) (X 0)) (X 3) (H 1))
            (add_comm (X 2) (X 0) (G7 2) (G7 0))))))) eq_refl.
Lemma additive_cancellation_typed : Typed ε additive_cancellation (statement Source.additive_cancellation).
Proof. RkCheck.certify_with 4096. Qed.

Definition order_refl := close (nlams (fields 1)
  (NApp (NClosed NaturalOrder.reflexivity) (X 0))) eq_refl.
Definition order_trans := close
  (nlams (fields 3 ++ [(800,OrderLaws.ord (X 0) (X 1));(801,OrderLaws.ord (X 1) (X 2))])
    (OrderLaws.otrans (X 0) (X 1) (X 2) (H 0) (H 1))) eq_refl.
Definition order_antisym := close
  (nlams (fields 2 ++ [(800,OrderLaws.ord (X 0) (X 1));(801,OrderLaws.ord (X 1) (X 0))])
    (OrderLaws.antisym (X 0) (X 1) (G11 0) (G11 1) (H 0) (H 1))) eq_refl.
Definition zero_least := close (nlams (fields 1)
  (napps (NClosed NaturalOrder.zero_least) [X 0;G11 0])) eq_refl.
Definition nontrivial := close (NLam 800 (nEq nZ one)
  (Cancellation.nonzero nZ (NClosed (RigCodes.good_zero 7)) (sym nZ one (H 0)))) eq_refl.
Lemma order_refl_typed : Typed ε order_refl (statement Source.order_refl).
Proof. RkCheck.certify_with 4096. Qed.
Lemma order_trans_typed : Typed ε order_trans (statement Source.order_trans).
Proof. RkCheck.certify_with 4096. Qed.
Lemma order_antisym_typed : Typed ε order_antisym (statement Source.order_antisym).
Proof. RkCheck.certify_with 4096. Qed.
Lemma zero_least_typed : Typed ε zero_least (statement Source.zero_least).
Proof. RkCheck.certify_with 4096. Qed.
Lemma nontrivial_typed : Typed ε nontrivial (statement Source.nontrivial).
Proof. RkCheck.certify_with 4096. Qed.

Definition monotone_fields (op : named -> named -> named) rel := fields 5 ++
  [eqarg 0 (op (X 2) (X 0)) (X 3);eqarg 1 (op (X 2) (X 1)) (X 4);
   (802,rel (X 0) (X 1))].
Definition nMonotone op (mono : named) := nlams (monotone_fields op OrderLaws.ord)
  (OrderLaws.ocong (op (X 2) (X 0)) (X 3) (op (X 2) (X 1)) (X 4) (H 0) (H 1)
    (napps mono [X 0;X 1;X 2;G11 0;G11 1;G11 2;H 2])).
Definition add_monotone := close (nMonotone add (NClosed OrderLaws.addition_monotone_left)) eq_refl.
Definition mul_monotone := close (nMonotone mul (NClosed OrderLaws.multiplication_monotone_left)) eq_refl.
Lemma add_monotone_typed : Typed ε add_monotone (statement (Source.graph_monotone (@Relational.add_graph))).
Proof. RkCheck.certify_with 4096. Qed.
Lemma mul_monotone_typed : Typed ε mul_monotone (statement (Source.graph_monotone (@Relational.mul_graph))).
Proof. RkCheck.certify_with 4096. Qed.
Definition add_strict_monotone := close
  (nlams (monotone_fields add OrderLaws.strict)
    (OrderLaws.scong (add (X 2) (X 0)) (X 3) (add (X 2) (X 1)) (X 4) (H 0) (H 1)
      (napps (NClosed OrderLaws.addition_strict_monotone_left)
        [X 0;X 1;X 2;G11 0;G11 1;G11 2;H 2]))) eq_refl.
Definition mul_strict_monotone := close
  (nlams (monotone_fields mul OrderLaws.strict ++ [(803,OrderLaws.strict nZ (X 2))])
    (OrderLaws.scong (mul (X 2) (X 0)) (X 3) (mul (X 2) (X 1)) (X 4) (H 0) (H 1)
      (napps (NClosed OrderLaws.multiplication_strict_monotone_left)
        [X 0;X 1;X 2;G11 0;G11 1;G11 2;H 2;H 3]))) eq_refl.
Lemma add_strict_monotone_typed : Typed ε add_strict_monotone (statement Source.addition_strict_monotone).
Proof. RkCheck.certify_with 4096. Qed.
Lemma mul_strict_monotone_typed : Typed ε mul_strict_monotone (statement Source.multiplication_strict_monotone).
Proof. RkCheck.certify_with 4096. Qed.

Definition successor_add_one := close (nlams (fields 1) (refl (suc (X 0)))) eq_refl.
Lemma successor_add_one_typed : Typed ε successor_add_one (statement Source.successor_add_one).
Proof. RkCheck.certify_with 4096. Qed.

Theorem rig_axioms_realized A : In A Source.rig_laws -> Realizes (statement A).
Proof.
  unfold Source.rig_laws. intro H.
  repeat (destruct H as [<-|H]; [eexists; first [exact add_total_typed |exact mul_total_typed
    |exact add_unique_typed |exact mul_unique_typed |exact add_commutative_typed |exact mul_commutative_typed
    |exact add_associative_typed |exact mul_associative_typed |exact add_zero_typed |exact mul_zero_typed
    |exact mul_one_typed |exact distributivity_typed |exact additive_cancellation_typed
    |exact order_refl_typed |exact order_trans_typed |exact order_antisym_typed |exact zero_least_typed
    |exact nontrivial_typed |exact add_monotone_typed |exact mul_monotone_typed
    |exact add_strict_monotone_typed |exact mul_strict_monotone_typed
    |exact successor_add_one_typed] |]).
  contradiction.
Qed.
Print Assumptions rig_axioms_realized.
End RigAxiomRealization.
