(** Uniform ground calculations and the remaining interpretation target. *)
From Stdlib Require Import Arith.PeanoNat Lia Lists.List Bool.Bool.
From PTSrk Require Import Syntax AbstractRewriting Congruence Reduction DefEq Context Typing Ranks.
From Interpretation_of_R.functional Require Import DirectRCodes DirectRFoundations.
Import ListNotations.

Module Kernel.
Import Codes.
Include Foundations.

Fixpoint ground_add_proof (m n : nat) {struct m} : closed_term :=
  match m with
  | 0 => apps Law_add_zero [numeral n; observed_numeral n]
  | S k =>
    let x := numeral k in let y := numeral n in
    let gx := observed_numeral k in let gy := observed_numeral n in
    let xy := dA x y in let gxy := gA x y gx gy in
    let lhs := dA (dS x) y in
    let mid := dS xy in
    let rhs := numeral (S (k+n)) in
    eT lhs mid rhs (gA (dS x) y (gS x gx) gy) (gS xy gxy)
      (gS (numeral (k+n)) (observed_numeral (k+n)))
      (apps Law_add_succ [x;gx;y;gy])
      (eSucc xy (numeral (k+n)) gxy (observed_numeral (k+n))
             (ground_add_proof k n))
  end.



Lemma ground_add_typed m n : Typed ε (ground_add_proof m n) (R1 m n).
Proof.
  induction m as [|m IH].
  - pose proof (numeral_typed n) as Hn.
    pose proof (observed_numeral_typed n) as Gn.
    change (Typed ε (apps Law_add_zero [numeral n; observed_numeral n])
      (EqAt (dA zero (numeral n)) (numeral n))).
    apply ground_add_zero_application; assumption.
  - pose proof (numeral_typed m) as Hm.
    pose proof (numeral_typed n) as Hn.
    pose proof (numeral_typed (m+n)) as Hmn.
    pose proof (observed_numeral_typed m) as Gm.
    pose proof (observed_numeral_typed n) as Gn.
    pose proof (observed_numeral_typed (m+n)) as Gmn.
    cbn [ground_add_proof]. apply equality_transitivity_application;
      eauto 8 using domain_successor_application, domain_addition_application,
        observed_successor_application, observed_addition_application,
        numeral_typed, observed_numeral_typed, addition_successor_application,
        successor_congruence_application.
Qed.

Fixpoint ground_mul_proof (m n : nat) {struct m} : closed_term :=
  match m with
  | 0 => apps Law_mul_zero [numeral n; observed_numeral n]
  | S k =>
    let x := numeral k in let y := numeral n in
    let gx := observed_numeral k in let gy := observed_numeral n in
    let xy := dM x y in let gxy := gM x y gx gy in
    let lhs := dM (dS x) y in
    let mid := dA y xy in
    let mid' := dA y (numeral (k*n)) in
    let rhs := numeral (n+k*n) in
    let grhs := observed_numeral (n+k*n) in
    eT lhs mid rhs (gM (dS x) y (gS x gx) gy) (gA y xy gy gxy) grhs
      (apps Law_mul_succ [x;gx;y;gy])
      (eT mid mid' rhs (gA y xy gy gxy)
        (gA y (numeral (k*n)) gy (observed_numeral (k*n))) grhs
        (eAdd y y xy (numeral (k*n)) gy gy gxy (observed_numeral (k*n))
           (eR y gy) (ground_mul_proof k n))
        (ground_add_proof n (k*n)))
  end.

Lemma ground_mul_typed m n : Typed ε (ground_mul_proof m n) (R2 m n).
Proof.
  induction m as [|m IH].
  - pose proof (numeral_typed n) as Hn.
    pose proof (observed_numeral_typed n) as Gn.
    change (Typed ε (apps Law_mul_zero [numeral n; observed_numeral n])
      (EqAt (dM zero (numeral n)) zero)).
    apply ground_mul_zero_application; assumption.
  - pose proof (numeral_typed m) as Hm.
    pose proof (numeral_typed n) as Hn.
    pose proof (numeral_typed (m*n)) as Hmn.
    pose proof (numeral_typed (n+m*n)) as Hsum.
    pose proof (observed_numeral_typed m) as Gm.
    pose proof (observed_numeral_typed n) as Gn.
    pose proof (observed_numeral_typed (m*n)) as Gmn.
    pose proof (observed_numeral_typed (n+m*n)) as Gsum.
    pose proof (ground_add_typed n (m*n)) as Hcalc.
    cbn [ground_mul_proof]. apply equality_transitivity_application.
    1-6: solve [eauto 8 using domain_successor_application, domain_addition_application,
      domain_multiplication_application, observed_successor_application,
      observed_addition_application, observed_multiplication_application,
      numeral_typed, observed_numeral_typed].
    + apply multiplication_successor_application; assumption.
    + apply equality_transitivity_application.
      1-6: solve [eauto 8 using domain_addition_application,
        domain_multiplication_application, observed_addition_application,
        observed_multiplication_application, numeral_typed, observed_numeral_typed].
      * apply addition_congruence_application.
        1-8: solve [eauto using domain_multiplication_application,
          observed_multiplication_application].
        -- apply equality_reflexivity_application; assumption.
        -- exact IH.
      * exact Hcalc.
Qed.

Fixpoint ground_order_proof (i j : nat) {struct j} : closed_term :=
  match j with
  | 0 => lR zero g_zero_proof
  | S k =>
    if Nat.eqb i (S k) then lR (numeral i) (observed_numeral i)
    else lT (numeral i) (numeral k) (numeral (S k))
       (observed_numeral i) (observed_numeral k)
       (gS (numeral k) (observed_numeral k))
       (ground_order_proof i k) (lSucc (numeral k) (observed_numeral k))
  end.
Lemma ground_order_typed i j : i <= j ->
  Typed ε (ground_order_proof i j) (LeAt (numeral i) (numeral j)).
Proof.
  revert i. induction j as [|j IH]; intros i H.
  - assert (i=0) by lia. subst i. cbn [ground_order_proof].
    apply order_reflexivity_application; [exact zero_typed | exact observed_zero_typed].
  - cbn [ground_order_proof]. destruct (Nat.eqb i (S j)) eqn:E.
    + apply Nat.eqb_eq in E. subst i.
      pose proof (numeral_typed (S j)) as Hj.
      pose proof (observed_numeral_typed (S j)) as Gj.
      apply order_reflexivity_application; assumption.
    + assert (Hi : i <= j) by (apply Nat.eqb_neq in E; lia).
      pose proof (IH i Hi) as Hp.
      pose proof (numeral_typed i) as Hi'.
      pose proof (numeral_typed j) as Hj.
      pose proof (observed_numeral_typed i) as Gi.
      pose proof (observed_numeral_typed j) as Gj.
      apply order_transitivity_application;
        eauto using numeral_typed, observed_numeral_typed,
          observed_successor_application, order_successor_application.
Qed.

Theorem R1_realized m n : Realizes (R1 m n).
Proof. exists (ground_add_proof m n). apply ground_add_typed. Qed.
Theorem R2_realized m n : Realizes (R2 m n).
Proof. exists (ground_mul_proof m n). apply ground_mul_typed. Qed.

(** Explicit target for the remaining uniform theorem.  No inhabitant of
    this record is postulated.  The generator and tests below are separate. *)
Record Theorem5Target : Type := {
  axiom_witness : axiom_instance -> closed_term;
  axiom_witness_typed : forall a,
    Typed ε (axiom_witness a) (axiom_type a)
}.

End Kernel.
