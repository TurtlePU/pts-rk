(** Direct R interpretation -- restructured draft, 2026-10-13.
    Compiler-unchecked. See docs/DirectR.md for the exact verification status. *)

From Stdlib Require Import Arith.PeanoNat Lia Lists.List Bool.Bool.
From PTSrk Require Import Syntax AbstractRewriting Congruence Reduction
  DefEq Context Typing Ranks.
Import ListNotations.

From PTSrk Require Import DirectRCodes DirectRKernel DirectREval
  DirectRCheck DirectRSymbolic.

Module Kernel.
Import Codes.
Include Core.

(** For symbolic induction goals only. Fixed certificates below are checked
    using run_check_sound directly against the upstream typing judgment. *)
Ltac certify := Symbolic.certify.

Lemma bottom_formation : Typed ε Bottom (𝓤 1).
Proof. RkCheck.certify_with 4096. Qed.
Lemma top_formation : Typed ε Top (𝓤 1).
Proof. RkCheck.certify_with 4096. Qed.
Lemma top_inhabited : Typed ε top_proof Top.
Proof. RkCheck.certify_with 4096. Qed.
Lemma domain_formation : Typed ε Domain (𝓤 3).
Proof. RkCheck.certify_with 4096. Qed.
Lemma zero_typed : Typed ε zero Domain.
Proof. RkCheck.certify_with 4096. Qed.
Lemma successor_typed : Typed ε successor (Arrow Domain Domain).
Proof. RkCheck.certify_with 4096. Qed.
Lemma addition_typed : Typed ε addition (Arrow Domain (Arrow Domain Domain)).
Proof. RkCheck.certify_with 4096. Qed.
Lemma multiplication_typed : Typed ε multiplication (Arrow Domain (Arrow Domain Domain)).
Proof. RkCheck.certify_with 4096. Qed.
Lemma good_formation : Typed ε Good (Arrow Domain (𝓤 12)).
Proof. RkCheck.certify_with 4096. Qed.
Lemma equality_formation : Typed ε Equality (Arrow Domain (Arrow Domain (𝓤 6))).
Proof. RkCheck.certify_with 4096. Qed.
Lemma order_formation : Typed ε Order (Arrow Domain (Arrow Domain (𝓤 6))).
Proof. RkCheck.certify_with 4096. Qed.
Lemma observed_formation : Typed ε G (Arrow Domain (𝓤 6)).
Proof. RkCheck.certify_with 4096. Qed.
Lemma good_zero_typed : Typed ε good_zero_proof good_zero_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma good_successor_typed : Typed ε good_succ_proof good_succ_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma good_addition_typed : Typed ε good_add_proof (good_binary_type addition).
Proof. RkCheck.certify_with 4096. Qed.
Lemma good_multiplication_typed : Typed ε good_mul_proof (good_binary_type multiplication).
Proof. RkCheck.certify_with 4096. Qed.
Lemma observed_zero_typed : Typed ε g_zero_proof g_zero_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma observed_successor_typed : Typed ε g_succ_proof g_succ_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma observed_addition_typed : Typed ε g_add_proof (g_binary_type addition).
Proof. RkCheck.certify_with 4096. Qed.
Lemma observed_multiplication_typed : Typed ε g_mul_proof (g_binary_type multiplication).
Proof. RkCheck.certify_with 4096. Qed.
Lemma good_to_observed_typed : Typed ε good_to_g_proof good_to_g_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma equality_reflexivity_typed : Typed ε equality_refl_proof equality_refl_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma order_reflexivity_typed : Typed ε order_refl_proof order_refl_type.
Proof. RkCheck.certify_with 4096. Qed.

Lemma Law_eq_refl_typed : Typed ε Law_eq_refl Law_eq_reflType.
Proof. RkCheck.certify_with 4096. Qed.

Lemma Law_eq_sym_typed : Typed ε Law_eq_sym Law_eq_symType.
Proof. RkCheck.certify_with 4096. Qed.

Lemma Law_eq_trans_typed : Typed ε Law_eq_trans Law_eq_transType.
Proof. RkCheck.certify_with 4096. Qed.

Lemma Law_succ_congr_typed : Typed ε Law_succ_congr Law_succ_congrType.
Proof. RkCheck.certify_with 4096. Qed.

Lemma Law_add_congr_typed : Typed ε Law_add_congr Law_add_congrType.
Proof. RkCheck.certify_with 4096. Qed.

Lemma Law_mul_congr_typed : Typed ε Law_mul_congr Law_mul_congrType.
Proof. RkCheck.certify_with 4096. Qed.

Lemma Law_order_congr_typed : Typed ε Law_order_congr Law_order_congrType.
Proof. RkCheck.certify_with 4096. Qed.

Lemma Law_order_refl_typed : Typed ε Law_order_refl Law_order_reflType.
Proof. RkCheck.certify_with 4096. Qed.

Lemma Law_order_trans_typed : Typed ε Law_order_trans Law_order_transType.
Proof. RkCheck.certify_with 4096. Qed.

Lemma Law_add_zero_typed : Typed ε Law_add_zero Law_add_zeroType.
Proof. RkCheck.certify_with 4096. Qed.

Lemma Law_add_succ_typed : Typed ε Law_add_succ Law_add_succType.
Proof. RkCheck.certify_with 4096. Qed.

Lemma Law_mul_zero_typed : Typed ε Law_mul_zero Law_mul_zeroType.
Proof. RkCheck.certify_with 4096. Qed.

Lemma Law_mul_succ_typed : Typed ε Law_mul_succ Law_mul_succType.
Proof. RkCheck.certify_with 4096. Qed.

Lemma Law_mul_zero_right_typed : Typed ε Law_mul_zero_right Law_mul_zero_rightType.
Proof. RkCheck.certify_with 4096. Qed.

Lemma Law_le_succ_typed : Typed ε Law_le_succ Law_le_succType.
Proof. RkCheck.certify_with 4096. Qed.

Lemma Law_le_add_left_typed : Typed ε Law_le_add_left Law_le_add_leftType.
Proof. RkCheck.certify_with 4096. Qed.

Lemma Law_le_add_right_typed : Typed ε Law_le_add_right Law_le_add_rightType.
Proof. RkCheck.certify_with 4096. Qed.

Lemma Law_le_mul_left_typed : Typed ε Law_le_mul_left Law_le_mul_leftType.
Proof. RkCheck.certify_with 4096. Qed.

Lemma Law_le_mul_right_typed : Typed ε Law_le_mul_right Law_le_mul_rightType.
Proof. RkCheck.certify_with 4096. Qed.

(** These structural lemmas use only the source weakening/substitution API. *)
Lemma lift_closed_zero (t : closed_term) : @lift_closed 0 t = t.
Proof.
  unfold lift_closed.
  transitivity (rename (fun i => i) t).
  - apply rename_ext. intro i. exact (match i with end).
  - apply rename_id.
Qed.
Lemma lift_closed_shift {n} (t : closed_term) :
  @lift_closed (S n) t = shift (@lift_closed n t).
Proof.
  unfold lift_closed, shift. rewrite rename_comp.
  apply rename_ext. intro i. exact (match i with end).
Qed.
Lemma lift_closed_typed {n} (G : Ctx nat n) (t A : closed_term) :
  Typed ε t A -> Typed G (lift_closed t) (lift_closed A).
Proof.
  intro H. induction G.
  - rewrite !lift_closed_zero. exact H.
  - rewrite !lift_closed_shift. apply weakening. exact IHG.
Qed.
Lemma substitute_shift {n} (t u : Term nat n) : shift t ◁ u = t.
Proof.
  unfold subst, shift. rewrite replace_rename.
  change (replace (fun i => var i) t = t). apply replace_var.
Qed.
Lemma arrow_application {n} (G : Ctx nat n) (f u A B : Term nat n) :
  Typed G f (Arrow A B) -> Typed G u A -> Typed G (app f u) B.
Proof.
  intros H J. rewrite <- (substitute_shift B u).
  exact (tApp H J).
Qed.

(** Uniform ground calculations.  These are PTS witnesses, not calculations
    in a meta-level arithmetic observation. *)
Definition apps (f : closed_term) (xs : list closed_term) : closed_term :=
  fold_left (@app nat 0) xs f.
Definition dS x := app successor x.
Definition dA x y := apps addition [x;y].
Definition dM x y := apps multiplication [x;y].
Definition gS x gx := apps g_succ_proof [x;gx].
Definition gA x y gx gy := apps g_add_proof [x;y;gx;gy].
Definition gM x y gx gy := apps g_mul_proof [x;y;gx;gy].
Definition eR x gx := apps Law_eq_refl [x;gx].
Definition eS x y gx gy h := apps Law_eq_sym [x;gx;y;gy;h].
Definition eT x y z gx gy gz h k := apps Law_eq_trans [x;gx;y;gy;z;gz;h;k].
Definition eSucc x y gx gy h := apps Law_succ_congr [x;gx;y;gy;h].
Definition eAdd x x' y y' gx gx' gy gy' h k :=
  apps Law_add_congr [x;gx;x';gx';y;gy;y';gy';h;k].
Definition eMul x x' y y' gx gx' gy gy' h k :=
  apps Law_mul_congr [x;gx;x';gx';y;gy;y';gy';h;k].
Definition lR x gx := apps Law_order_refl [x;gx].
Definition lT x y z gx gy gz h k := apps Law_order_trans [x;gx;y;gy;z;gz;h;k].
Definition lSucc x gx := apps Law_le_succ [x;gx].

Fixpoint observed_numeral (n : nat) : closed_term :=
  match n with
  | 0 => g_zero_proof
  | S k => gS (numeral k) (observed_numeral k)
  end.
Fixpoint admitted_numeral (n : nat) : closed_term :=
  match n with
  | 0 => good_zero_proof
  | S k => apps good_succ_proof [numeral k; admitted_numeral k]
  end.

Lemma numeral_typed n : Typed ε (numeral n) Domain.
Proof.
  induction n as [|n IH].
  - exact zero_typed.
  - change (Typed ε (app successor (numeral n)) Domain).
    certify.
Qed.
Lemma observed_numeral_typed n : Typed ε (observed_numeral n) (GAt (numeral n)).
Proof.
  induction n as [|n IH].
  - exact observed_zero_typed.
  - pose proof (numeral_typed n) as Hn.
    cbn [observed_numeral]. certify.
Qed.
Lemma admitted_numeral_typed n : Typed ε (admitted_numeral n) (GoodAt (numeral n)).
Proof.
  induction n as [|n IH].
  - exact good_zero_typed.
  - pose proof (numeral_typed n) as Hn.
    cbn [admitted_numeral]. certify.
Qed.

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
    cbn [ground_add_proof]. certify.
  - pose proof (numeral_typed m) as Hm.
    pose proof (numeral_typed n) as Hn.
    pose proof (numeral_typed (m+n)) as Hmn.
    pose proof (observed_numeral_typed m) as Gm.
    pose proof (observed_numeral_typed n) as Gn.
    pose proof (observed_numeral_typed (m+n)) as Gmn.
    cbn [ground_add_proof]. certify.
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
    cbn [ground_mul_proof]. certify.
  - pose proof (numeral_typed m) as Hm.
    pose proof (numeral_typed n) as Hn.
    pose proof (numeral_typed (m*n)) as Hmn.
    pose proof (numeral_typed (n+m*n)) as Hsum.
    pose proof (observed_numeral_typed m) as Gm.
    pose proof (observed_numeral_typed n) as Gn.
    pose proof (observed_numeral_typed (m*n)) as Gmn.
    pose proof (observed_numeral_typed (n+m*n)) as Gsum.
    pose proof (ground_add_typed n (m*n)) as Hcalc.
    cbn [ground_mul_proof]. certify.
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
  - assert (i=0) by lia. subst i. cbn [ground_order_proof]. certify.
  - cbn [ground_order_proof]. destruct (Nat.eqb i (S j)) eqn:E.
    + apply Nat.eqb_eq in E. subst i.
      pose proof (numeral_typed (S j)) as Hj.
      pose proof (observed_numeral_typed (S j)) as Gj. certify.
    + assert (Hi : i <= j) by (apply Nat.eqb_neq in E; lia).
      pose proof (IH i Hi) as Hp.
      pose proof (numeral_typed i) as Hi'.
      pose proof (numeral_typed j) as Hj.
      pose proof (observed_numeral_typed i) as Gi.
      pose proof (observed_numeral_typed j) as Gj. certify.
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
