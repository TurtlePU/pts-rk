(** Direct R interpretation -- restructured draft, 2026-10-13.
    Compiler-unchecked. No new PTS axioms or answer-type nontriviality claims.
    See docs/DirectR.md and docs/DirectR-obligations.md. *)

From Stdlib Require Import Arith.PeanoNat Lia Lists.List Bool.Bool.
From PTSrk Require Import Syntax AbstractRewriting Congruence Reduction
  DefEq Context Typing Ranks.
Import ListNotations.

From PTSrk Require Import DirectRCodes.

Module ArithmeticCore.
Unset Implicit Arguments.

(** This is the Rocq metatheoretic algebraic core.  Its elements stand for
    ALREADY ADMITTED elements of an observation; hence the delta guards of
    the object telescope are not repeated in this record.  This record is
    not itself a PTS object and is not claimed to inhabit [Codes.Domain]. *)
Record observation : Type := {
  carrier : Type;
  oz : carrier;
  os : carrier -> carrier;
  oa : carrier -> carrier -> carrier;
  om : carrier -> carrier -> carrier;
  oe : carrier -> carrier -> Prop;
  ol : carrier -> carrier -> Prop;
  oe_refl : forall x, oe x x;
  oe_sym : forall x y, oe x y -> oe y x;
  oe_trans : forall x y z, oe x y -> oe y z -> oe x z;
  os_congr : forall x y, oe x y -> oe (os x) (os y);
  oa_congr : forall x x' y y', oe x x' -> oe y y' -> oe (oa x y) (oa x' y');
  om_congr : forall x x' y y', oe x x' -> oe y y' -> oe (om x y) (om x' y');
  ol_congr : forall x x' y y', oe x x' -> oe y y' -> ol x y -> ol x' y';
  ol_refl : forall x, ol x x;
  ol_trans : forall x y z, ol x y -> ol y z -> ol x z;
  oa_zero : forall x, oe (oa oz x) x;
  oa_succ : forall x y, oe (oa (os x) y) (os (oa x y));
  om_zero : forall x, oe (om oz x) oz;
  om_succ : forall x y, oe (om (os x) y) (oa y (om x y));
  om_zero_right : forall x, oe (om x oz) oz;
  ol_succ : forall x, ol x (os x);
  ol_add_left : forall x y, ol x (oa x y);
  ol_add_right : forall x y, ol y (oa x y);
  ol_mul_left : forall x y, ol (os oz) y -> ol x (om x y);
  ol_mul_right : forall x y, ol (os oz) x -> ol y (om x y)
}.

Fixpoint numeral (A : observation) (n : nat) : carrier A :=
  match n with 0 => oz A | S k => os A (numeral A k) end.

Lemma order_replace_left (A : observation) (x y z : carrier A) :
  oe A x y -> ol A x z -> ol A y z.
Proof.
  intros Hxy Hxz.
  exact (ol_congr A x y z z Hxy (oe_refl A z) Hxz).
Qed.

Lemma order_replace_right (A : observation) (x y z : carrier A) :
  oe A y z -> ol A x y -> ol A x z.
Proof.
  intros Hyz Hxy.
  exact (ol_congr A x x y z (oe_refl A x) Hyz Hxy).
Qed.

Lemma equal_implies_order (A : observation) (x y : carrier A) :
  oe A x y -> ol A x y.
Proof.
  intro H. exact (order_replace_right A x x y H (ol_refl A x)).
Qed.

Lemma numeral_add (A : observation) (m n : nat) :
  oe A (oa A (numeral A m) (numeral A n)) (numeral A (m + n)).
Proof.
  induction m as [|m IH].
  - cbn [numeral]. apply oa_zero.
  - cbn [numeral Nat.add].
    eapply (oe_trans A).
    + apply oa_succ.
    + apply os_congr. exact IH.
Qed.

Lemma numeral_mul (A : observation) (m n : nat) :
  oe A (om A (numeral A m) (numeral A n)) (numeral A (m * n)).
Proof.
  induction m as [|m IH].
  - cbn [numeral Nat.mul]. apply om_zero.
  - change (oe A (om A (os A (numeral A m)) (numeral A n))
                    (numeral A (n + m * n))).
    eapply (oe_trans A).
    + apply om_succ.
    + eapply (oe_trans A).
      * apply oa_congr.
        -- apply oe_refl.
        -- exact IH.
      * apply numeral_add.
Qed.

Lemma numeral_order (A : observation) (i j : nat) :
  i <= j -> ol A (numeral A i) (numeral A j).
Proof.
  intro H. induction H as [|j Hij IH].
  - apply ol_refl.
  - eapply (ol_trans A).
    + exact IH.
    + apply ol_succ.
Qed.

(** The finite/large alternatives underlying Lemma 4.  This is the host-logic
    version of the FLAT NEGATIVE disjunction [Codes.CaseAt], not a claim that
    positive existentials may be extracted from that negative encoding. *)
Definition bounded_case (A : observation) (n : nat) (x : carrier A) : Prop :=
  (exists i : nat, i <= n /\ oe A x (numeral A i)) \/
  ol A (numeral A (S n)) x.

Lemma case_of_numeral_equality (A : observation) (n k : nat) (x : carrier A) :
  oe A x (numeral A k) -> bounded_case A n x.
Proof.
  intro E. destruct (Nat.le_gt_cases k n) as [Hle | Hgt].
  - left. exists k. split; assumption.
  - right.
    eapply (order_replace_right A).
    + apply oe_sym. exact E.
    + apply numeral_order. lia.
Qed.

Lemma case_zero (A : observation) (n : nat) : bounded_case A n (oz A).
Proof.
  left. exists 0. split.
  - lia.
  - apply oe_refl.
Qed.

Lemma case_succ (A : observation) (n : nat) (x : carrier A) :
  bounded_case A n x -> bounded_case A n (os A x).
Proof.
  intros [[i [Hi Ei]] | Hlarge].
  - destruct (Nat.lt_ge_cases i n) as [Hlt | Hge].
    + left. exists (S i). split.
      * lia.
      * apply os_congr. exact Ei.
    + assert (i = n) by lia. subst i.
      right. apply equal_implies_order. apply oe_sym.
      apply os_congr. exact Ei.
  - right. eapply (ol_trans A).
    + exact Hlarge.
    + apply ol_succ.
Qed.

Lemma case_add (A : observation) (n : nat) (x y : carrier A) :
  bounded_case A n x -> bounded_case A n y ->
  bounded_case A n (oa A x y).
Proof.
  intros [[i [Hi Ei]] | Hx] Cy.
  - destruct Cy as [[j [Hj Ej]] | Hy].
    + apply (case_of_numeral_equality A n (i + j)).
      eapply (oe_trans A).
      * exact (oa_congr A x (numeral A i) y (numeral A j) Ei Ej).
      * apply numeral_add.
    + right. eapply (ol_trans A).
      * exact Hy.
      * apply ol_add_right.
  - right. eapply (ol_trans A).
    + exact Hx.
    + apply ol_add_left.
Qed.

Lemma positive_of_finite_case (A : observation) (i : nat) (x : carrier A) :
  oe A x (numeral A (S i)) -> ol A (numeral A 1) x.
Proof.
  intro E. eapply (order_replace_right A).
  - apply oe_sym. exact E.
  - apply numeral_order. lia.
Qed.

Lemma positive_of_large_case (A : observation) (n : nat) (x : carrier A) :
  ol A (numeral A (S n)) x -> ol A (numeral A 1) x.
Proof.
  intro H. eapply (ol_trans A _ (numeral A (S n))).
  - apply numeral_order. lia.
  - exact H.
Qed.

Lemma case_mul (A : observation) (n : nat) (x y : carrier A) :
  bounded_case A n x -> bounded_case A n y ->
  bounded_case A n (om A x y).
Proof.
  intros [[i [Hi Ei]] | Hx] [[j [Hj Ej]] | Hy].
  - apply (case_of_numeral_equality A n (i * j)).
    eapply (oe_trans A).
    + exact (om_congr A x (numeral A i) y (numeral A j) Ei Ej).
    + apply numeral_mul.
  - destruct i as [|i].
    + apply (case_of_numeral_equality A n 0).
      eapply (oe_trans A).
      * apply om_congr.
        -- exact Ei.
        -- apply oe_refl.
      * apply om_zero.
    + right. eapply (ol_trans A).
      * exact Hy.
      * apply ol_mul_right. apply (positive_of_finite_case A i x). exact Ei.
  - destruct j as [|j].
    + apply (case_of_numeral_equality A n 0).
      eapply (oe_trans A).
      * apply om_congr.
        -- apply oe_refl.
        -- exact Ej.
      * apply om_zero_right.
    + right. eapply (ol_trans A).
      * exact Hx.
      * apply ol_mul_left. apply (positive_of_finite_case A j y). exact Ej.
  - right. eapply (ol_trans A).
    + exact Hx.
    + apply ol_mul_left. apply (positive_of_large_case A n y). exact Hy.
Qed.

(** The source arithmetic expressions are external, finite trees.  An
    induction on these trees is NOT induction on arbitrary PTS inhabitants. *)
Inductive expression : Type :=
| e_zero : expression
| e_succ : expression -> expression
| e_add : expression -> expression -> expression
| e_mul : expression -> expression -> expression.

Fixpoint evaluate (A : observation) (e : expression) : carrier A :=
  match e with
  | e_zero => oz A
  | e_succ x => os A (evaluate A x)
  | e_add x y => oa A (evaluate A x) (evaluate A y)
  | e_mul x y => om A (evaluate A x) (evaluate A y)
  end.
Fixpoint value (e : expression) : nat :=
  match e with
  | e_zero => 0
  | e_succ x => S (value x)
  | e_add x y => value x + value y
  | e_mul x y => value x * value y
  end.
Fixpoint encode (e : expression) : Codes.closed_term :=
  match e with
  | e_zero => Codes.zero
  | e_succ x => app Codes.successor (encode x)
  | e_add x y => app (app Codes.addition (encode x)) (encode y)
  | e_mul x y => app (app Codes.multiplication (encode x)) (encode y)
  end.

Theorem expression_bounded_case (A : observation) (n : nat) (e : expression) :
  bounded_case A n (evaluate A e).
Proof.
  induction e as [|x IH|x IHx y IHy|x IHx y IHy]; cbn [evaluate].
  - apply case_zero.
  - apply case_succ. exact IH.
  - apply case_add; assumption.
  - apply case_mul; assumption.
Qed.

Theorem expression_to_numeral (A : observation) (e : expression) :
  oe A (evaluate A e) (numeral A (value e)).
Proof.
  induction e as [|x IH|x IHx y IHy|x IHx y IHy]; cbn [evaluate value].
  - apply oe_refl.
  - apply os_congr. exact IH.
  - eapply (oe_trans A).
    + exact (oa_congr A _ _ _ _ IHx IHy).
    + apply numeral_add.
  - eapply (oe_trans A).
    + exact (om_congr A _ _ _ _ IHx IHy).
    + apply numeral_mul.
Qed.

(** Separate meta-level interface. Kernel and Generated construct deep PTS
    witnesses directly; they do not instantiate this Prop-level record. *)
Record domain_closed (A : observation) (Good : carrier A -> Prop) : Prop := {
  good_z : Good (oz A);
  good_s : forall x, Good x -> Good (os A x);
  good_a : forall x y, Good x -> Good y -> Good (oa A x y);
  good_m : forall x y, Good x -> Good y -> Good (om A x y)
}.

Record R_schemes (A : observation) (Good : carrier A -> Prop) : Prop := {
  R_domain : domain_closed A Good;
  R_add : forall m n,
      oe A (oa A (numeral A m) (numeral A n)) (numeral A (m + n));
  R_mul : forall m n,
      oe A (om A (numeral A m) (numeral A n)) (numeral A (m * n));
  R_distinct : forall m n, m <> n -> ~ oe A (numeral A m) (numeral A n);
  R_bounded : forall n x, Good x -> ol A x (numeral A n) ->
      exists i, i <= n /\ oe A x (numeral A i);
  R_comparison : forall n x, Good x ->
      ol A x (numeral A n) \/ ol A (numeral A n) x
}.

Theorem theorem5_algebraic_core
    (A : observation) (Good : carrier A -> Prop)
    (closed_domain : domain_closed A Good)
    (certified_cases : forall n x, Good x -> bounded_case A n x)
    (separate : forall m n, m <> n -> ~ oe A (numeral A m) (numeral A n))
    (no_reverse : forall m n, n < m -> ~ ol A (numeral A m) (numeral A n))
  : R_schemes A Good.
Proof.
  constructor.
  - exact closed_domain.
  - exact (numeral_add A).
  - exact (numeral_mul A).
  - exact separate.
  - intros n x Gx Hxn.
    destruct (certified_cases n x Gx) as [Hfinite | Hlarge].
    + exact Hfinite.
    + exfalso. apply (no_reverse (S n) n).
      * lia.
      * eapply (ol_trans A); eassumption.
  - intros n x Gx.
    destruct (certified_cases n x Gx) as [[i [Hi Ei]] | Hlarge].
    + left. eapply (order_replace_left A).
      * apply oe_sym. exact Ei.
      * apply numeral_order. exact Hi.
    + right. eapply (ol_trans A _ (numeral A (S n))).
      * apply numeral_order. lia.
      * exact Hlarge.
Qed.

End ArithmeticCore.

Module CappedArithmetic.
Import ArithmeticCore.

(** Arithmetic observations for Section 3.  These are FINITE ARITHMETIC
    tables, not a set-theoretic model of PTS-rk or a proof of nontriviality. *)
Definition clamp (c x : nat) : nat := Nat.min x c.

Lemma clamp_small (c x : nat) : x <= c -> clamp c x = x.
Proof. intro H. unfold clamp. apply Nat.min_l. exact H. Qed.
Lemma clamp_large (c x : nat) : c <= x -> clamp c x = c.
Proof. intro H. unfold clamp. apply Nat.min_r. exact H. Qed.
Lemma clamp_bound (c x : nat) : clamp c x <= c.
Proof.
  destruct (Nat.le_ge_cases x c) as [H | H].
  - rewrite (clamp_small c x H). exact H.
  - rewrite (clamp_large c x H). apply Nat.le_refl.
Qed.
Lemma clamp_idem (c x : nat) : clamp c (clamp c x) = clamp c x.
Proof. apply clamp_small. apply clamp_bound. Qed.
Lemma clamp_zero (c : nat) : clamp c 0 = 0.
Proof. reflexivity. Qed.
Lemma clamp_one (c : nat) : 0 < c -> clamp c 1 = 1.
Proof. intro H. apply clamp_small. lia. Qed.
Lemma clamp_lower (c a x : nat) : a <= x -> a <= c -> a <= clamp c x.
Proof.
  intros Hax Hac. destruct (Nat.le_ge_cases x c) as [H | H].
  - rewrite (clamp_small c x H). exact Hax.
  - rewrite (clamp_large c x H). exact Hac.
Qed.

Lemma clamp_add_left (c x y : nat) :
  clamp c (clamp c x + y) = clamp c (x + y).
Proof.
  destruct (Nat.le_ge_cases x c) as [H | H].
  - rewrite (clamp_small c x H). reflexivity.
  - rewrite (clamp_large c x H).
    rewrite (clamp_large c (c + y)) by lia.
    rewrite (clamp_large c (x + y)) by lia.
    reflexivity.
Qed.
Lemma clamp_add_right (c x y : nat) :
  clamp c (x + clamp c y) = clamp c (x + y).
Proof.
  rewrite (Nat.add_comm x (clamp c y)).
  rewrite clamp_add_left. rewrite (Nat.add_comm y x). reflexivity.
Qed.
Lemma clamp_add_both (c x y : nat) :
  clamp c (clamp c x + clamp c y) = clamp c (x + y).
Proof. rewrite clamp_add_left, clamp_add_right. reflexivity. Qed.
Lemma clamp_succ (c x : nat) : clamp c (S (clamp c x)) = clamp c (S x).
Proof.
  replace (S (clamp c x)) with (clamp c x + 1) by lia.
  rewrite clamp_add_left. replace (x + 1) with (S x) by lia. reflexivity.
Qed.

Lemma clamp_mul_left (c x y : nat) :
  clamp c (clamp c x * y) = clamp c (x * y).
Proof.
  destruct (Nat.le_ge_cases x c) as [H | H].
  - rewrite (clamp_small c x H). reflexivity.
  - rewrite (clamp_large c x H).
    destruct y as [|y].
    + repeat rewrite Nat.mul_0_r. reflexivity.
    + rewrite (clamp_large c (c * S y)) by nia.
      rewrite (clamp_large c (x * S y)) by nia.
      reflexivity.
Qed.
Lemma clamp_mul_right (c x y : nat) :
  clamp c (x * clamp c y) = clamp c (x * y).
Proof.
  rewrite (Nat.mul_comm x (clamp c y)).
  rewrite clamp_mul_left. rewrite (Nat.mul_comm y x). reflexivity.
Qed.
Lemma clamp_mul_both (c x y : nat) :
  clamp c (clamp c x * clamp c y) = clamp c (x * y).
Proof. rewrite clamp_mul_left, clamp_mul_right. reflexivity. Qed.

Lemma capped_add_zero (c x : nat) : x <= c -> clamp c (0 + x) = x.
Proof. intro H. change (clamp c x = x). apply clamp_small. exact H. Qed.
Lemma capped_add_succ (c x y : nat) :
  clamp c (clamp c (S x) + y) = clamp c (S (clamp c (x + y))).
Proof. rewrite clamp_add_left, clamp_succ. reflexivity. Qed.
Lemma capped_mul_zero (c x : nat) : clamp c (0 * x) = 0.
Proof. reflexivity. Qed.
Lemma capped_mul_zero_right (c x : nat) : clamp c (x * 0) = 0.
Proof. rewrite Nat.mul_0_r. reflexivity. Qed.
Lemma capped_mul_succ (c x y : nat) :
  clamp c (clamp c (S x) * y) = clamp c (y + clamp c (x * y)).
Proof. rewrite clamp_mul_left, clamp_add_right. reflexivity. Qed.

Definition bounded (c : nat) := {x : nat | x <= c}.
Definition val {c : nat} (x : bounded c) : nat := proj1_sig x.
Definition bound {c : nat} (x : bounded c) : val x <= c := proj2_sig x.
Definition pack (c n : nat) : bounded c :=
  exist (fun x => x <= c) (clamp c n) (clamp_bound c n).
Definition cz (c : nat) : bounded c := pack c 0.
Definition cs (c : nat) (x : bounded c) : bounded c := pack c (S (val x)).
Definition ca (c : nat) (x y : bounded c) : bounded c := pack c (val x + val y).
Definition cm (c : nat) (x y : bounded c) : bounded c := pack c (val x * val y).
Definition ce (c : nat) (x y : bounded c) : Prop := val x = val y.
Definition cl (c : nat) (x y : bounded c) : Prop := val x <= val y.

(** Every law from the observation telescope holds, including right
    multiplication by zero at the cap.  No cancellation is assumed. *)
Definition capped_observation (c : nat) (positive_cap : 0 < c) : observation.
Proof.
  refine {| carrier := bounded c;
            oz := cz c; os := cs c; oa := ca c; om := cm c;
            oe := ce c; ol := cl c |}.
  - intro x. reflexivity.
  - intros x y H. symmetry. exact H.
  - intros x y z Hxy Hyz. transitivity (val y); assumption.
  - intros x y H.
    unfold ce, cs, val, pack in *. cbn in *. now rewrite H.
  - intros x x' y y' Hx Hy.
    unfold ce, ca, val, pack in *. cbn in *. now rewrite Hx, Hy.
  - intros x x' y y' Hx Hy.
    unfold ce, cm, val, pack in *. cbn in *. now rewrite Hx, Hy.
  - intros x x' y y' Hx Hy Hxy. unfold ce, cl in *. lia.
  - intro x. apply Nat.le_refl.
  - intros x y z Hxy Hyz. unfold cl in *. lia.
  - intro x. change (clamp c (0 + val x) = val x).
    apply capped_add_zero. exact (bound x).
  - intros x y.
    change (clamp c (clamp c (S (val x)) + val y) =
            clamp c (S (clamp c (val x + val y)))).
    apply capped_add_succ.
  - intro x. change (clamp c (0 * val x) = 0). apply capped_mul_zero.
  - intros x y.
    change (clamp c (clamp c (S (val x)) * val y) =
            clamp c (val y + clamp c (val x * val y))).
    apply capped_mul_succ.
  - intro x. change (clamp c (val x * 0) = 0). apply capped_mul_zero_right.
  - intro x. change (val x <= clamp c (S (val x))).
    apply clamp_lower.
    + lia.
    + exact (bound x).
  - intros x y. change (val x <= clamp c (val x + val y)).
    apply clamp_lower.
    + lia.
    + exact (bound x).
  - intros x y. change (val y <= clamp c (val x + val y)).
    apply clamp_lower.
    + lia.
    + exact (bound y).
  - intros x y Hy. change (clamp c 1 <= val y) in Hy.
    rewrite (clamp_one c positive_cap) in Hy.
    change (val x <= clamp c (val x * val y)).
    apply clamp_lower.
    + nia.
    + exact (bound x).
  - intros x y Hx. change (clamp c 1 <= val x) in Hx.
    rewrite (clamp_one c positive_cap) in Hx.
    change (val y <= clamp c (val x * val y)).
    apply clamp_lower.
    + nia.
    + exact (bound y).
Defined.

Lemma capped_numeral (c : nat) (Hc : 0 < c) (n : nat) :
  val (numeral (capped_observation c Hc) n) = clamp c n.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - change (clamp c (S (val (numeral (capped_observation c Hc) n))) =
            clamp c (S n)).
    rewrite IH. apply clamp_succ.
Qed.

Lemma capped_expression (c : nat) (Hc : 0 < c) (e : expression) :
  val (evaluate (capped_observation c Hc) e) = clamp c (value e).
Proof.
  induction e as [|x IH|x IHx y IHy|x IHx y IHy].
  - reflexivity.
  - change (clamp c (S (val (evaluate (capped_observation c Hc) x))) =
            clamp c (S (value x))).
    rewrite IH. apply clamp_succ.
  - change (clamp c (val (evaluate (capped_observation c Hc) x) +
                     val (evaluate (capped_observation c Hc) y)) =
            clamp c (value x + value y)).
    rewrite IHx, IHy. apply clamp_add_both.
  - change (clamp c (val (evaluate (capped_observation c Hc) x) *
                     val (evaluate (capped_observation c Hc) y)) =
            clamp c (value x * value y)).
    rewrite IHx, IHy. apply clamp_mul_both.
Qed.

(** Separation in the external class of certified arithmetic observations.
    The additional step needed by the paper is to REALIZE each of these
    finite observations as PTS selector terms with typing derivations. *)
Definition universal_numeral_equality (m n : nat) : Prop :=
  forall A : observation, oe A (numeral A m) (numeral A n).
Definition universal_numeral_order (m n : nat) : Prop :=
  forall A : observation, ol A (numeral A m) (numeral A n).

Theorem observations_separate_numerals (m n : nat) :
  universal_numeral_equality m n -> m = n.
Proof.
  intro H. set (c := S (m + n)).
  assert (Hc : 0 < c) by (unfold c; lia).
  specialize (H (capped_observation c Hc)).
  change (val (numeral (capped_observation c Hc) m) =
          val (numeral (capped_observation c Hc) n)) in H.
  rewrite (capped_numeral c Hc m), (capped_numeral c Hc n) in H.
  assert (Hm : m <= c) by (unfold c; lia).
  assert (Hn : n <= c) by (unfold c; lia).
  rewrite (clamp_small c m Hm), (clamp_small c n Hn) in H.
  exact H.
Qed.

Theorem observations_reflect_numeral_order (m n : nat) :
  universal_numeral_order m n -> m <= n.
Proof.
  intro H. set (c := S (m + n)).
  assert (Hc : 0 < c) by (unfold c; lia).
  specialize (H (capped_observation c Hc)).
  change (val (numeral (capped_observation c Hc) m) <=
          val (numeral (capped_observation c Hc) n)) in H.
  rewrite (capped_numeral c Hc m), (capped_numeral c Hc n) in H.
  assert (Hm : m <= c) by (unfold c; lia).
  assert (Hn : n <= c) by (unfold c; lia).
  rewrite (clamp_small c m Hm), (clamp_small c n Hn) in H.
  exact H.
Qed.

Corollary observations_refute_reverse_order (n : nat) :
  ~ universal_numeral_order (S n) n.
Proof.
  intro H. pose proof (observations_reflect_numeral_order (S n) n H). lia.
Qed.

Theorem observations_reflect_ground_equality (e f : expression) :
  (forall A : observation, oe A (evaluate A e) (evaluate A f)) -> value e = value f.
Proof.
  intro H. set (c := S (value e + value f)).
  assert (Hc : 0 < c) by (unfold c; lia).
  specialize (H (capped_observation c Hc)).
  change (val (evaluate (capped_observation c Hc) e) =
          val (evaluate (capped_observation c Hc) f)) in H.
  rewrite (capped_expression c Hc e), (capped_expression c Hc f) in H.
  assert (He : value e <= c) by (unfold c; lia).
  assert (Hf : value f <= c) by (unfold c; lia).
  rewrite (clamp_small c (value e) He), (clamp_small c (value f) Hf) in H.
  exact H.
Qed.

Example zero_at_the_cap : forall c, clamp c (c * 0) = 0.
Proof. intro c. apply capped_mul_zero_right. Qed.

End CappedArithmetic.
