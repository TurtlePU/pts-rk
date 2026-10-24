(** A fixed original-PTS evaluator for conjunction expressions with Boolean
    DATA leaves.  No whole-expression result or source-dependent truth table
    is substituted for the represented expression.  Comparison operations
    will be supplied as leaf terms and evaluated by this same fold. *)
From Stdlib Require Import Lists.List Bool.Bool.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting Reduction.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRCheck DirectRStructural.
From PTSrk.SelfConsistency Require Import GuardedTables StructuralCodes CheckerComparisons.
Import ListNotations.

Module InternalComparisonFolds.
Import CommonCodes Core Structural.
Module GT := GuardedTables.GuardedTables.
Module CC := CheckerComparisons.CheckerComparisons.

Definition B := NClosed GT.boolean.
Definition expression := close
  (NPi 0 (NSort 1)
    (nArrow (nArrow B (NVar 0))
      (nArrow (nArrow (NVar 0) (nArrow (NVar 0) (NVar 0))) (NVar 0)))) eq_refl.
Definition E := NClosed expression.
Definition leaf := close
  (nlams [(1, B); (0, NSort 1); (2, nArrow B (NVar 0));
    (3, nArrow (NVar 0) (nArrow (NVar 0) (NVar 0)))]
    (NApp (NVar 2) (NVar 1))) eq_refl.
Definition both := close
  (nlams [(4, E); (5, E); (0, NSort 1); (2, nArrow B (NVar 0));
    (3, nArrow (NVar 0) (nArrow (NVar 0) (NVar 0)))]
    (napps (NVar 3)
      [napps (NVar 4) [NVar 0; NVar 2; NVar 3];
       napps (NVar 5) [NVar 0; NVar 2; NVar 3]])) eq_refl.
Definition conjunction := close
  (nlams [(0, B); (1, B); (2, NSort 0); (3, NVar 2); (4, NVar 2)]
    (napps (NVar 0) [NVar 2;
      napps (NVar 1) [NVar 2; NVar 3; NVar 4]; NVar 4])) eq_refl.
Definition identity := close (NLam 0 B (NVar 0)) eq_refl.
Definition evaluate := close
  (NLam 0 E (napps (NVar 0)
    [B; NClosed identity; NClosed conjunction])) eq_refl.

Theorem expression_sorted : Typed ε expression (𝓤 3).
Proof. RkCheck.certify_with 256. Qed.
Theorem leaf_typed : Typed ε leaf (Arrow GT.boolean expression).
Proof. RkCheck.certify_with 256. Qed.
Theorem both_typed : Typed ε both (Arrow expression (Arrow expression expression)).
Proof. RkCheck.certify_with 256. Qed.
Theorem conjunction_typed : Typed ε conjunction
  (Arrow GT.boolean (Arrow GT.boolean GT.boolean)).
Proof. RkCheck.certify_with 256. Qed.
Theorem identity_typed : Typed ε identity (Arrow GT.boolean GT.boolean).
Proof. RkCheck.certify_with 256. Qed.
Theorem evaluate_type_sorted : Typed ε (Arrow expression GT.boolean) (𝓤 4).
Proof. RkCheck.certify_with 256. Qed.
Theorem evaluate_typed : Typed ε evaluate (Arrow expression GT.boolean).
Proof. RkCheck.certify_with 256. Qed.

Theorem conjunction_beta a b :
  app (app conjunction (GT.point a)) (GT.point b) =ᵝ GT.point (andb a b).
Proof.
  destruct a, b; eapply RkCheck.check_conv_sound with (fuel := 256);
    vm_compute; reflexivity.
Qed.

(** Open schemata keep arbitrary supplied leaf programs opaque. *)
Lemma evaluate_leaf_schema :
  @app nat 1 (lift_closed evaluate) (app (lift_closed leaf) V0) =ᵝ V0.
Proof.
  eapply RkCheck.check_conv_sound with (fuel := 256); vm_compute; reflexivity.
Qed.
Lemma evaluate_both_schema :
  @app nat 2 (lift_closed evaluate)
    (app (app (lift_closed both) (var (fsucc fzero))) V0) =ᵝ
  app (app (lift_closed conjunction)
    (app (lift_closed evaluate) (var (fsucc fzero))))
    (app (lift_closed evaluate) V0).
Proof.
  eapply RkCheck.check_conv_sound with (fuel := 256); vm_compute; reflexivity.
Qed.
Theorem evaluate_leaf_beta (b : closed_term) :
  app evaluate (app leaf b) =ᵝ b.
Proof.
  pose proof (replace_equiv (fin_match b (fun i : Fin 0 => match i with end))
    _ _ evaluate_leaf_schema) as H.
  structural_substitution_in H; exact H.
Qed.
Theorem evaluate_both_beta (x y : closed_term) :
  app evaluate (app (app both x) y) =ᵝ
    app (app conjunction (app evaluate x)) (app evaluate y).
Proof.
  pose proof (replace_equiv
    (fin_match y (fin_match x (fun i : Fin 0 => match i with end)))
    _ _ evaluate_both_schema) as H.
  structural_substitution_in H; exact H.
Qed.

(** Each comparison remains an operation applied to its own two operands.
    The native expression compiler never supplies the overall Boolean result. *)
Fixpoint quote_with (compare : code -> code -> closed_term) (e : CC.Expr) : closed_term :=
  match e with
  | CC.Truth b => app leaf (GT.point b)
  | CC.Compare x y => app leaf (compare x y)
  | CC.Both a b => app (app both (quote_with compare a)) (quote_with compare b)
  end.
Fixpoint evaluate_with (compare : code -> code -> closed_term) (e : CC.Expr) : closed_term :=
  match e with
  | CC.Truth b => GT.point b
  | CC.Compare x y => compare x y
  | CC.Both a b =>
      app (app conjunction (evaluate_with compare a)) (evaluate_with compare b)
  end.

Theorem quote_with_typed compare e :
  (forall x y, Typed ε (compare x y) GT.boolean) ->
  Typed ε (quote_with compare e) expression.
Proof.
  intro H; induction e; cbn [quote_with].
  - eapply arrow_application; [apply leaf_typed | apply GT.point_typed].
  - eapply arrow_application; [apply leaf_typed | apply H].
  - eapply arrow_application; [|exact IHe2].
    eapply arrow_application; [apply both_typed | exact IHe1].
Qed.
Theorem evaluate_with_typed compare e :
  (forall x y, Typed ε (compare x y) GT.boolean) ->
  Typed ε (evaluate_with compare e) GT.boolean.
Proof.
  intro H; induction e; cbn [evaluate_with].
  - apply GT.point_typed.
  - apply H.
  - eapply arrow_application; [|exact IHe2].
    eapply arrow_application; [apply conjunction_typed | exact IHe1].
Qed.
Theorem evaluate_quote_typed compare e :
  (forall x y, Typed ε (compare x y) GT.boolean) ->
  Typed ε (app evaluate (quote_with compare e)) GT.boolean.
Proof.
  intro H; eapply arrow_application; [apply evaluate_typed |].
  apply quote_with_typed; exact H.
Qed.

(** The first equation is symbolic and needs no comparison correctness or
    typing premise.  It exhibits the literal AND of the supplied leaf terms. *)
Theorem evaluate_quote_beta compare e :
  app evaluate (quote_with compare e) =ᵝ evaluate_with compare e.
Proof.
  induction e; cbn [quote_with evaluate_with].
  - apply evaluate_leaf_beta.
  - apply evaluate_leaf_beta.
  - transitivity (app (app conjunction (app evaluate (quote_with compare e1)))
      (app evaluate (quote_with compare e2))).
    + apply evaluate_both_beta.
    + apply beta_app; [apply beta_app; [reflexivity | exact IHe1] | exact IHe2].
Qed.
Theorem evaluate_with_canonical compare e :
  (forall x y, compare x y =ᵝ GT.point (CC.code_eqb x y)) ->
  evaluate_with compare e =ᵝ GT.point (CC.eval e).
Proof.
  intro H; induction e; cbn [evaluate_with CC.eval].
  - reflexivity.
  - apply H.
  - transitivity (app (app conjunction (GT.point (CC.eval e1))) (GT.point (CC.eval e2))).
    + apply beta_app; [apply beta_app; [reflexivity | exact IHe1] | exact IHe2].
    + apply conjunction_beta.
Qed.
Theorem evaluate_quote_canonical compare e :
  (forall x y, compare x y =ᵝ GT.point (CC.code_eqb x y)) ->
  app evaluate (quote_with compare e) =ᵝ GT.point (CC.eval e).
Proof.
  intro H; transitivity (evaluate_with compare e);
    [apply evaluate_quote_beta | apply evaluate_with_canonical; exact H].
Qed.

(** Canonical Booleans are beta-normal, so the preceding equivalence also
    provides actual forward reduction and exact output correspondence. *)
Lemma point_no_step b (t : closed_term) : ~ step nat 0 (GT.point b) t.
Proof.
  destruct b; intro H;
    repeat match goal with H : step _ _ _ _ |- _ => inversion H; clear H; subst end.
Qed.
Lemma point_reduct_equal b (t : closed_term) :
  reduces_to nat 0 (GT.point b) t -> GT.point b = t.
Proof.
  intro H; inversion H; subst; [reflexivity |].
  exfalso; eapply point_no_step; eassumption.
Qed.
Lemma equivalent_point_reduces (t : closed_term) b :
  t =ᵝ GT.point b -> reduces_to nat 0 t (GT.point b).
Proof.
  intro H; apply def_equiv_prop in H; destruct H as [u [HT HP]].
  rewrite <- (point_reduct_equal b u HP) in HT; exact HT.
Qed.
Lemma point_equiv_injective b c : GT.point b =ᵝ GT.point c -> b = c.
Proof.
  intro H; apply equivalent_point_reduces in H; apply point_reduct_equal in H.
  destruct b, c; try reflexivity; discriminate H.
Qed.
Theorem evaluate_quote_reduces compare e :
  (forall x y, compare x y =ᵝ GT.point (CC.code_eqb x y)) ->
  reduces_to nat 0 (app evaluate (quote_with compare e)) (GT.point (CC.eval e)).
Proof. intro H; apply equivalent_point_reduces, evaluate_quote_canonical; exact H. Qed.
Theorem evaluate_quote_output_exact compare e b :
  (forall x y, compare x y =ᵝ GT.point (CC.code_eqb x y)) ->
  (reduces_to nat 0 (app evaluate (quote_with compare e)) (GT.point b)
    <-> CC.eval e = b).
Proof.
  intro H; split.
  - intro HB; apply point_equiv_injective.
    transitivity (app evaluate (quote_with compare e)).
    + symmetry; apply evaluate_quote_canonical; exact H.
    + apply def_equiv_prop; exists (GT.point b); split; [exact HB | reflexivity].
  - intros <-; apply evaluate_quote_reduces; exact H.
Qed.

End InternalComparisonFolds.
