(** The finite carrier at a singleton numeral is its least transitive
    closure. Quantifying over subsets of omega_codes gives a bounded
    definition and a uniform graph without selecting a native function.
    The 3*n code-tag arithmetic and the other decoder branches are separate. *)
From Stdlib Require Import Arith.PeanoNat Lia.
From Equations Require Import Equations.
From ZFC Require Import Sets Axioms Cartesian.
From PTSrk Require Import Syntax.
From PTSrkModel Require Import SetFunctions SetApplication CodeUniverses
  CountableCodes CodeHierarchyBounds HierarchyBounds BoundedFormulas
  BoundedFormulaTransport BoundedGraphs.
Import CodeUniverses.CodeUniverses Bounded.

Lemma finite_carrier_transitive n : transitive_set (finite_carrier n).
Proof.
  intros x Hx y Hy. apply finite_carrier_membership in Hx as [k [Hk E]].
  destruct k as [|k].
  - destruct (Vide_est_vide y (IN_sound_right y _ _ E Hy)).
  - apply finite_carrier_membership. exists k; split; [lia |].
    apply IN_Sing_EQ. exact (IN_sound_right y _ _ E Hy).
Qed.

Lemma numeral_subset_finite n : INC (numeral n) (finite_carrier n).
Proof.
  intros x Hx. destruct n as [|n].
  - destruct (Vide_est_vide x Hx).
  - apply finite_carrier_membership. exists n; split; [lia | apply IN_Sing_EQ; exact Hx].
Qed.

Lemma finite_carrier_least n X : transitive_set X ->
  INC (numeral n) X -> INC (finite_carrier n) X.
Proof.
  induction n as [|n IH]; intros HX HN y Hy.
  - apply finite_carrier_membership in Hy as [k [Hk _]]; lia.
  - assert (Hn : IN (numeral n) X) by (apply HN, IN_Sing).
    apply finite_carrier_membership in Hy as [k [Hk E]].
    destruct (Nat.eq_dec k n) as [-> | Hne].
    + exact (IN_sound_left (numeral n) y X (EQ_sym _ _ E) Hn).
    + apply IH; [exact HX | exact (HX (numeral n) Hn) |].
      apply finite_carrier_membership; exists k; split; [lia | exact E].
Qed.

Definition subsetF {n} (X Y : Fin n) := all X (member fzero (fsucc Y)).
Definition transitiveF {n} (X : Fin n) :=
  all X (all fzero (member fzero (fsucc (fsucc X)))).
Lemma subset_formula_correct {n} (r : Fin n -> Ens) X Y :
  holds (subsetF X Y) r <-> INC (r X) (r Y).
Proof. reflexivity. Qed.
Lemma transitive_formula_correct {n} (r : Fin n -> Ens) X :
  holds (transitiveF X) r <-> transitive_set (r X).
Proof. reflexivity. Qed.

Definition finiteCarrierF {n} (P q Y : Fin n) :=
  conj (transitiveF Y) (conj (subsetF q Y)
    (all P (impl (conj (transitiveF fzero) (subsetF (fsucc q) fzero))
      (subsetF (fsucc Y) fzero)))).

Theorem finite_carrier_formula_correct {k} (r : Fin k -> Ens) P q Y n :
  EQ (r P) (Power omega_codes) -> EQ (r q) (numeral n) ->
  (holds (finiteCarrierF P q Y) r <-> EQ (r Y) (finite_carrier n)).
Proof.
  intros EP EN. unfold finiteCarrierF. cbn [holds].
  setoid_rewrite transitive_formula_correct. setoid_rewrite subset_formula_correct.
  cbn [fin_match]. split.
  - intros [HY [HN HL]]. apply INC_EQ.
    + apply HL.
      * apply (IN_sound_right _ _ _ (EQ_sym _ _ EP)), INC_IN_Power, finite_subset_omega.
      * split; [apply finite_carrier_transitive |].
        intros z Hz. apply numeral_subset_finite.
        exact (IN_sound_right z _ _ EN Hz).
    + apply finite_carrier_least; [exact HY |].
      intros z Hz. apply HN. exact (IN_sound_right z _ _ (EQ_sym _ _ EN) Hz).
  - intro E. split.
    + intros x Hx y Hy. apply (IN_sound_right y _ _ (EQ_sym _ _ E)).
      apply (finite_carrier_transitive n x); [exact (IN_sound_right x _ _ E Hx) | exact Hy].
    + split.
      * intros z Hz. apply (IN_sound_right z _ _ (EQ_sym _ _ E)), numeral_subset_finite.
        exact (IN_sound_right z _ _ EN Hz).
      * intros X HX [HT HN] z Hz. apply (finite_carrier_least n X HT).
        -- intros u Hu. apply HN. exact (IN_sound_right u _ _ (EQ_sym _ _ EN) Hu).
        -- exact (IN_sound_right z _ _ E Hz).
Qed.

Definition finite_carrier_certificate : Formula 3 :=
  finiteCarrierF (fsucc (fsucc fzero)) (fsucc fzero) fzero.
Definition finite_carrier_parameters :=
  fin_match (Power omega_codes) (fun i : Fin 0 => match i with end).

Lemma finite_carrier_certificate_correct x n y : EQ x (numeral n) ->
  (holds finite_carrier_certificate
     (fin_match y (fin_match x finite_carrier_parameters)) <-> EQ y (finite_carrier n)).
Proof. intro E. apply finite_carrier_formula_correct; [apply EQ_refl | exact E]. Qed.

Definition finite_carrier_graph := bounded_formula_graph finite_carrier_certificate
  finite_carrier_parameters omega_codes (Power omega_codes).

Theorem finite_carrier_graph_typed :
  IN finite_carrier_graph (dependent_product omega_codes (fun _ => Power omega_codes)).
Proof.
  apply bounded_formula_graph_typed.
  - intros x Hx. apply omega_membership in Hx as [n E].
    exists (finite_carrier n). split; [apply INC_IN_Power, finite_subset_omega |].
    apply (proj2 (finite_carrier_certificate_correct x n _ E)), EQ_refl.
  - intros x y z Hx Hy Hz HP HQ. apply omega_membership in Hx as [n E].
    apply (proj1 (finite_carrier_certificate_correct x n y E)) in HP.
    apply (proj1 (finite_carrier_certificate_correct x n z E)) in HQ.
    eapply EQ_tran; [exact HP | apply EQ_sym; exact HQ].
Qed.

Theorem finite_carrier_graph_application n y :
  application finite_carrier_graph (numeral n) y <-> EQ y (finite_carrier n).
Proof.
  unfold finite_carrier_graph. rewrite bounded_formula_graph_spec.
  rewrite (finite_carrier_certificate_correct _ n y (EQ_refl _)). split.
  - tauto.
  - intro E. split; [apply numeral_in_omega |]. split; [| exact E].
    apply (IN_sound_left (finite_carrier n) y _ (EQ_sym _ _ E)).
    apply INC_IN_Power, finite_subset_omega.
Qed.

Theorem finite_carrier_graph_beta n :
  EQ (apply_set finite_carrier_graph (numeral n)) (finite_carrier n).
Proof.
  apply apply_set_value.
  - apply finite_carrier_graph_application, EQ_refl.
  - intros y Hy. apply finite_carrier_graph_application; exact Hy.
Qed.

Print Assumptions finite_carrier_transitive.
Print Assumptions numeral_subset_finite.
Print Assumptions finite_carrier_least.
Print Assumptions finite_carrier_formula_correct.
Print Assumptions finite_carrier_certificate_correct.
Print Assumptions finite_carrier_graph_typed.
Print Assumptions finite_carrier_graph_application.
Print Assumptions finite_carrier_graph_beta.
