(** Bounded certificate for powerset formation inside a supplied ambient
    set. Adequacy of the bound is essential: quantification over W alone
    does not characterize Power X unless all subsets of X occur in W.
    This is an Ens translation check, not a first-order BZC interpretation. *)
From ZFC Require Import Sets Axioms Cartesian.
From PTSrk Require Import Syntax.
From PTSrkModel Require Import SetFunctions SetApplication HierarchyBounds
  BoundedFormulas BoundedGraphs BoundedFiniteCarriers SuppliedHierarchy
  CardinalHierarchy CountableCodes.
Import Bounded.

Definition powersetF {n} (W X Y : Fin n) :=
  conj (all Y (subsetF fzero (fsucc X)))
    (all W (impl (subsetF fzero (fsucc X)) (member fzero (fsucc Y)))).

Theorem powerset_formula_correct {n} (r : Fin n -> Ens) W X Y :
  INC (Power (r X)) (r W) ->
  (holds (powersetF W X Y) r <-> EQ (r Y) (Power (r X))).
Proof.
  intro HW. unfold powersetF. cbn [holds].
  setoid_rewrite subset_formula_correct. cbn [fin_match]. split.
  - intros [HY HC]. apply INC_EQ.
    + intros z Hz. apply INC_IN_Power, HY; exact Hz.
    + intros z Hz. apply HC; [apply HW; exact Hz |].
      apply IN_Power_INC; exact Hz.
  - intro E. split.
    + intros z Hz. apply IN_Power_INC.
      exact (IN_sound_right z _ _ E Hz).
    + intros z Hz HZ. apply (IN_sound_right z _ _ (EQ_sym _ _ E)).
      apply INC_IN_Power; exact HZ.
Qed.

Definition powerset_certificate : Formula 3 :=
  powersetF (fsucc (fsucc fzero)) (fsucc fzero) fzero.
Definition powerset_parameters (W : Ens) :=
  fin_match W (fun i : Fin 0 => match i with end).
Definition bounded_powerset_graph W := bounded_formula_graph
  powerset_certificate (powerset_parameters W) W W.

Section Ambient.
Variable W : Ens.
Hypothesis HW : transitive_set W.
Hypothesis HP : forall x, IN x W -> IN (Power x) W.

Lemma powerset_certificate_correct x y : IN x W ->
  (holds powerset_certificate (fin_match y (fin_match x (powerset_parameters W)))
    <-> EQ y (Power x)).
Proof. intro Hx. apply powerset_formula_correct. apply HW, HP; exact Hx. Qed.

Theorem bounded_powerset_graph_application x y :
  application (bounded_powerset_graph W) x y <-> IN x W /\ EQ y (Power x).
Proof.
  unfold bounded_powerset_graph. rewrite bounded_formula_graph_spec. split.
  - intros [Hx [Hy H]]. split; [exact Hx |].
    apply (proj1 (powerset_certificate_correct x y Hx)); exact H.
  - intros [Hx E]. split; [exact Hx |]. split.
    + exact (IN_sound_left (Power x) y W (EQ_sym _ _ E) (HP x Hx)).
    + apply (proj2 (powerset_certificate_correct x y Hx)); exact E.
Qed.

Theorem bounded_powerset_graph_typed :
  IN (bounded_powerset_graph W) (dependent_product W (fun _ => W)).
Proof.
  apply bounded_formula_graph_typed.
  - intros x Hx. exists (Power x). split; [apply HP; exact Hx |].
    apply (proj2 (powerset_certificate_correct x _ Hx)), EQ_refl.
  - intros x y z Hx Hy Hz HY HZ.
    apply (proj1 (powerset_certificate_correct x y Hx)) in HY.
    apply (proj1 (powerset_certificate_correct x z Hx)) in HZ.
    eapply EQ_tran; [exact HY | apply EQ_sym; exact HZ].
Qed.

Theorem bounded_powerset_graph_beta x : IN x W ->
  EQ (apply_set (bounded_powerset_graph W) x) (Power x).
Proof.
  intro Hx. apply apply_set_value.
  - apply bounded_powerset_graph_application; split; [exact Hx | apply EQ_refl].
  - intros y Hy. apply bounded_powerset_graph_application in Hy; tauto.
Qed.
End Ambient.

Theorem envelope_powerset_graph_typed W H :
  transitive_set W -> tower_envelope W H ->
  IN (bounded_powerset_graph H) (dependent_product H (fun _ => H)).
Proof.
  intros HW HH. apply bounded_powerset_graph_typed.
  - exact (envelope_transitive W H HW HH).
  - intros x Hx. exact (envelope_power_closed W H x HW HH Hx).
Qed.

Theorem envelope_powerset_carrier_step W H i :
  transitive_set W -> INC omega_codes W -> tower_envelope W H ->
  EQ (apply_set (bounded_powerset_graph H) (carrier i)) (carrier (S i)).
Proof.
  intros HW HO HH. change (EQ (apply_set (bounded_powerset_graph H) (carrier i))
    (Power (carrier i))).
  apply bounded_powerset_graph_beta.
  - exact (envelope_transitive W H HW HH).
  - intros x Hx. exact (envelope_power_closed W H x HW HH Hx).
  - exact (envelope_carrier W H i HO HH).
Qed.

Print Assumptions powerset_formula_correct.
Print Assumptions powerset_certificate_correct.
Print Assumptions bounded_powerset_graph_application.
Print Assumptions bounded_powerset_graph_typed.
Print Assumptions bounded_powerset_graph_beta.
Print Assumptions envelope_powerset_graph_typed.
Print Assumptions envelope_powerset_carrier_step.
