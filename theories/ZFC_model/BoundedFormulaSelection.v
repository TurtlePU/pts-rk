(** A bounded defining formula for selection from formula-defined fibers.
    Both the candidate set and the selected graph have bounded separation
    predicates. This does not certify arbitrary semantic predicates. *)
From Equations Require Import Equations.
From ZFC Require Import Sets Axioms.
From PTSrk Require Import Syntax.
From PTSrkModel Require Import SetFunctions SetApplication CountableDichotomy
  BoundedFormulas BoundedFormulaTransport BoundedApplication BoundedGraphs
  BoundedChoice.
Import Bounded.

Definition selection_lift {n} : Fin (S (S n)) -> Fin (S (S (S (S (S (S (S (S n)))))))) :=
  fin_match fzero (fin_match (fsucc (fsucc (fsucc fzero)))
    (fun i => fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc i))))))))).
Definition selection_parameters {n} B c (r : Fin n -> Ens) :=
  fin_match B (fin_match (Power B) (fin_match c (fin_match (value_bound c) r))).
Definition selection_env {n} B c (r : Fin n -> Ens) x y :=
  fin_match y (fin_match x (selection_parameters B c r)).

Lemma selection_lift_correct {n} p (r : Fin n -> Ens) B c x y K z :
  holds (rename_formula selection_lift p)
    (fin_match z (fin_match K (selection_env B c r x y))) <-> formula_relation p r x z.
Proof.
  rewrite holds_rename. apply holds_extensional.
  intro i; dependent elimination i as [fzero | fsucc i]; [apply EQ_refl |].
  dependent elimination i; apply EQ_refl.
Qed.

Definition selection_certificate {n} (p : Formula (S (S n))) : Formula (S (S (S (S (S (S n)))))) :=
  ex (fsucc (fsucc (fsucc fzero)))
    (conj (all fzero (conj (member fzero (fsucc (fsucc (fsucc (fsucc fzero)))))
      (rename_formula selection_lift p)))
      (conj (all (fsucc (fsucc (fsucc fzero)))
        (impl (rename_formula selection_lift p) (member fzero (fsucc fzero))))
        (applyValueF (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))
          (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))) fzero (fsucc fzero)))).

Theorem selection_certificate_correct {n} p (r : Fin n -> Ens) B c x y :
  holds (selection_certificate p) (selection_env B c r x y) <->
  EQ y (apply_set c (relation_candidates B (formula_relation p r) x)).
Proof.
  unfold selection_certificate. cbn [holds].
  setoid_rewrite selection_lift_correct.
  setoid_rewrite apply_value_formula_correct.
  2: { intros v HV. eapply application_value_bound; exact HV. }
  cbn [selection_env selection_parameters fin_match]. split.
  - intros [K [HK [Hsub [Hsup Ey]]]].
    assert (EK : EQ K (relation_candidates B (formula_relation p r) x)).
    { apply INC_EQ.
      - intros z Hz. apply (relation_candidates_spec _ _ (formula_relation_extensional p r)).
        exact (Hsub z Hz).
      - intros z Hz. apply (relation_candidates_spec _ _ (formula_relation_extensional p r)) in Hz.
        apply Hsup; tauto. }
    eapply EQ_tran; [exact Ey | apply apply_set_extensional; [apply EQ_refl | exact EK]].
  - intro Ey. exists (relation_candidates B (formula_relation p r) x).
    split; [apply INC_IN_Power, Comp_INC |]. split.
    + intros z Hz. apply (relation_candidates_spec _ _ (formula_relation_extensional p r)); exact Hz.
    + split; [| exact Ey]. intros z Hz HP.
      apply (relation_candidates_spec _ _ (formula_relation_extensional p r)); auto.
Qed.

Definition formula_selection_graph {n} p (r : Fin n -> Ens) A B c :=
  bounded_formula_graph (selection_certificate p) (selection_parameters B c r) A B.

Lemma selected_formula_member {n} p (r : Fin n -> Ens) B c x :
  subset_choice B c -> (exists y, IN y B /\ formula_relation p r x y) ->
  IN (apply_set c (relation_candidates B (formula_relation p r) x)) B /\
  formula_relation p r x (apply_set c (relation_candidates B (formula_relation p r) x)).
Proof.
  intros HC [y Hy]. apply (relation_candidates_spec _ _ (formula_relation_extensional p r)).
  apply HC; [apply INC_IN_Power, Comp_INC |].
  exists y. apply (relation_candidates_spec _ _ (formula_relation_extensional p r)); exact Hy.
Qed.

Theorem formula_selection_graph_typed {n} p (r : Fin n -> Ens) A B c :
  subset_choice B c ->
  (forall x, IN x A -> exists y, IN y B /\ formula_relation p r x y) ->
  IN (formula_selection_graph p r A B c) (dependent_product A (fun _ => B)).
Proof.
  intros HC HT. apply bounded_formula_graph_typed.
  - intros x Hx.
    exists (apply_set c (relation_candidates B (formula_relation p r) x)).
    split; [exact (proj1 (selected_formula_member p r B c x HC (HT x Hx))) |].
    apply selection_certificate_correct, EQ_refl.
  - intros x y z Hx Hy Hz EY EZ.
    apply selection_certificate_correct in EY. apply selection_certificate_correct in EZ.
    eapply EQ_tran; [exact EY | apply EQ_sym; exact EZ].
Qed.

Theorem formula_selection_graph_value {n} p (r : Fin n -> Ens) A B c x :
  subset_choice B c ->
  (forall x, IN x A -> exists y, IN y B /\ formula_relation p r x y) -> IN x A ->
  EQ (apply_set (formula_selection_graph p r A B c) x)
    (apply_set c (relation_candidates B (formula_relation p r) x)).
Proof.
  intros HC HT Hx.
  pose proof (apply_set_spec A (fun _ => B) _ x
    (formula_selection_graph_typed p r A B c HC HT) Hx) as HA.
  apply bounded_formula_graph_spec in HA as [_ [_ HP]].
  apply selection_certificate_correct; exact HP.
Qed.

Theorem bounded_formula_set_choice (AC : family_choice) {n} p (r : Fin n -> Ens) A B :
  (forall x, IN x A -> exists y, IN y B /\ formula_relation p r x y) ->
  exists g, IN g (dependent_product A (fun _ => B)) /\
    forall x, IN x A -> formula_relation p r x (apply_set g x).
Proof.
  intro HT. destruct (subset_choice_from_family_choice AC B) as [c HC].
  exists (formula_selection_graph p r A B c). split.
  - apply formula_selection_graph_typed; assumption.
  - intros x Hx. pose proof (selected_formula_member p r B c x HC (HT x Hx)) as [_ HP].
    apply (proj2 (formula_relation_extensional p r x x _ _ (EQ_refl x)
      (formula_selection_graph_value p r A B c x HC HT Hx))); exact HP.
Qed.

Print Assumptions selection_lift_correct.
Print Assumptions selection_certificate_correct.
Print Assumptions selected_formula_member.
Print Assumptions formula_selection_graph_typed.
Print Assumptions formula_selection_graph_value.
Print Assumptions bounded_formula_set_choice.
