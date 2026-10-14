(** Formula-defined bounded graphs by separation, without a choice or
    replacement premise. This does not supply the defining formula for
    every native Ens function, in particular the current decoder. *)
From Equations Require Import Equations.
From ZFC Require Import Sets Axioms Cartesian.
From PTSrk Require Import Syntax.
From PTSrkModel Require Import SetFunctions SetApplication SetBijections BoundedFormulas
  BoundedFormulaTransport.
Import Bounded.

Definition graph_env {n} (r : Fin n -> Ens) A B e :=
  fin_match e (fin_match A (fin_match B r)).
Definition graph_lift {n} : Fin (S (S n)) -> Fin (S (S (S (S (S n))))) :=
  weak (weak (fun i : Fin n => fsucc (fsucc (fsucc i)))).
Definition graph_certificate {n} (p : Formula (S (S n))) : Formula (S (S (S n))) :=
  ex (fsucc fzero) (ex (fsucc (fsucc (fsucc fzero)))
    (conj (coupleF (fsucc (fsucc fzero)) (fsucc fzero) fzero)
      (rename_formula graph_lift p))).

Lemma graph_lift_correct {n} p (r : Fin n -> Ens) A B e x y :
  holds (rename_formula graph_lift p) (fin_match y (fin_match x (graph_env r A B e))) <->
  holds p (fin_match y (fin_match x r)).
Proof.
  rewrite holds_rename. apply holds_extensional.
  intro i; dependent elimination i as [fzero | fsucc i]; [apply EQ_refl |].
  dependent elimination i; apply EQ_refl.
Qed.

Theorem graph_certificate_correct {n} p (r : Fin n -> Ens) A B e :
  holds (graph_certificate p) (graph_env r A B e) <->
  exists x, IN x A /\ exists y, IN y B /\
    EQ e (Couple x y) /\ holds p (fin_match y (fin_match x r)).
Proof.
  unfold graph_certificate. cbn [holds].
  setoid_rewrite couple_correct. setoid_rewrite graph_lift_correct. reflexivity.
Qed.

Lemma graph_certificate_extensional {n} p (r : Fin n -> Ens) A B e e' :
  holds (graph_certificate p) (graph_env r A B e) -> EQ e e' ->
  holds (graph_certificate p) (graph_env r A B e').
Proof.
  intros H E.
  assert (ER : forall i, EQ (graph_env r A B e i) (graph_env r A B e' i)).
  { intro i; dependent elimination i; [exact E | apply EQ_refl]. }
  exact (proj1 (holds_extensional (graph_certificate p) _ _ ER) H).
Qed.

Definition bounded_formula_graph {n} p (r : Fin n -> Ens) A B :=
  Comp (Prod A B) (fun e => holds (graph_certificate p) (graph_env r A B e)).

Theorem bounded_formula_graph_spec {n} p (r : Fin n -> Ens) A B x y :
  application (bounded_formula_graph p r A B) x y <->
    IN x A /\ IN y B /\ holds p (fin_match y (fin_match x r)).
Proof.
  split.
  - intro H.
    pose proof (IN_Comp_P _ _ _ (graph_certificate_extensional p r A B) H) as HP.
    apply graph_certificate_correct in HP as [u [Hu [v [Hv [E HP]]]]].
    pose proof (Couple_inj_left _ _ _ _ E) as Ex.
    pose proof (Couple_inj_right _ _ _ _ E) as Ey.
    split; [exact (IN_sound_left u x A (EQ_sym _ _ Ex) Hu) |].
    split; [exact (IN_sound_left v y B (EQ_sym _ _ Ey) Hv) |].
    assert (ER : forall i, EQ (fin_match y (fin_match x r) i)
      (fin_match v (fin_match u r) i)).
    { intro i; dependent elimination i as [fzero | fsucc i]; [exact Ey |].
      dependent elimination i; [exact Ex | apply EQ_refl]. }
    exact (proj2 (holds_extensional p _ _ ER) HP).
  - intros [Hx [Hy HP]]. apply IN_P_Comp.
    + apply graph_certificate_extensional.
    + apply Couple_IN_Prod; assumption.
    + apply graph_certificate_correct. exists x; split; [exact Hx |].
      exists y; split; [exact Hy |]. split; [apply EQ_refl | exact HP].
Qed.

Theorem bounded_formula_graph_agrees {n} p (r : Fin n -> Ens) A B f :
  family_extensional f -> (forall x, IN x A -> IN (f x) B) ->
  (forall x y, IN x A -> IN y B ->
    (holds p (fin_match y (fin_match x r)) <-> EQ y (f x))) ->
  EQ (bounded_formula_graph p r A B) (graph A f).
Proof.
  intros EF HB HP. apply INC_EQ.
  - intros e He.
    pose proof (IN_Comp_P _ _ _ (graph_certificate_extensional p r A B) He) as H.
    apply graph_certificate_correct in H as [x [Hx [y [Hy [E H]]]]].
    apply (IN_sound_left (Couple x y) e _ (EQ_sym _ _ E)).
    apply graph_application_unique; [exact EF | exact Hx |].
    apply (proj1 (HP x y Hx Hy)); exact H.
  - intros e [i E].
    apply (IN_sound_left (Couple (pi2 A i) (f (pi2 A i))) e _ (EQ_sym _ _ E)).
    apply bounded_formula_graph_spec. split; [apply index_member |].
    split; [apply HB, index_member |].
    apply (proj2 (HP _ _ (index_member A i) (HB _ (index_member A i)))); apply EQ_refl.
Qed.

Print Assumptions graph_lift_correct.
Print Assumptions graph_certificate_correct.
Print Assumptions bounded_formula_graph_spec.
Print Assumptions bounded_formula_graph_agrees.

Theorem bounded_formula_graph_typed {n} p (r : Fin n -> Ens) A B :
  (forall x, IN x A -> exists y, IN y B /\ holds p (fin_match y (fin_match x r))) ->
  (forall x y z, IN x A -> IN y B -> IN z B ->
    holds p (fin_match y (fin_match x r)) ->
    holds p (fin_match z (fin_match x r)) -> EQ y z) ->
  IN (bounded_formula_graph p r A B) (dependent_product A (fun _ => B)).
Proof.
  intros HT HU. apply bounded_function_member; [apply Comp_INC |]. split.
  - intros x Hx. destruct (HT x Hx) as [y [Hy HP]]. exists y.
    apply bounded_formula_graph_spec; auto.
  - split.
    + intros x y H. apply bounded_formula_graph_spec in H; tauto.
    + intros x y z H J.
      apply bounded_formula_graph_spec in H as [Hx [Hy HP]].
      apply bounded_formula_graph_spec in J as [_ [Hz HQ]].
      exact (HU x y z Hx Hy Hz HP HQ).
Qed.

Theorem bounded_formula_function {n} p (r : Fin n -> Ens) A B :
  (forall x, IN x A -> exists y, IN y B /\ holds p (fin_match y (fin_match x r))) ->
  (forall x y z, IN x A -> IN y B -> IN z B ->
    holds p (fin_match y (fin_match x r)) ->
    holds p (fin_match z (fin_match x r)) -> EQ y z) ->
  exists g, IN g (dependent_product A (fun _ => B)) /\
    forall x, IN x A -> holds p (fin_match (apply_set g x) (fin_match x r)).
Proof.
  intros HT HU.
  pose proof (bounded_formula_graph_typed p r A B HT HU) as HG.
  exists (bounded_formula_graph p r A B). split; [exact HG |].
  intros x Hx. pose proof (apply_set_spec A (fun _ => B) _ x HG Hx) as H.
  apply bounded_formula_graph_spec in H; tauto.
Qed.
Print Assumptions bounded_formula_graph_typed.
Print Assumptions bounded_formula_function.
