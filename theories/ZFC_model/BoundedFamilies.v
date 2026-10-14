(** Bounded reconstruction of the range of a set-coded family. No arbitrary
    Ens -> Ens parameter or indexed sup occurs in the reconstructed range.
    Equivalence with the earlier indexed construction is proved below. *)
From ZFC Require Import Sets Axioms Cartesian.
From PTSrk Require Import Syntax.
From PTSrkModel Require Import SetFunctions SetApplication BoundedFormulas.
Import Bounded.

Definition rangeF {n} (A f y : Fin n) :=
  ex A (applicationF (fsucc f) fzero (fsucc y)).
Definition range_predicate A f y := exists x, IN x A /\ application f x y.
Lemma range_formula_correct {n} (r : Fin n -> Ens) A f y :
  holds (rangeF A f y) r <-> range_predicate (r A) (r f) (r y).
Proof.
  unfold rangeF, range_predicate. cbn [holds].
  setoid_rewrite application_correct. reflexivity.
Qed.
Definition range_env (A f y : Ens) :=
  fin_match A (fin_match f (fin_match y (fun i : Fin 0 => match i with end))).
Definition range_certificate : Formula 3 :=
  rangeF fzero (fsucc fzero) (fsucc (fsucc fzero)).
Lemma range_certificate_correct A f y :
  holds range_certificate (range_env A f y) <-> range_predicate A f y.
Proof. apply range_formula_correct. Qed.
Lemma range_predicate_extensional A f y z :
  range_predicate A f y -> EQ y z -> range_predicate A f z.
Proof.
  intros [x [Hx Hxy]] E. exists x; split; [exact Hx |].
  eapply application_arguments; [apply EQ_refl | apply EQ_refl | exact E | exact Hxy].
Qed.
Lemma range_certificate_extensional A f y z :
  holds range_certificate (range_env A f y) -> EQ y z ->
  holds range_certificate (range_env A f z).
Proof.
  rewrite !range_certificate_correct. apply range_predicate_extensional.
Qed.

(** The supplied bound W bounds the elements of every fiber. The formula
    defining the range uses only A, f and its candidate member. *)
Definition bounded_family_range W A f :=
  Comp (Power W) (fun y => holds range_certificate (range_env A f y)).
Theorem bounded_family_range_spec W A f y :
  IN y (bounded_family_range W A f) <->
  IN y (Power W) /\ exists x, IN x A /\ application f x y.
Proof.
  split.
  - intro Hy. split; [exact (Comp_INC _ _ _ Hy) |].
    apply range_certificate_correct.
    exact (IN_Comp_P _ _ _ (range_certificate_extensional A f) Hy).
  - intros [Hy Hp]. apply IN_P_Comp.
    + apply range_certificate_extensional.
    + exact Hy.
    + apply range_certificate_correct; exact Hp.
Qed.

Theorem bounded_family_range_equivalence W A f :
  IN f (dependent_product A (fun _ => Power W)) ->
  EQ (bounded_family_range W A f) (family_range A (apply_set f)).
Proof.
  intro Hf. apply INC_EQ.
  - intros y Hy. apply bounded_family_range_spec in Hy as [_ [x [Hx Hxy]]].
    destruct (dependent_product_elimination _ _ _ Hf) as [_ [_ HU]].
    assert (Ey : EQ (apply_set f x) y).
    { apply apply_set_value; [exact Hxy | intros z Hz; exact (HU x z y Hz Hxy)]. }
    destruct (IN_EXType A x Hx) as [i Ex]. exists i.
    eapply EQ_tran; [apply EQ_sym; exact Ey |].
    apply apply_set_extensional; [apply EQ_refl | exact Ex].
  - intros y [i E]. apply bounded_family_range_spec. split.
    + apply (IN_sound_left (apply_set f (pi2 A i)) y _ (EQ_sym _ _ E)).
      apply (apply_set_typed A (fun _ => Power W)); [exact Hf | apply index_member].
    + exists (pi2 A i). split; [apply index_member |].
      eapply application_arguments; [apply EQ_refl | apply EQ_refl | apply EQ_sym; exact E |].
      apply (apply_set_spec A (fun _ => Power W)); [exact Hf | apply index_member].
Qed.

Theorem bounded_family_range_bound W A f :
  IN (bounded_family_range W A f) (Power (Power W)).
Proof. apply INC_IN_Power, Comp_INC. Qed.

Theorem bounded_family_union_bound W A f :
  INC (Union (bounded_family_range W A f)) W.
Proof.
  intros y Hy. destruct (Union_IN _ _ Hy) as [X [HX HyX]].
  apply bounded_family_range_spec in HX as [HX _].
  exact (IN_Power_INC W X HX y HyX).
Qed.

Print Assumptions range_formula_correct.
Print Assumptions bounded_family_range_spec.
Print Assumptions bounded_family_range_equivalence.
Print Assumptions bounded_family_range_bound.
Print Assumptions bounded_family_union_bound.
Check bounded_family_range_equivalence.
