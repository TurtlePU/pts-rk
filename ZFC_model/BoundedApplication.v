(** Bounded formulas for the actual union-of-fiber application, including
    nonfunctional and empty graphs. This is a predicate certificate, not a
    first-order BZC interpretation of the complete Ens development. *)
From ZFC Require Import Sets Axioms Cartesian.
From PTSrk Require Import Syntax.
From PTSrkModel Require Import SetFunctions SetApplication BoundedFormulas.
Import Bounded.

Definition applyValueF {n} (W g x y : Fin n) : Formula n :=
  conj
    (all y (ex (fsucc W)
      (conj (applicationF (fsucc (fsucc g)) (fsucc (fsucc x)) fzero)
        (member (fsucc fzero) fzero))))
    (all W (impl (applicationF (fsucc g) (fsucc x) fzero)
      (all fzero (member fzero (fsucc (fsucc y)))))).

Theorem apply_value_formula_correct {n} (r : Fin n -> Ens) W g x y :
  (forall v, application (r g) (r x) v -> IN v (r W)) ->
  (holds (applyValueF W g x y) r <-> EQ (r y) (apply_set (r g) (r x))).
Proof.
  intro HB. unfold applyValueF. cbn [holds].
  setoid_rewrite application_correct. cbn [fin_match]. split.
  - intros [HY HW]. apply INC_EQ.
    + intros z Hz. destruct (HY z Hz) as [v [Hv [Happ Hzv]]].
      apply (IN_Union (value_fiber (r g) (r x)) v z);
        [apply value_fiber_spec; exact Happ | exact Hzv].
    + intros z Hz. destruct (Union_IN (value_fiber (r g) (r x)) z Hz)
        as [v [Hv Hzv]].
      apply value_fiber_spec in Hv. exact (HW v (HB v Hv) Hv z Hzv).
  - intro E. split.
    + intros z Hz.
      pose proof (IN_sound_right z _ _ E Hz) as Hz'.
      destruct (Union_IN (value_fiber (r g) (r x)) z Hz') as [v [Hv Hzv]].
      apply value_fiber_spec in Hv. exists v; split; [apply HB; exact Hv | auto].
    + intros v Hv Happ z Hzv. apply (IN_sound_right z _ _ (EQ_sym _ _ E)).
      apply (IN_Union (value_fiber (r g) (r x)) v z);
        [apply value_fiber_spec; exact Happ | exact Hzv].
Qed.

Definition application_env (g x y : Ens) :=
  fin_match g (fin_match x (fin_match y (fun i : Fin 0 => match i with end))).
Definition fiber_certificate : Formula 3 :=
  applicationF fzero (fsucc fzero) (fsucc (fsucc fzero)).
Definition value_fiber_by_formula g x :=
  Comp (value_bound g) (fun y => holds fiber_certificate (application_env g x y)).

Theorem fiber_certificate_correct g x y :
  holds fiber_certificate (application_env g x y) <-> application g x y.
Proof. apply application_correct. Qed.

Theorem value_fiber_bounded_separation g x :
  EQ (value_fiber g x) (value_fiber_by_formula g x).
Proof.
  assert (HE : forall y z,
    holds fiber_certificate (application_env g x y) -> EQ y z ->
    holds fiber_certificate (application_env g x z)).
  { intros y z Hy E. apply fiber_certificate_correct in Hy.
    apply fiber_certificate_correct.
    eapply application_arguments; [apply EQ_refl | apply EQ_refl | exact E | exact Hy]. }
  apply INC_EQ.
  - intros y Hy. apply value_fiber_spec in Hy. apply IN_P_Comp.
    + exact HE.
    + eapply application_value_bound; exact Hy.
    + apply fiber_certificate_correct; exact Hy.
  - intros y Hy. apply value_fiber_spec, fiber_certificate_correct.
    exact (IN_Comp_P _ _ _ HE Hy).
Qed.

Theorem apply_set_bounded_separation g x :
  EQ (apply_set g x) (Union (value_fiber_by_formula g x)).
Proof. apply Union_sound, value_fiber_bounded_separation. Qed.

Definition apply_value_env W g x y :=
  fin_match W (application_env g x y).
Definition apply_value_certificate : Formula 4 :=
  applyValueF fzero (fsucc fzero) (fsucc (fsucc fzero))
    (fsucc (fsucc (fsucc fzero))).
Theorem apply_value_certificate_correct g x y :
  holds apply_value_certificate (apply_value_env (value_bound g) g x y) <->
  EQ y (apply_set g x).
Proof. apply apply_value_formula_correct. apply application_value_bound. Qed.

Print Assumptions apply_value_formula_correct.
Print Assumptions fiber_certificate_correct.
Print Assumptions value_fiber_bounded_separation.
Print Assumptions apply_set_bounded_separation.
Print Assumptions apply_value_certificate_correct.
