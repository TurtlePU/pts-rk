From Stdlib Require Import Lists.List Arith.PeanoNat.
Import ListNotations.

(** A precise boundary on fixed finite models.  This file concerns TOTAL,
    UNTYPED application with the universal K EQUATION.  It does not concern
    a rank-indexed/partial application operation, or the directed [red]
    predicate of CombinatoryPTS-rk.mm0.  In particular, the result below is
    not an impossibility theorem for finite models of that Horn signature. *)
Module EquationalBoundary.

Section FiniteMaps.
Context {A : Type}.
Variable enumeration : list A.
Hypothesis enumeration_nodup : NoDup enumeration.
Hypothesis enumeration_complete : forall x, In x enumeration.

Lemma injective_map_nodup (f : A -> A)
  (injective : forall x y, f x = f y -> x = y) :
  forall xs, NoDup xs -> NoDup (map f xs).
Proof.
  intros xs H; induction H as [|x xs Hnot Hnd IH]; simpl.
  - constructor.
  - constructor; [|exact IH].
    intros Hin; apply in_map_iff in Hin.
    destruct Hin as [y [Heq Hy]].
    apply injective in Heq; subst; contradiction.
Qed.

Lemma finite_injective_surjective (f : A -> A)
  (injective : forall x y, f x = f y -> x = y) :
  forall y, exists x, f x = y.
Proof.
  assert (Hincl : incl (map f enumeration) enumeration).
  { intros y _; apply enumeration_complete. }
  assert (Hreverse : incl enumeration (map f enumeration)).
  { apply NoDup_length_incl.
    - apply injective_map_nodup; assumption.
    - rewrite length_map; reflexivity.
    - exact Hincl. }
  intro y; specialize (Hreverse y (enumeration_complete y)).
  apply in_map_iff in Hreverse; destruct Hreverse as [x [Heq _]].
  exists x; exact Heq.
Qed.
End FiniteMaps.

Section ApplicativeAlgebra.
Context {A : Type}.
Variable enumeration : list A.
Hypothesis enumeration_nodup : NoDup enumeration.
Hypothesis enumeration_complete : forall x, In x enumeration.
Variable app : A -> A -> A.
Variable k : A.
Hypothesis k_equation : forall x y, app (app k x) y = x.

Lemma k_embedding_injective :
  forall x y, app k x = app k y -> x = y.
Proof.
  intros x y H.
  pose proof (f_equal (fun f => app f k) H) as Happly.
  cbn in Happly.
  now rewrite !k_equation in Happly.
Qed.

(** K alone already forces infinitude of a nontrivial total equational
    applicative algebra; neither extensionality nor other combinators are
    needed.  The proof uses only constructive finite-list facts. *)
Theorem finite_k_algebra_trivial : forall x y : A, x = y.
Proof.
  destruct (finite_injective_surjective enumeration enumeration_nodup
    enumeration_complete (app k) k_embedding_injective k) as [a Ha].
  assert (Hconstant : forall x, app k x = a).
  { intro x; rewrite <- Ha at 1; apply k_equation. }
  intros x y; apply k_embedding_injective.
  rewrite !Hconstant; reflexivity.
Qed.

(** A positive typing fact plus an empty Void fibre is therefore incompatible
    with this particular equational semantics on a fixed finite carrier.
    This does not import or modify original PTS typing. *)
Theorem no_finite_void_separating_k_model
  (typing : A -> A -> Prop) (void : A)
  (inhabited : exists t T, typing t T)
  (void_empty : forall t, ~ typing t void) : False.
Proof.
  destruct inhabited as [t [T Ht]].
  apply (void_empty t).
  rewrite <- (finite_k_algebra_trivial T void); exact Ht.
Qed.
End ApplicativeAlgebra.

Print Assumptions finite_injective_surjective.
Print Assumptions k_embedding_injective.
Print Assumptions finite_k_algebra_trivial.
Print Assumptions no_finite_void_separating_k_model.
End EquationalBoundary.
