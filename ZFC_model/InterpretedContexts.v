(** Context validity follows context structure, not the soundness conclusion. *)
From Equations Require Import Equations.
From ZFC Require Import Sets Axioms.
From PTSrk Require Import Syntax Context Typing Ranks.
From PTSrkModel Require Import CodeUniverses CardinalHierarchy Denotation.
Import CodeUniverses.CodeUniverses.

Section Contexts.
Variables H s : Ens.

Fixpoint valid_valuation {n} (G : Ctx nat n) : (Fin n -> Ens) -> Prop :=
  match G in Ctx _ k return (Fin k -> Ens) -> Prop with
  | ε => fun _ => True
  | @cons _ k D A => fun rho =>
      valid_valuation D (fun i => rho (fsucc i)) /\
      exists a, denotes H s k D (fun i => rho (fsucc i)) A a /\
        IN (rho fzero) (decode a)
  end.

Lemma valid_valuation_extend n (G : Ctx nat n) rho A a x :
  valid_valuation G rho -> denotes H s n G rho A a -> IN x (decode a) ->
  valid_valuation (G & A) (fin_match x rho).
Proof. intros HV HA Hx; split; [exact HV | exists a; auto]. Qed.

Theorem valid_valuation_extensional n (G : Ctx nat n) rho :
  valid_valuation G rho -> forall rho', valuation_eq rho rho' -> valid_valuation G rho'.
Proof.
  induction G; intros HV rho' E; [exact I |].
  destruct HV as [HV [a [HA Hx]]]. split.
  - eapply IHG; [exact HV | intro i; apply E].
  - exists a; split.
    + eapply denotes_valuation_extensional; [exact HA | intro i; apply E].
    + eapply IN_sound_left; [apply E | exact Hx].
Qed.

Lemma denotes_shift_valuation n (G : Ctx nat n) A (rho : Fin (S n) -> Ens) t v :
  denotes H s n G (fun i => rho (fsucc i)) t v ->
  denotes H s (S n) (G & A) rho (shift t) v.
Proof.
  intro HD. eapply denotes_valuation_extensional.
  - exact (denotes_shift H s n G (fun i => rho (fsucc i)) t v A (rho fzero) HD).
  - intro i; dependent elimination i; apply EQ_refl.
Qed.

Theorem valid_valuation_lookup n (G : Ctx nat n) rho : valid_valuation G rho ->
  forall i, exists a, denotes H s n G rho (G !! i) a /\ IN (rho i) (decode a).
Proof.
  induction G; intros HV i; [dependent elimination i |].
  destruct HV as [HV [a [HA Hx]]]. dependent elimination i as [fzero | fsucc j].
  - exists a; split; [apply denotes_shift_valuation; exact HA | exact Hx].
  - destruct (IHG _ HV j) as [b [HB Hi]]. exists b; split.
    + apply denotes_shift_valuation; exact HB.
    + exact Hi.
Qed.

Definition realizes {n} (G : Ctx nat n) rho (t T : Term nat n) :=
  exists v a, denotes H s n G rho t v /\ denotes H s n G rho T a /\ IN v (decode a).

Theorem variable_realization n (G : Ctx nat n) rho i :
  valid_valuation G rho -> realizes G rho (var i) (G !! i).
Proof.
  intro HV. destruct (valid_valuation_lookup n G rho HV i) as [a [HA Hi]].
  exists (rho i), a; split; [apply denotes_var | auto].
Qed.

Theorem sort_realization n (G : Ctx nat n) rho i : realizes G rho (𝓤 i) (𝓤 0).
Proof.
  exists (repr (sort i)), (repr (sort 0)); repeat split;
    try apply denotes_sort; apply concrete_sort_axiom.
Qed.
End Contexts.
Print Assumptions valid_valuation_extensional.
Print Assumptions valid_valuation_lookup.
Print Assumptions variable_realization.
Print Assumptions sort_realization.
