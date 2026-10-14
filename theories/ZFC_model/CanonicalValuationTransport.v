(** Structural transport of canonical valuations when corresponding
    declarations have actual canonical denotations at the SAME value.
    This is the local evidence supplied by a prospective normalization
    induction, not an assumed semantic-conversion or validity theorem.

    Syntactic context morphisms are kept separate: together with the proved
    valuation transport they transport existing body certificates. No
    normalization, totality, or original model soundness is asserted. *)
From Equations Require Import Equations.
From ZFC Require Import Sets Axioms.
From PTSrk Require Import Syntax Context Typing Ranks.
From PTSrkModel Require Import CodeUniverses CardinalHierarchy ContextTransport
  CanonicalDenotation CanonicalRealization CanonicalContext.
Import CodeUniverses.CodeUniverses.

Module CanonicalValuationTransport.
Module CD := CanonicalDenotation.CanonicalDenotation.
Module CR := CanonicalRealization.CanonicalRealization.
Module CC := CanonicalContext.CanonicalContext.

Section Transport.
Variables H s : Ens.

Lemma valid_cons_at_value n (G : Ctx nat n) (rho : Fin (S n) -> Ens) A a :
  CD.denotes H s n G (fun i => rho (fsucc i)) A a ->
  (CR.valid_valuation H s (G & A) rho <->
    CR.valid_valuation H s G (fun i => rho (fsucc i)) /\
    IN (rho fzero) (decode a)).
Proof.
  intro DA; split.
  - intros [HV [b [DB Hx]]]. split; [exact HV |].
    eapply IN_sound_right; [apply decoding_extensional;
      eapply CD.coherent; [exact DB | exact DA] | exact Hx].
  - intros [HV Hx]; split; [exact HV | exists a; auto].
Qed.

Theorem same_value_binder_validity n (G : Ctx nat n)
  (rho : Fin (S n) -> Ens) A B a :
  CD.denotes H s n G (fun i => rho (fsucc i)) A a ->
  CD.denotes H s n G (fun i => rho (fsucc i)) B a ->
  (CR.valid_valuation H s (G & A) rho <-> CR.valid_valuation H s (G & B) rho).
Proof.
  intros DA DB.
  rewrite (valid_cons_at_value n G rho A a DA), (valid_cons_at_value n G rho B a DB).
  reflexivity.
Qed.

(** Each extension contains paired declaration witnesses, quantified over
    valid SOURCE-tail valuations. The target-tail validity needed to use
    these witnesses is obtained by induction, never supplied as a premise. *)
Inductive corresponding_contexts : forall n, Ctx nat n -> Ctx nat n -> Prop :=
| corresponding_empty : corresponding_contexts 0 ε ε
| corresponding_cons n (G D : Ctx nat n) A B :
    corresponding_contexts n G D ->
    (forall rho, CR.valid_valuation H s G rho -> exists a,
      CD.denotes H s n G rho A a /\ CD.denotes H s n D rho B a) ->
    corresponding_contexts (S n) (G & A) (D & B).

Theorem corresponding_validity n (G D : Ctx nat n) :
  corresponding_contexts n G D -> forall rho,
  CR.valid_valuation H s G rho <-> CR.valid_valuation H s D rho.
Proof.
  intro HC; induction HC as [| n G D A B HC IH HD]; intro rho.
  - reflexivity.
  - split; intro HV.
    + pose proof (proj1 HV) as HG.
      destruct (HD (fun i => rho (fsucc i)) HG) as [a [DA DB]].
      apply (proj2 (valid_cons_at_value n D rho B a DB)).
      apply (proj1 (valid_cons_at_value n G rho A a DA)) in HV.
      split; [apply (proj1 (IH _)); exact HG | exact (proj2 HV)].
    + assert (HG : CR.valid_valuation H s G (fun i => rho (fsucc i))).
      { apply (proj2 (IH _)); exact (proj1 HV). }
      destruct (HD (fun i => rho (fsucc i)) HG) as [a [DA DB]].
      apply (proj2 (valid_cons_at_value n G rho A a DA)).
      apply (proj1 (valid_cons_at_value n D rho B a DB)) in HV.
      split; [exact HG | exact (proj2 HV)].
Qed.

Theorem corresponding_contexts_symmetric n (G D : Ctx nat n) :
  corresponding_contexts n G D -> corresponding_contexts n D G.
Proof.
  intro HC; induction HC as [| n G D A B HC IH HD]; constructor; [exact IH |].
  intros rho HV. apply (proj2 (corresponding_validity n G D HC rho)) in HV.
  destruct (HD rho HV) as [a [DA DB]]; exists a; auto.
Qed.

Theorem corresponding_contexts_transitive n (G D E : Ctx nat n) :
  corresponding_contexts n G D -> corresponding_contexts n D E ->
  corresponding_contexts n G E.
Proof.
  intros HGD; revert E.
  induction HGD as [| n G D A B HC IH HD]; intros E HDE.
  - dependent elimination HDE; constructor.
  - dependent elimination HDE. constructor.
    + eapply IH; eassumption.
    + intros rho HV. destruct (HD rho HV) as [a [DA DB]].
      pose proof (proj1 (corresponding_validity _ _ _ HC rho) HV) as VD.
      destruct (e rho VD) as [b [DB' DE]].
      exists a; split; [exact DA |].
      eapply CD.denotes_equal; [exact DE |].
      eapply CD.coherent; [exact DB' | exact DB].
Qed.

Theorem corresponding_environment_transport n (G D : Ctx nat n) rho t v :
  corresponding_contexts n G D -> context_typing_morphism G D ->
  CR.valid_valuation H s G rho -> CD.denotes H s n G rho t v ->
  CR.valid_valuation H s D rho /\ CD.denotes H s n D rho t v.
Proof.
  intros HC HM HV Dt; split.
  - apply (proj1 (corresponding_validity n G D HC rho)); exact HV.
  - eapply CC.denotes_context_transport; eassumption.
Qed.
End Transport.
End CanonicalValuationTransport.

Print Assumptions CanonicalValuationTransport.valid_cons_at_value.
Print Assumptions CanonicalValuationTransport.same_value_binder_validity.
Print Assumptions CanonicalValuationTransport.corresponding_validity.
Print Assumptions CanonicalValuationTransport.corresponding_contexts_symmetric.
Print Assumptions CanonicalValuationTransport.corresponding_contexts_transitive.
Print Assumptions CanonicalValuationTransport.corresponding_environment_transport.
