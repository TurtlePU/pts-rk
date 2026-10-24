(** Scope-polymorphic applications of the EXISTING exact-rank-one Boolean
    predicate transport.  Beta conversion supplies transport in this
    direction; no converse, extensional equality or parametricity is used. *)
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRCheck DirectRStructural.
From PTSrk.SelfConsistency Require Import GuardedTables InternalExecutionGraph.

Module BooleanAgreement.
Import CommonCodes Core Structural.
Module EG := InternalExecutionGraph.InternalExecutionGraph.
Module GT := GuardedTables.GuardedTables.

Definition v1 {n} : Term nat (S (S n)) := var (fsucc fzero).
Definition v2 {n} : Term nat (S (S (S n))) := var (fsucc (fsucc fzero)).
Definition v3 {n} : Term nat (S (S (S (S n)))) := var (fsucc (fsucc (fsucc fzero))).

Definition refl_type : closed_term :=
  Π GT.boolean (EG.same_at V0 V0).
Theorem refl_type_sorted : Typed ε refl_type (𝓤 3).
Proof. RkCheck.certify_with 256. Qed.
Theorem refl_typed : Typed ε EG.same_refl refl_type.
Proof.
  eapply tConv; [exact EG.same_refl_typed |exact refl_type_sorted|].
  apply (RkCheck.check_conv_sound 256); vm_compute; reflexivity.
Qed.

Definition and_type : closed_term :=
  Π GT.boolean (Π (lift_closed GT.boolean)
    (Π (lift_closed GT.boolean) (Π (lift_closed GT.boolean)
      (Arrow (EG.same_at v3 v1) (Arrow (EG.same_at v2 V0)
        (EG.same_at (EG.and_at v3 v2) (EG.and_at v1 V0))))))).
Theorem and_type_sorted : Typed ε and_type (𝓤 4).
Proof. RkCheck.certify_with 256. Qed.
Theorem and_typed : Typed ε EG.same_and and_type.
Proof.
  eapply tConv; [exact EG.same_and_typed |exact and_type_sorted|].
  apply (RkCheck.check_conv_sound 256); vm_compute; reflexivity.
Qed.

Lemma same_application {n} (G : Ctx nat n) b c :
  Typed G b (lift_closed GT.boolean) -> Typed G c (lift_closed GT.boolean) ->
  Typed G (EG.same_at b c) (𝓤 3).
Proof.
  intros Hb Hc; pose proof (lift_closed_typed G _ _ EG.same_sorted) as H.
  change (Typed G (lift_closed EG.same)
    (Arrow (lift_closed GT.boolean) (Arrow (lift_closed GT.boolean) (𝓤 3)))) in H.
  unfold EG.same_at; eapply arrow_application; [|exact Hc].
  eapply arrow_application; [exact H|exact Hb].
Qed.

Lemma same_refl_application {n} (G : Ctx nat n) b :
  Typed G b (lift_closed GT.boolean) ->
  Typed G (app (lift_closed EG.same_refl) b) (EG.same_at b b).
Proof.
  intro Hb; pose proof (lift_closed_typed G _ _ refl_typed) as H.
  change (Typed G (lift_closed EG.same_refl)
    (Π (lift_closed GT.boolean) (EG.same_at V0 V0))) in H.
  pose proof (tApp H Hb) as K; unfold EG.same_at in K; structural_substitution_in K; exact K.
Qed.

Lemma same_from_beta {n} (G : Ctx nat n) b c :
  Typed G b (lift_closed GT.boolean) -> Typed G c (lift_closed GT.boolean) -> b =ᵝ c ->
  Typed G (app (lift_closed EG.same_refl) b) (EG.same_at b c).
Proof.
  intros Hb Hc Hbc; eapply tConv;
    [apply same_refl_application, Hb |apply same_application; assumption|].
  unfold EG.same_at; apply beta_app; [reflexivity|exact Hbc].
Qed.

Lemma same_and_application {n} (G : Ctx nat n) b c d e h k :
  Typed G b (lift_closed GT.boolean) -> Typed G c (lift_closed GT.boolean) ->
  Typed G d (lift_closed GT.boolean) -> Typed G e (lift_closed GT.boolean) ->
  Typed G h (EG.same_at b d) -> Typed G k (EG.same_at c e) ->
  Typed G (app (app (app (app (app (app (lift_closed EG.same_and) b) c) d) e) h) k)
    (EG.same_at (EG.and_at b c) (EG.and_at d e)).
Proof.
  intros Hb Hc Hd He Hh Hk; pose proof (lift_closed_typed G _ _ and_typed) as H.
  change (Typed G (lift_closed EG.same_and)
    (Π (lift_closed GT.boolean) (Π (lift_closed GT.boolean)
      (Π (lift_closed GT.boolean) (Π (lift_closed GT.boolean)
        (Arrow (EG.same_at v3 v1) (Arrow (EG.same_at v2 V0)
          (EG.same_at (EG.and_at v3 v2) (EG.and_at v1 V0))))))))) in H.
  pose proof (tApp H Hb) as H1.
  unfold EG.same_at, EG.and_at, v1, v2, v3 in H1; structural_substitution_in H1.
  pose proof (tApp H1 Hc) as H2; structural_substitution_in H2.
  pose proof (tApp H2 Hd) as H3; structural_substitution_in H3.
  pose proof (tApp H3 He) as H4; structural_substitution_in H4.
  eapply arrow_application; [|exact Hk].
  eapply arrow_application; [exact H4|exact Hh].
Qed.

End BooleanAgreement.
