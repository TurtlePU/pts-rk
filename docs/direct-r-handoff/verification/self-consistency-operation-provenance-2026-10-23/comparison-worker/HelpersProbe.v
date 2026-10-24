From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRCheck DirectRStructural.
From PTSrk.SelfConsistency Require Import InternalComparisonGraph NamedTemplates NamedBeta.
Import CommonCodes Core Structural InternalComparisonGraph.InternalComparisonGraph.
Definition trace_at {n} (x y z b : Term nat n) :=
  app (app (app (app (lift_closed trace) x) y) z) b.
Definition v1 {n} : Term nat (S (S n)) := var (fsucc fzero).
Definition v2 {n} : Term nat (S (S (S n))) := var (fsucc (fsucc fzero)).
Definition v3 {n} : Term nat (S (S (S (S n)))) := var (fsucc (fsucc (fsucc fzero))).
Lemma trace_application {n} (G : Ctx nat n) x y z b :
  Typed G x (lift_closed IC.carrier) -> Typed G y (lift_closed IC.carrier) ->
  Typed G z (CMP.zip_at x y) -> Typed G b (lift_closed GT.boolean) ->
  Typed G (trace_at x y z b) (𝓤 6).
Proof.
  intros Hx Hy Hz Hb.
  pose proof (lift_closed_typed G _ _ trace_sorted) as H.
  change (Typed G (lift_closed trace)
    (Π (lift_closed IC.carrier) (Π (lift_closed IC.carrier)
      (Π (CMP.zip_at v1 V0) (Arrow (lift_closed GT.boolean) (𝓤 6)))))) in H.
  pose proof (tApp H Hx) as H1.
  unfold CMP.zip_at, v1, V0 in H1; structural_substitution_in H1.
  pose proof (tApp H1 Hy) as H2; structural_substitution_in H2.
  pose proof (tApp H2 Hz) as H3; structural_substitution_in H3.
  unfold trace_at; eapply arrow_application; [exact H3 |exact Hb].
Qed.
Lemma trace_head_beta {n} (e : NamedTemplates.NamedTemplates.environment n)
    x y z b result :
  NamedTemplates.NamedTemplates.evaluate
    (npis fields (At (NVar 0) (NVar 1) (NVar 2) (NVar 3)))
    (NamedTemplates.NamedTemplates.update
      (NamedTemplates.NamedTemplates.update
        (NamedTemplates.NamedTemplates.update
          (NamedTemplates.NamedTemplates.update e 0 x) 1 y) 2 z) 3 b) = Some result ->
  trace_at x y z b =ᵝ result.
Proof.
  intro H; unfold trace_at.
  eapply NamedBeta.NamedBeta.named_application4_beta.
  - apply NamedTemplates.NamedTemplates.evaluate_close.
  - exact H.
Qed.
