From Stdlib Require Import Lists.List.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel.
From PTSrk.SelfConsistency Require Import NamedTemplates.
Import ListNotations CommonCodes Core.
Print Implicit NamedTemplates.NamedTemplates.evaluate_close.
Lemma probe (c : closed_term) :
  assemble (NClosed c) [99;98] = Some (@lift_closed 2 c).
Proof.
  pose proof (NamedTemplates.NamedTemplates.evaluate_close
    (NClosed c) eq_refl 2
    (NamedTemplates.NamedTemplates.names [99;98])) as E.
  match type of E with ?T => idtac T end.
  pose proof (eq_trans
    (NamedTemplates.NamedTemplates.assemble_evaluate (NClosed c) [99;98]) E) as H.
  exact H.
Qed.
