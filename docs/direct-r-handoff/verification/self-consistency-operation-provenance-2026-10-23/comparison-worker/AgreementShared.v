From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq Preservation.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRCheck DirectRStructural.
From PTSrk.SelfConsistency Require Import InternalComparisonGraph InternalJointTraversal HelpersProbe AgreementBase.
Import ListNotations CommonCodes Core Structural InternalComparisonGraph.InternalComparisonGraph.
Module JT := InternalJointTraversal.InternalJointTraversal.
Fixpoint lambda_parts {n} (t : Term nat n) :
  sigT (fun m : nat => (telescope n m * Term nat m)%type) :=
  match t with
  | lam A b => match lambda_parts b with
    | existT _ m (T, u) => existT _ m (tel_cons 0 A T, u)
    end
  | _ => existT _ n (tel_nil, t)
  end.
Definition assembled_or_sort env t :=
  match assemble t env with Some u => u | None => 𝓤 0 end.
Definition agreement_telescope : telescope 0 5 :=
  fst (projT2 (lambda_parts AgreementBase.agreement)).
Definition base_context : Ctx nat 4 :=
  (((ε & IC.carrier) & lift_closed IC.carrier) & CMP.zip_at v1 V0) & lift_closed GT.boolean.
Lemma base_context_wf : @wf nat RankSorts _ base_context.
Proof. apply (RkCheck.check_ctx_sound 512); vm_compute; reflexivity. Qed.
Definition agreement_context := telescope_context agreement_telescope ε.
Lemma agreement_context_wf : @wf nat RankSorts _ agreement_context.
Proof.
  change (@wf nat RankSorts _ (base_context & trace_at v3 v2 v1 V0)).
  eapply wf_cons; [exact base_context_wf |].
  apply trace_application; (apply (RkCheck.check_sound 512);
    [exact base_context_wf | vm_compute; reflexivity]).
Qed.
Definition agreement_body := assembled_or_sort [4;3;2;1;0]
  (napps (NVar 4) ([agree_motive] ++ map agree_atom IC.tags ++ map agree_pair_atom IC.tags ++[agree_pair])).
Definition agreement_result := assembled_or_sort [4;3;2;1;0]
  (Same (Compare (NVar 0) (NVar 1) (NVar 2)) (NVar 3)).
Lemma agreement_body_typed : Typed agreement_context agreement_body agreement_result.
Proof. apply (RkCheck.check_sound 4096); [exact agreement_context_wf | vm_compute; reflexivity]. Qed.
Definition agreement := telescope_abstract agreement_telescope agreement_body.
Theorem agreement_typed : Typed ε agreement AgreementBase.agreement_type.
Proof.
  change (Typed ε (telescope_abstract agreement_telescope agreement_body)
    (telescope_product agreement_telescope agreement_result)).
  apply JT.telescope_abstraction_from_context;
    [exact agreement_context_wf | exact agreement_body_typed].
Qed.
