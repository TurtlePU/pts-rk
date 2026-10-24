From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq Preservation.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRCheck DirectREval DirectRStructural.
From PTSrk.SelfConsistency Require Import StructuralCodes InternalComparisonGraph InternalJointTraversal.
Import ListNotations.
Import CommonCodes Core Structural InternalComparisonGraph.InternalComparisonGraph.
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
Definition atom_template t := close (nlams ([(0,C)]++fields)
  (NApp (NVar (300+IC.tag_number t)) (NVar 0))) (ltac:(destruct t; reflexivity)).
Definition atom_env := rev (map fst fields)++[0].
Definition atom_telescope : telescope 0 (length atom_env) :=
  fst (projT2 (lambda_parts (atom_template NZero))).
Definition atom_context := telescope_context atom_telescope ε.
Definition atom_body t := assembled_or_sort atom_env (NApp (NVar (300+IC.tag_number t)) (NVar 0)).
Definition atom_result t := assembled_or_sort atom_env
  (At (NClosed (IC.atom t)) (NVar 0) (AtomZip t (NVar 0)) (Test t (NVar 0))).
Lemma atom_context_wf : @wf nat RankSorts _ atom_context.
Proof. apply (RkCheck.check_ctx_sound 2048); vm_compute; reflexivity. Qed.
Lemma atom_body_typed t : Typed atom_context (atom_body t) (atom_result t).
Proof. destruct t; (apply (RkCheck.infer_sound 512); [exact atom_context_wf | vm_compute; reflexivity]). Qed.
Definition atom_trace t := telescope_abstract atom_telescope (atom_body t).
Definition atom_trace_type t := telescope_product atom_telescope (atom_result t).
Theorem atom_trace_typed t : Typed ε (atom_trace t) (atom_trace_type t).
Proof. unfold atom_trace, atom_trace_type; apply JT.telescope_abstraction_from_context;
  [exact atom_context_wf |apply atom_body_typed]. Qed.

Definition pair_atom_template t := close (nlams ([(0,C);(1,C)]++fields)
  (napps (NVar (400+IC.tag_number t)) [NVar 0;NVar 1])) (ltac:(destruct t; reflexivity)).
Definition pair_atom_env := rev (map fst fields)++[1;0].
Definition pair_atom_telescope : telescope 0 (length pair_atom_env) :=
  fst (projT2 (lambda_parts (pair_atom_template NZero))).
Definition pair_atom_context := telescope_context pair_atom_telescope ε.
Definition pair_atom_body t := assembled_or_sort pair_atom_env
  (napps (NVar (400+IC.tag_number t)) [NVar 0;NVar 1]).
Definition pair_atom_result t := assembled_or_sort pair_atom_env
  (At (Pair (NVar 0) (NVar 1)) (NClosed (IC.atom t))
    (PairAtomZip t (NVar 0) (NVar 1)) (NClosed (GT.point false))).
Lemma pair_atom_context_wf : @wf nat RankSorts _ pair_atom_context.
Proof. apply (RkCheck.check_ctx_sound 2048); vm_compute; reflexivity. Qed.
Lemma pair_atom_body_typed t : Typed pair_atom_context (pair_atom_body t) (pair_atom_result t).
Proof. destruct t; (apply (RkCheck.infer_sound 512); [exact pair_atom_context_wf | vm_compute; reflexivity]). Qed.
Definition pair_atom_trace t := telescope_abstract pair_atom_telescope (pair_atom_body t).
Definition pair_atom_trace_type t := telescope_product pair_atom_telescope (pair_atom_result t).
Theorem pair_atom_trace_typed t : Typed ε (pair_atom_trace t) (pair_atom_trace_type t).
Proof. unfold pair_atom_trace, pair_atom_trace_type; apply JT.telescope_abstraction_from_context;
  [exact pair_atom_context_wf |apply pair_atom_body_typed]. Qed.
