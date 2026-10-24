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
Definition atom_head t := assembled_or_sort atom_env (NVar (300+IC.tag_number t)).
Definition atom_head_type t := assembled_or_sort atom_env (atom_case t).
Definition atom_index t : Fin (length atom_env) :=
  match lookup atom_env (300+IC.tag_number t) with Some i => i | None => fzero end.
Definition atom_input := assembled_or_sort atom_env (NVar 0).
Definition atom_body t := assembled_or_sort atom_env (NApp (NVar (300+IC.tag_number t)) (NVar 0)).
Definition atom_result t := assembled_or_sort atom_env
  (At (NClosed (IC.atom t)) (NVar 0) (AtomZip t (NVar 0)) (Test t (NVar 0))).
Lemma atom_head_typed t : Typed atom_context (atom_head t) (atom_head_type t).
Proof.
  assert (E : atom_head t = var (atom_index t)) by (destruct t; reflexivity).
  rewrite E.
  replace (atom_head_type t) with (atom_context !! atom_index t).
  - apply tV.
  - destruct t;
    cbn [atom_context atom_telescope lambda_parts atom_template close nlams
      fields C B predicate atom_case pair_atom_case pair_args pair_case
      pair_conclusion At Pair Zip AtomZip PairAtomZip PairZip And Test npis
      napps nArrow assemble map rev fst List.app telescope_context atom_head_type
      assembled_or_sort atom_env atom_index lookup IC.tags IC.tag_number
      index ctx_top ctx_pred fin_match];
    unfold shift;
    repeat first [rewrite rename_lift_closed | rewrite rename_comp |
      rewrite rename_product | rewrite rename_application |
      progress cbn [rename weak fin_match]]; reflexivity.
Qed.
Lemma atom_input_typed : Typed atom_context atom_input (lift_closed IC.carrier).
Proof. apply tV. Qed.
Lemma atom_body_typed t : Typed atom_context (atom_body t) (atom_result t).
Proof.
  pose proof (atom_head_typed t) as H.
  unfold atom_head_type, assembled_or_sort, atom_case in H.
  cbn [assemble] in H.
  pose proof (tApp H atom_input_typed) as K.
  unfold atom_result, atom_body, atom_input, atom_head, assembled_or_sort.
  unfold atom_input, atom_head in K.
  destruct t; exact K.
Qed.
