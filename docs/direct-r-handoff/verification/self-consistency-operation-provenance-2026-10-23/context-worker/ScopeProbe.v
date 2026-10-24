(** Original contextual lookup, NOT lifted substitution-environment lookup.
    Every crossed context extension shifts the selected declaration, including
    the zero-index case.  These are independent original-PTS graph clauses;
    no native index/equality/typing or output-scope premise occurs in them.

    Literal context codes use GEmpty and GExtend(prefix,declaration).  They
    are DISTINCT from CertificateSerialization.encode_context, whose extension
    stores a declaration CERTIFICATE and a rank.  Extraction of those actual
    declarations is a separate source-provenance bridge.

    Lookup is a local raw operation trace: zero need not inspect its prefix.
    The separate ContextGuard certifies the entire scoped context when needed.
    No arbitrary-witness functionality or dependent typing is asserted. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks Preservation DefEq AbstractRewriting.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRCheck DirectRStructural.
From PTSrk.SelfConsistency Require Import StructuralCodes InternalCarrier
  InternalResources InternalBinary InternalScope InternalRenamingLookup
  InternalRenaming InternalJointTraversal NamedTemplates NamedBeta.
Import ListNotations.

Module InternalContextLookup.
Import CommonCodes Core Structural InternalCarrier.InternalCarrier
  InternalResources.InternalResources InternalBinary.InternalBinary
  InternalScope.InternalScope InternalRenamingLookup.InternalRenamingLookup
  InternalRenaming.InternalRenaming.
Module JT := InternalJointTraversal.InternalJointTraversal.
Module NT := NamedTemplates.NamedTemplates.
Module NB := NamedBeta.NamedBeta.

(** Check each complete binder context once, then assemble original tLam
    derivations.  This avoids repeated expansion of the closed shift graph. *)
Local Fixpoint lambda_parts {n} (t : Term nat n) :
  sigT (fun m : nat => (telescope n m * Term nat m)%type) :=
  match t with
  | lam A b => match lambda_parts b with
    | existT _ m (T,u) => existT _ m (tel_cons 0 A T,u)
    end
  | _ => existT _ n (tel_nil,t)
  end.
Local Definition assembled_or_sort env t :=
  match assemble t env with Some u => u | None => 𝓤 0 end.

Definition empty_context := atom GEmpty.
Definition CtxCons g a := node (NClosed (atom GExtend)) (node g a).
Definition context_cons := close (nlams [(0, C); (1, C)]
  (CtxCons (NVar 0) (NVar 1))) eq_refl.

Definition context_lookup_step_arguments := step_codes ++
  [(20, CtxLookup (NVar 10) (NVar 12) (NVar 14) (NVar 16))] ++ step_edges.
Definition context_lookup_step_type := close (npis context_lookup_step_arguments
  (CtxLookup (NVar 11) (CtxCons (NVar 12) (NVar 13)) (NVar 15) (NVar 17))) eq_refl.
Definition context_lookup_step := close (nlams (context_lookup_step_arguments ++ lookup_fields)
  (napps (NVar 72) [NVar 10; NVar 11; NVar 12; NVar 13;
    NVar 14; NVar 15; NVar 16; NVar 17;
    napps (NVar 20) [NVar 70; NVar 71; NVar 72]; NVar 21; NVar 22; NVar 23])) eq_refl.

(** Arbitrary represented lookup witnesses give scoped outputs.  Each local
    shift uses its OWN target-successor edge to derive the environment bound.
    This law uses neither canonical reflection nor source typing. *)
Definition scope_motive := nlams [(10, C); (11, C); (12, C); (13, C)]
  (Scope (NVar 10) (NVar 13)).
Definition scope_zero := nlams zero_arguments
  (napps (NVar 99)
    [ShiftEnv (NVar 10); NVar 11; NVar 10; NVar 11; stop; NVar 13; NVar 14;
     napps (NVar 98) [NVar 10; NVar 11; NVar 20]; NVar 21]).
Definition scope_step := nlams (step_codes ++
  [(20, Scope (NVar 10) (NVar 16))] ++ step_edges)
  (napps (NVar 99)
    [ShiftEnv (NVar 10); NVar 11; NVar 10; NVar 11; stop; NVar 16; NVar 17;
     napps (NVar 98) [NVar 10; NVar 11; NVar 21]; NVar 23]).
Definition scope_arguments := lookup_arguments ++
  [(4, CtxLookup (NVar 0) (NVar 1) (NVar 2) (NVar 3))].
Definition context_lookup_scope_type := close
  (npis scope_arguments (Scope (NVar 0) (NVar 3))) eq_refl.
Definition context_lookup_scope_template := close
  (nlams ([(98, NClosed bounded_shift_bound_type); (99, NClosed renaming_scope_type)] ++
    scope_arguments)
    (napps (NVar 4) [scope_motive; scope_zero; scope_step])) eq_refl.
Local Lemma scope_result_exact :
  telescope_product scope_telescope scope_result =
  Arrow bounded_shift_bound_type (Arrow renaming_scope_type context_lookup_scope_type).
Proof.
  pose proof (NT.evaluate_close
    (npis scope_arguments (Scope (NVar 0) (NVar 3))) eq_refl
    2 (NT.names [99;98])) as E.
  pose proof (eq_trans (NT.assemble_evaluate
    (npis scope_arguments (Scope (NVar 0) (NVar 3))) [99;98]) E) as H.
  change (Π (@lift_closed 0 bounded_shift_bound_type)
    (Π (@lift_closed 1 renaming_scope_type)
      (assembled_or_sort [99;98]
        (npis scope_arguments (Scope (NVar 0) (NVar 3)))))) = _.
  unfold assembled_or_sort; rewrite H.
  rewrite <- (@lift_closed_arrow 1 renaming_scope_type context_lookup_scope_type).
  rewrite <- (@lift_closed_arrow 0 bounded_shift_bound_type
    (Arrow renaming_scope_type context_lookup_scope_type)).
  apply lift_closed_zero.
Qed.
Definition context_lookup_scope :=
  app (app context_lookup_scope_template bounded_shift_bound) renaming_scope.

End InternalContextLookup.
