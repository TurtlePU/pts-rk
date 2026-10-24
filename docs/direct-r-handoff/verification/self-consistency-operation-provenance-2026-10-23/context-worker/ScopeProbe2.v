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

(** Independent contextual scope.  Declaration scope is an input guard, not
    a claim that any declaration has an inhabiting term. *)
Definition CG n g := napps (NVar 50) [n; g].
Definition guard_empty_rule := CG stop (NClosed empty_context).
Definition guard_cons_codes := [(10, C); (11, C); (12, C); (13, C)].
Definition guard_cons_arguments := guard_cons_codes ++
  [(14, Succ (NVar 10) (NVar 11));
   (15, CG (NVar 10) (NVar 12)); (16, Scope (NVar 10) (NVar 13))].
Definition guard_cons_rule := npis guard_cons_arguments
  (CG (NVar 11) (CtxCons (NVar 12) (NVar 13))).
Definition guard_fields := [(50, nArrow C (nArrow C (NSort 12)));
  (51, guard_empty_rule); (52, guard_cons_rule)].
Definition context_guard := close (nlams [(0, C); (1, C)]
  (npis guard_fields (CG (NVar 0) (NVar 1)))) eq_refl.
Definition ContextGuard n g := napps (NClosed context_guard) [n; g].

Definition context_guard_empty_type := close
  (ContextGuard stop (NClosed empty_context)) eq_refl.
Definition context_guard_empty := close (nlams guard_fields (NVar 51)) eq_refl.

Definition context_guard_cons_arguments := guard_cons_codes ++
  [(14, Succ (NVar 10) (NVar 11));
   (15, ContextGuard (NVar 10) (NVar 12)); (16, Scope (NVar 10) (NVar 13))].
Definition context_guard_cons_type := close (npis context_guard_cons_arguments
  (ContextGuard (NVar 11) (CtxCons (NVar 12) (NVar 13)))) eq_refl.
Definition context_guard_cons := close
  (nlams (context_guard_cons_arguments ++ guard_fields)
    (napps (NVar 52) [NVar 10; NVar 11; NVar 12; NVar 13; NVar 14;
      napps (NVar 15) [NVar 50; NVar 51; NVar 52]; NVar 16])) eq_refl.

(** Shift is the existing annotated renaming graph with its fixed, bounded
    successor environment; it is neither a new primitive nor native shift. *)
Definition Shift n m a b := Rename (ShiftEnv n) m n m stop a b.
Definition LR n g i a := napps (NVar 70) [n; g; i; a].
Definition zero_codes := [(10, C); (11, C); (12, C); (13, C); (14, C)].
Definition zero_arguments := zero_codes ++
  [(20, Succ (NVar 10) (NVar 11));
   (21, Shift (NVar 10) (NVar 11) (NVar 13) (NVar 14))].
Definition zero_rule := npis zero_arguments
  (LR (NVar 11) (CtxCons (NVar 12) (NVar 13)) stop (NVar 14)).
Definition step_codes := [(10, C); (11, C); (12, C); (13, C);
  (14, C); (15, C); (16, C); (17, C)].
Definition step_edges :=
  [(21, Succ (NVar 10) (NVar 11)); (22, Succ (NVar 14) (NVar 15));
   (23, Shift (NVar 10) (NVar 11) (NVar 16) (NVar 17))].
Definition step_rule := npis (step_codes ++
  [(20, LR (NVar 10) (NVar 12) (NVar 14) (NVar 16))] ++ step_edges)
  (LR (NVar 11) (CtxCons (NVar 12) (NVar 13)) (NVar 15) (NVar 17)).
Definition lookup_fields :=
  [(70, nArrow C (nArrow C (nArrow C (nArrow C (NSort 12)))));
   (71, zero_rule); (72, step_rule)].
Definition lookup_arguments := [(0, C); (1, C); (2, C); (3, C)].
Definition context_lookup := close (nlams lookup_arguments
  (npis lookup_fields (LR (NVar 0) (NVar 1) (NVar 2) (NVar 3)))) eq_refl.
Definition CtxLookup n g i a := napps (NClosed context_lookup) [n; g; i; a].
Definition context_lookup_sort_type := close (npis lookup_arguments (NSort 18)) eq_refl.

Definition context_lookup_zero_type := close (npis zero_arguments
  (CtxLookup (NVar 11) (CtxCons (NVar 12) (NVar 13)) stop (NVar 14))) eq_refl.
Definition context_lookup_zero := close (nlams (zero_arguments ++ lookup_fields)
  (napps (NVar 71) [NVar 10; NVar 11; NVar 12; NVar 13; NVar 14; NVar 20; NVar 21])) eq_refl.
Local Definition zero_telescope : telescope 0 10 :=
  fst (projT2 (lambda_parts context_lookup_zero)).
Local Definition zero_context := telescope_context zero_telescope ε.
Local Definition zero_body := snd (projT2 (lambda_parts context_lookup_zero)).
Local Definition zero_result := assembled_or_sort
  (rev (map fst (zero_arguments ++ lookup_fields)))
  (LR (NVar 11) (CtxCons (NVar 12) (NVar 13)) stop (NVar 14)).

Definition context_lookup_step_arguments := step_codes ++
  [(20, CtxLookup (NVar 10) (NVar 12) (NVar 14) (NVar 16))] ++ step_edges.
Definition context_lookup_step_type := close (npis context_lookup_step_arguments
  (CtxLookup (NVar 11) (CtxCons (NVar 12) (NVar 13)) (NVar 15) (NVar 17))) eq_refl.
Definition context_lookup_step := close (nlams (context_lookup_step_arguments ++ lookup_fields)
  (napps (NVar 72) [NVar 10; NVar 11; NVar 12; NVar 13;
    NVar 14; NVar 15; NVar 16; NVar 17;
    napps (NVar 20) [NVar 70; NVar 71; NVar 72]; NVar 21; NVar 22; NVar 23])) eq_refl.
Local Definition step_telescope : telescope 0 15 :=
  fst (projT2 (lambda_parts context_lookup_step)).
Local Definition step_context := telescope_context step_telescope ε.
Local Definition step_body := snd (projT2 (lambda_parts context_lookup_step)).
Local Definition step_result := assembled_or_sort
  (rev (map fst (context_lookup_step_arguments ++ lookup_fields)))
  (LR (NVar 11) (CtxCons (NVar 12) (NVar 13)) (NVar 15) (NVar 17)).

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
Local Definition scope_telescope : telescope 0 7 :=
  fst (projT2 (lambda_parts context_lookup_scope_template)).
Local Definition scope_context := telescope_context scope_telescope ε.
Local Definition scope_body := snd (projT2 (lambda_parts context_lookup_scope_template)).
Local Definition scope_result := assembled_or_sort [4;3;2;1;0;99;98]
  (Scope (NVar 0) (NVar 3)).
Local Lemma lift_closed_arrow {n} (A B : closed_term) :
  @lift_closed n (Arrow A B) =
  Π (@lift_closed n A) (@lift_closed (S n) B).
Proof.
  unfold lift_closed at 1; rewrite rename_arrow.
  fold (@lift_closed n A); fold (@lift_closed n B).
  unfold Arrow; rewrite <- lift_closed_shift; reflexivity.
Qed.
Local Lemma scope_result_exact :
  telescope_product scope_telescope scope_result =
  Arrow bounded_shift_bound_type (Arrow renaming_scope_type context_lookup_scope_type).
Proof.
  pose proof (NT.evaluate_close
    (npis scope_arguments (Scope (NVar 0) (NVar 3))) eq_refl
    2 (NT.names [99;98])) as E.
  pose proof (eq_trans (NT.assemble_evaluate
    (npis scope_arguments (Scope (NVar 0) (NVar 3))) [99;98]) E) as H.
  change ((Π (@lift_closed 0 bounded_shift_bound_type)
    (Π (@lift_closed 1 renaming_scope_type)
      (assembled_or_sort [99;98]
        (npis scope_arguments (Scope (NVar 0) (NVar 3)))))) =
    Arrow bounded_shift_bound_type (Arrow renaming_scope_type context_lookup_scope_type)).
  unfold assembled_or_sort; rewrite H.
  exact (eq_trans
    (f_equal (fun b => Π (@lift_closed 0 bounded_shift_bound_type) b)
      (eq_sym (@lift_closed_arrow 1 renaming_scope_type context_lookup_scope_type)))
    (eq_trans (eq_sym (@lift_closed_arrow 0 bounded_shift_bound_type
      (Arrow renaming_scope_type context_lookup_scope_type)))
      (lift_closed_zero _))).
Qed.
Definition context_lookup_scope :=
  app (app context_lookup_scope_template bounded_shift_bound) renaming_scope.

Local Lemma lambda_parts_exact {n} (t : Term nat n) :
  telescope_abstract (fst (projT2 (lambda_parts t)))
    (snd (projT2 (lambda_parts t))) = t.
Proof.
  induction t; cbn [lambda_parts]; try reflexivity.
  destruct (lambda_parts t2) as [m [T u]]; cbn in *; now rewrite IHt2.
Qed.
Lemma final_assembly_from_parts
  (Hwf : @wf nat RankSorts _ scope_context)
  (Hbody : Typed scope_context scope_body scope_result) :
  Typed ε context_lookup_scope_template
    (Arrow bounded_shift_bound_type (Arrow renaming_scope_type context_lookup_scope_type)).
Proof.
  rewrite <- (lambda_parts_exact context_lookup_scope_template).
  rewrite <- scope_result_exact.
  apply JT.telescope_abstraction_from_context; [exact Hwf | exact Hbody].
Qed.

End InternalContextLookup.
