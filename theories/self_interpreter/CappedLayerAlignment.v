From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting DefEq.
From PTSrk.NormalizationComplexity Require Import Morphisms Greedy.
From PTSrk.SelfInterpreter Require Import CappedQuotationState CappedInterpreter
  FragmentUniformity CheckedEqualityLayers CheckedContextualFields CheckedEqualityFields
  ContextualTelescope UniformTelescope UniformTelescopeRecovery ContextualEqualityExtension
  ContextualEqualityRealizer ContextualTelescopeRun IndexedEquality LayerCodeAlignment
  CodeAlignment ChurchSyntax.
Import Context ListNotations.

(** The allocated capped slot is an ordinary variable, including under arbitrary
    dependent telescopes. Actual identity filling erases its transport literally. *)
Module CappedLayerAlignment.

Definition new_base cap R {rs} (D : ContextualTelescope.ContextualTelescope.telescope (CheckedEqualityLayers.CheckedEqualityLayers.width R) rs) e :=
  FragmentUniformity.FragmentUniformity.extend cap (CheckedEqualityLayers.CheckedEqualityLayers.request_budget (CheckedContextualFields.CheckedContextualFields.pack D e)) R.
Definition insertion cap R {rs} (D : ContextualTelescope.ContextualTelescope.telescope (CheckedEqualityLayers.CheckedEqualityLayers.width R) rs) e :
  Fin (CheckedEqualityLayers.CheckedEqualityLayers.width R) -> Fin (CheckedEqualityLayers.CheckedEqualityLayers.width (new_base cap R D e)) := up.
Definition new_domains cap R {rs} (D : ContextualTelescope.ContextualTelescope.telescope (CheckedEqualityLayers.CheckedEqualityLayers.width R) rs) e :=
  ContextualTelescope.ContextualTelescope.rename_telescope D (CheckedEqualityLayers.CheckedEqualityLayers.width (new_base cap R D e)) (insertion cap R D e).
Definition lifted cap R {rs} (D : ContextualTelescope.ContextualTelescope.telescope (CheckedEqualityLayers.CheckedEqualityLayers.width R) rs) e
    (t : Term nat (ContextualTelescope.ContextualTelescope.scope rs (CheckedEqualityLayers.CheckedEqualityLayers.width R))) :=
  rename (ContextualTelescope.ContextualTelescope.lift_ren rs (insertion cap R D e)) t.
Definition field_application cap R {rs} (D : ContextualTelescope.ContextualTelescope.telescope (CheckedEqualityLayers.CheckedEqualityLayers.width R) rs) e
    (a : CappedQuotationState.CappedQuotationState.allocation cap R (CheckedContextualFields.CheckedContextualFields.pack D e)) :=
  UniformTelescope.UniformTelescope.apply_under (new_domains cap R D e) (var (ChurchSyntax.ChurchSyntax.front (CappedQuotationState.CappedQuotationState.slot a))).

Theorem field_application_typed cap R rs (D : ContextualTelescope.ContextualTelescope.telescope (CheckedEqualityLayers.CheckedEqualityLayers.width R) rs) e a :
  @typ nat RankSorts _ (ContextualTelescope.ContextualTelescope.context (new_domains cap R D e) (CheckedEqualityLayers.CheckedEqualityLayers.signature (new_base cap R D e)))
    (field_application cap R D e a)
    (IndexedEquality.IndexedEquality.eq_type (CheckedEqualityFields.CheckedEqualityFields.level e) (lifted cap R D e (CheckedEqualityFields.CheckedEqualityFields.carrier e))
      (lifted cap R D e (CheckedEqualityFields.CheckedEqualityFields.left e)) (lifted cap R D e (CheckedEqualityFields.CheckedEqualityFields.right e))).
Proof.
  unfold field_application; apply UniformTelescope.UniformTelescope.apply_under_typed.
  unfold new_domains, lifted; rewrite <- IndexedEquality.IndexedEquality.eq_type_rename, <- ContextualTelescope.ContextualTelescope.close_type_rename.
  pose proof (CappedQuotationState.CappedQuotationState.allocated_typed cap R (CheckedContextualFields.CheckedContextualFields.pack D e) a) as H.
  rewrite CheckedContextualFields.CheckedContextualFields.field_pack in H; exact H.
Qed.
Theorem field_application_normal cap R rs (D : ContextualTelescope.ContextualTelescope.telescope (CheckedEqualityLayers.CheckedEqualityLayers.width R) rs) e a :
  normalb (field_application cap R D e a)=true.
Proof. apply UniformTelescope.UniformTelescope.apply_under_normal; reflexivity. Qed.
Lemma insertion_fill cap R rs (D : ContextualTelescope.ContextualTelescope.telescope (CheckedEqualityLayers.CheckedEqualityLayers.width R) rs) e i :
  CheckedEqualityLayers.CheckedEqualityLayers.identity_fill (new_base cap R D e) (insertion cap R D e i)=CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R i.
Proof. apply TarskiPalette.TarskiPalette.fill_block_source. Qed.
Lemma filled_new_domains cap R rs (D : ContextualTelescope.ContextualTelescope.telescope (CheckedEqualityLayers.CheckedEqualityLayers.width R) rs) e :
  ContextualTelescope.ContextualTelescope.replace_telescope (new_domains cap R D e) 0 (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill (new_base cap R D e)) =
    ContextualEqualityExtension.ContextualEqualityExtension.filled_domains D (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R).
Proof.
  unfold new_domains, ContextualEqualityExtension.ContextualEqualityExtension.filled_domains.
  transitivity (ContextualTelescope.ContextualTelescope.rename_telescope (ContextualTelescope.ContextualTelescope.replace_telescope D 0 (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R)) 0 (fun i => i)).
  - apply UniformTelescopeRecovery.UniformTelescopeRecovery.telescope_substitution_square; intro i; rewrite rename_id; apply insertion_fill.
  - apply UniformTelescopeRecovery.UniformTelescopeRecovery.telescope_rename_id.
Qed.
Theorem filled_lifted cap R rs (D : ContextualTelescope.ContextualTelescope.telescope (CheckedEqualityLayers.CheckedEqualityLayers.width R) rs) e t :
  replace (ContextualTelescope.ContextualTelescope.lift_sub rs (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill (new_base cap R D e))) (lifted cap R D e t) =
    ContextualEqualityExtension.ContextualEqualityExtension.filled (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R) t.
Proof.
  unfold lifted, ContextualEqualityExtension.ContextualEqualityExtension.filled; rewrite replace_rename; apply replace_ext.
  apply CodeAlignment.CodeAlignment.lift_sub_square, insertion_fill.
Qed.

Definition transport cap R {rs} (D : ContextualTelescope.ContextualTelescope.telescope (CheckedEqualityLayers.CheckedEqualityLayers.width R) rs) e a P z :=
  IndexedEquality.IndexedEquality.transport (field_application cap R D e a) (lifted cap R D e P) (lifted cap R D e z).
Theorem transport_typed cap R rs (D : ContextualTelescope.ContextualTelescope.telescope (CheckedEqualityLayers.CheckedEqualityLayers.width R) rs) e a P z :
  @typ nat RankSorts _ (ContextualTelescope.ContextualTelescope.context D (CheckedEqualityLayers.CheckedEqualityLayers.signature R)) P (IndexedEquality.IndexedEquality.motive_type (CheckedEqualityFields.CheckedEqualityFields.level e) (CheckedEqualityFields.CheckedEqualityFields.carrier e)) ->
  @typ nat RankSorts _ (ContextualTelescope.ContextualTelescope.context D (CheckedEqualityLayers.CheckedEqualityLayers.signature R)) z (app P (CheckedEqualityFields.CheckedEqualityFields.left e)) ->
  @typ nat RankSorts _ (ContextualTelescope.ContextualTelescope.context (new_domains cap R D e) (CheckedEqualityLayers.CheckedEqualityLayers.signature (new_base cap R D e)))
    (transport cap R D e a P z) (lifted cap R D e (app P (CheckedEqualityFields.CheckedEqualityFields.right e))).
Proof.
  intros HP Hz; unfold transport; change (lifted cap R D e (app P (CheckedEqualityFields.CheckedEqualityFields.right e))) with
    (app (lifted cap R D e P) (lifted cap R D e (CheckedEqualityFields.CheckedEqualityFields.right e))).
  eapply IndexedEquality.IndexedEquality.transport_typed; [apply field_application_typed| |].
  - change (typ (ContextualTelescope.ContextualTelescope.context (new_domains cap R D e) (CheckedEqualityLayers.CheckedEqualityLayers.signature (new_base cap R D e)))
      (lifted cap R D e P) (lifted cap R D e (IndexedEquality.IndexedEquality.motive_type (CheckedEqualityFields.CheckedEqualityFields.level e) (CheckedEqualityFields.CheckedEqualityFields.carrier e)))).
    apply typing_rename with (G := ContextualTelescope.ContextualTelescope.context D (CheckedEqualityLayers.CheckedEqualityLayers.signature R));
      [apply ContextualTelescope.ContextualTelescope.context_ren, CappedInterpreter.CappedInterpreter.insertion_typed|exact HP].
  - change (typ (ContextualTelescope.ContextualTelescope.context (new_domains cap R D e) (CheckedEqualityLayers.CheckedEqualityLayers.signature (new_base cap R D e)))
      (lifted cap R D e z) (lifted cap R D e (app P (CheckedEqualityFields.CheckedEqualityFields.left e)))).
    apply typing_rename with (G := ContextualTelescope.ContextualTelescope.context D (CheckedEqualityLayers.CheckedEqualityLayers.signature R));
      [apply ContextualTelescope.ContextualTelescope.context_ren, CappedInterpreter.CappedInterpreter.insertion_typed|exact Hz].
Qed.
Theorem transport_normal cap R rs (D : ContextualTelescope.ContextualTelescope.telescope (CheckedEqualityLayers.CheckedEqualityLayers.width R) rs) e a P z :
  normalb P=true -> normalb z=true -> normalb (transport cap R D e a P z)=true.
Proof.
  intros HP Hz; unfold transport, IndexedEquality.IndexedEquality.transport; cbn [normalb isLambda].
  rewrite field_application_normal; unfold lifted; rewrite !UniformTelescope.UniformTelescope.normalb_rename, HP, Hz.
  unfold field_application; rewrite UniformTelescope.UniformTelescope.apply_under_neutral by reflexivity; reflexivity.
Qed.
Theorem transport_neutral cap R rs (D : ContextualTelescope.ContextualTelescope.telescope (CheckedEqualityLayers.CheckedEqualityLayers.width R) rs) e a P z :
  isLambda (transport cap R D e a P z)=false.
Proof. reflexivity. Qed.
Theorem transport_erases cap R rs (D : ContextualTelescope.ContextualTelescope.telescope (CheckedEqualityLayers.CheckedEqualityLayers.width R) rs) e a P z :
  reduces_to nat _ (replace (ContextualTelescope.ContextualTelescope.lift_sub rs (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill (new_base cap R D e)))
    (transport cap R D e a P z)) (ContextualEqualityExtension.ContextualEqualityExtension.filled (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R) z).
Proof.
  unfold transport; rewrite IndexedEquality.IndexedEquality.transport_replace, !filled_lifted.
  unfold field_application; rewrite UniformTelescope.UniformTelescope.apply_under_replace, filled_new_domains; cbn [replace].
  pose proof (CappedQuotationState.CappedQuotationState.allocated_fill cap R (CheckedContextualFields.CheckedContextualFields.pack D e) a) as HF.
  rewrite LayerCodeAlignment.LayerCodeAlignment.value_pack in HF.
  pose proof (ContextualEqualityRealizer.ContextualEqualityRealizer.normal_witness_erases (CheckedEqualityFields.CheckedEqualityFields.level e) 0 rs ε (ContextualEqualityExtension.ContextualEqualityExtension.filled_domains D (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R))
    (ContextualEqualityExtension.ContextualEqualityExtension.filled (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R) (CheckedEqualityFields.CheckedEqualityFields.carrier e)) (ContextualEqualityExtension.ContextualEqualityExtension.filled (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R) (CheckedEqualityFields.CheckedEqualityFields.left e))
    (ContextualTelescope.ContextualTelescope.scope rs 0) (fun i => var i) (ContextualEqualityExtension.ContextualEqualityExtension.filled (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R) P) (ContextualEqualityExtension.ContextualEqualityExtension.filled (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R) z)) as H.
  rewrite ContextualTelescopeRun.ContextualTelescopeRun.run_apply_under, replace_var in H.
  exact (eq_ind_r (fun q : Term nat 0 => reduces_to nat _
    (IndexedEquality.IndexedEquality.transport (UniformTelescope.UniformTelescope.apply_under (ContextualEqualityExtension.ContextualEqualityExtension.filled_domains D (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R)) q)
      (ContextualEqualityExtension.ContextualEqualityExtension.filled (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R) P) (ContextualEqualityExtension.ContextualEqualityExtension.filled (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R) z))
    (ContextualEqualityExtension.ContextualEqualityExtension.filled (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R) z)) H HF).
Qed.

Print Assumptions field_application_typed.
Print Assumptions field_application_normal.
Print Assumptions insertion_fill.
Print Assumptions filled_new_domains.
Print Assumptions filled_lifted.
Print Assumptions transport_typed.
Print Assumptions transport_normal.
Print Assumptions transport_neutral.
Print Assumptions transport_erases.
End CappedLayerAlignment.
