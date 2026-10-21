From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting DefEq.
From PTSrk.NormalizationComplexity Require Import Morphisms Greedy.
From PTSrk.SelfInterpreter Require Import CheckedEqualityLayers CheckedContextualFields
  CheckedEqualityFields ContextualTelescope UniformTelescope UniformTelescopeRecovery
  ContextualEqualityExtension ContextualEqualityRealizer ContextualTelescopeRun
  IndexedEquality TarskiContext BrownPalsberg CodeAlignment GlobalEqualityInsertion
  QuotationCache.
Import Context ListNotations.

(** Concrete code alignment through a COMPLETE numeric-budget layer.
    The equality slot is computed by allocate_original from independent
    original endpoint evidence, not supplied as an equality oracle. *)
Module LayerCodeAlignment.

(** Package correctness is literal dependent data equality, so even the
    context-sensitive normalized identity value is preserved exactly. *)
Record telescope_endpoint n := Endpoint {
  endpoint_ranks : list nat;
  endpoint_domains : ContextualTelescope.ContextualTelescope.telescope n endpoint_ranks;
  endpoint_body : CheckedEqualityFields.CheckedEqualityFields.descriptor (ContextualTelescope.ContextualTelescope.scope endpoint_ranks n)
}.
Arguments Endpoint {n} _ _ _.
Definition unpack {n} (x : CheckedContextualFields.CheckedContextualFields.candidate n) : telescope_endpoint n :=
  Endpoint (CheckedContextualFields.CheckedContextualFields.profile x) (CheckedContextualFields.CheckedContextualFields.domains x) (CheckedContextualFields.CheckedContextualFields.endpoint x).
Definition prepend n r A (p : telescope_endpoint (S n)) : telescope_endpoint n :=
  match p with Endpoint rs D e => Endpoint (r::rs) (ContextualTelescope.ContextualTelescope.tcons r A D) e end.
Theorem unpack_pack n rs (D : ContextualTelescope.ContextualTelescope.telescope n rs) e : unpack (CheckedContextualFields.CheckedContextualFields.pack D e) = Endpoint rs D e.
Proof.
  revert e; induction D; intro e; [reflexivity |].
  exact (f_equal (prepend n r A) (IHD e)).
Qed.
Definition endpoint_value n sigma (p : telescope_endpoint n) :=
  match p with Endpoint rs D e => ContextualEqualityExtension.ContextualEqualityExtension.value (CheckedEqualityFields.CheckedEqualityFields.level e) D sigma (CheckedEqualityFields.CheckedEqualityFields.carrier e) (CheckedEqualityFields.CheckedEqualityFields.left e) end.
Theorem value_pack n rs (D : ContextualTelescope.ContextualTelescope.telescope n rs) sigma e :
  CheckedContextualFields.CheckedContextualFields.value sigma (CheckedContextualFields.CheckedContextualFields.pack D e) = ContextualEqualityExtension.ContextualEqualityExtension.value (CheckedEqualityFields.CheckedEqualityFields.level e) D sigma (CheckedEqualityFields.CheckedEqualityFields.carrier e) (CheckedEqualityFields.CheckedEqualityFields.left e).
Proof. exact (f_equal (endpoint_value n sigma) (unpack_pack n rs D e)). Qed.

Definition new_base (R : CheckedEqualityLayers.CheckedEqualityLayers.realization) {rs} (D : ContextualTelescope.ContextualTelescope.telescope (CheckedEqualityLayers.CheckedEqualityLayers.width R) rs) e :=
  CheckedEqualityLayers.CheckedEqualityLayers.extend (CheckedEqualityLayers.CheckedEqualityLayers.request_budget (CheckedContextualFields.CheckedContextualFields.pack D e)) R.
Definition insertion (R : CheckedEqualityLayers.CheckedEqualityLayers.realization) {rs} (D : ContextualTelescope.ContextualTelescope.telescope (CheckedEqualityLayers.CheckedEqualityLayers.width R) rs) e :=
  CheckedEqualityLayers.CheckedEqualityLayers.insertion (CheckedEqualityLayers.CheckedEqualityLayers.request_budget (CheckedContextualFields.CheckedContextualFields.pack D e)) R.
Definition new_domains (R : CheckedEqualityLayers.CheckedEqualityLayers.realization) {rs} (D : ContextualTelescope.ContextualTelescope.telescope (CheckedEqualityLayers.CheckedEqualityLayers.width R) rs) e :=
  ContextualTelescope.ContextualTelescope.rename_telescope D (CheckedEqualityLayers.CheckedEqualityLayers.width (new_base R D e)) (insertion R D e).
Definition lifted (R : CheckedEqualityLayers.CheckedEqualityLayers.realization) {rs} (D : ContextualTelescope.ContextualTelescope.telescope (CheckedEqualityLayers.CheckedEqualityLayers.width R) rs) e
    (t : Term nat (ContextualTelescope.ContextualTelescope.scope rs (CheckedEqualityLayers.CheckedEqualityLayers.width R))) :=
  rename (ContextualTelescope.ContextualTelescope.lift_ren rs (insertion R D e)) t.
Definition field_application (R : CheckedEqualityLayers.CheckedEqualityLayers.realization) {rs} (D : ContextualTelescope.ContextualTelescope.telescope (CheckedEqualityLayers.CheckedEqualityLayers.width R) rs) e
    (a : CheckedEqualityLayers.CheckedEqualityLayers.allocation R (CheckedContextualFields.CheckedContextualFields.pack D e)) :=
  UniformTelescope.UniformTelescope.apply_under (new_domains R D e) (var (CheckedEqualityLayers.CheckedEqualityLayers.CS.front (CheckedEqualityLayers.CheckedEqualityLayers.slot a))).

Theorem field_application_typed R rs (D : ContextualTelescope.ContextualTelescope.telescope (CheckedEqualityLayers.CheckedEqualityLayers.width R) rs) e a :
  @typ nat RankSorts _ (ContextualTelescope.ContextualTelescope.context (new_domains R D e) (CheckedEqualityLayers.CheckedEqualityLayers.signature (new_base R D e)))
    (field_application R D e a)
    (IndexedEquality.IndexedEquality.eq_type (CheckedEqualityFields.CheckedEqualityFields.level e) (lifted R D e (CheckedEqualityFields.CheckedEqualityFields.carrier e))
      (lifted R D e (CheckedEqualityFields.CheckedEqualityFields.left e)) (lifted R D e (CheckedEqualityFields.CheckedEqualityFields.right e))).
Proof.
  unfold field_application; apply UniformTelescope.UniformTelescope.apply_under_typed.
  unfold new_domains, lifted; rewrite <- IndexedEquality.IndexedEquality.eq_type_rename, <- ContextualTelescope.ContextualTelescope.close_type_rename.
  pose proof (CheckedEqualityLayers.CheckedEqualityLayers.allocated_typed R (CheckedContextualFields.CheckedContextualFields.pack D e) a) as H.
  rewrite CheckedContextualFields.CheckedContextualFields.field_pack in H; exact H.
Qed.
Theorem field_application_normal R rs (D : ContextualTelescope.ContextualTelescope.telescope (CheckedEqualityLayers.CheckedEqualityLayers.width R) rs) e a :
  normalb (field_application R D e a) = true.
Proof. apply UniformTelescope.UniformTelescope.apply_under_normal; reflexivity. Qed.

Lemma filled_new_domains R rs (D : ContextualTelescope.ContextualTelescope.telescope (CheckedEqualityLayers.CheckedEqualityLayers.width R) rs) e :
  ContextualTelescope.ContextualTelescope.replace_telescope (new_domains R D e) 0 (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill (new_base R D e)) =
  ContextualEqualityExtension.ContextualEqualityExtension.filled_domains D (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R).
Proof.
  unfold new_domains, ContextualEqualityExtension.ContextualEqualityExtension.filled_domains.
  transitivity (ContextualTelescope.ContextualTelescope.rename_telescope (ContextualTelescope.ContextualTelescope.replace_telescope D 0 (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R)) 0 (fun i => i)).
  - apply UniformTelescopeRecovery.UniformTelescopeRecovery.telescope_substitution_square; intro i; rewrite rename_id.
    apply CheckedEqualityLayers.CheckedEqualityLayers.insertion_fill.
  - apply UniformTelescopeRecovery.UniformTelescopeRecovery.telescope_rename_id.
Qed.
Theorem filled_lifted R rs (D : ContextualTelescope.ContextualTelescope.telescope (CheckedEqualityLayers.CheckedEqualityLayers.width R) rs) e t :
  replace (ContextualTelescope.ContextualTelescope.lift_sub rs (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill (new_base R D e))) (lifted R D e t) =
  ContextualEqualityExtension.ContextualEqualityExtension.filled (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R) t.
Proof.
  unfold lifted, ContextualEqualityExtension.ContextualEqualityExtension.filled; rewrite replace_rename; apply replace_ext.
  apply CodeAlignment.CodeAlignment.lift_sub_square; apply CheckedEqualityLayers.CheckedEqualityLayers.insertion_fill.
Qed.

Definition transport R {rs} (D : ContextualTelescope.ContextualTelescope.telescope (CheckedEqualityLayers.CheckedEqualityLayers.width R) rs) e a P z :=
  IndexedEquality.IndexedEquality.transport (field_application R D e a) (lifted R D e P) (lifted R D e z).
Theorem transport_typed R rs (D : ContextualTelescope.ContextualTelescope.telescope (CheckedEqualityLayers.CheckedEqualityLayers.width R) rs) e a P z :
  @typ nat RankSorts _ (ContextualTelescope.ContextualTelescope.context D (CheckedEqualityLayers.CheckedEqualityLayers.signature R)) P (IndexedEquality.IndexedEquality.motive_type (CheckedEqualityFields.CheckedEqualityFields.level e) (CheckedEqualityFields.CheckedEqualityFields.carrier e)) ->
  @typ nat RankSorts _ (ContextualTelescope.ContextualTelescope.context D (CheckedEqualityLayers.CheckedEqualityLayers.signature R)) z (app P (CheckedEqualityFields.CheckedEqualityFields.left e)) ->
  @typ nat RankSorts _ (ContextualTelescope.ContextualTelescope.context (new_domains R D e) (CheckedEqualityLayers.CheckedEqualityLayers.signature (new_base R D e)))
    (transport R D e a P z) (lifted R D e (app P (CheckedEqualityFields.CheckedEqualityFields.right e))).
Proof.
  intros HP Hz; unfold transport; change (lifted R D e (app P (CheckedEqualityFields.CheckedEqualityFields.right e))) with
    (app (lifted R D e P) (lifted R D e (CheckedEqualityFields.CheckedEqualityFields.right e))).
  eapply IndexedEquality.IndexedEquality.transport_typed; [apply field_application_typed | |].
  - change (typ (ContextualTelescope.ContextualTelescope.context (new_domains R D e) (CheckedEqualityLayers.CheckedEqualityLayers.signature (new_base R D e)))
      (lifted R D e P) (lifted R D e (IndexedEquality.IndexedEquality.motive_type (CheckedEqualityFields.CheckedEqualityFields.level e) (CheckedEqualityFields.CheckedEqualityFields.carrier e)))).
    apply typing_rename with (G := ContextualTelescope.ContextualTelescope.context D (CheckedEqualityLayers.CheckedEqualityLayers.signature R)); [apply ContextualTelescope.ContextualTelescope.context_ren, CheckedEqualityLayers.CheckedEqualityLayers.insertion_typed | exact HP].
  - change (typ (ContextualTelescope.ContextualTelescope.context (new_domains R D e) (CheckedEqualityLayers.CheckedEqualityLayers.signature (new_base R D e)))
      (lifted R D e z) (lifted R D e (app P (CheckedEqualityFields.CheckedEqualityFields.left e)))).
    apply typing_rename with (G := ContextualTelescope.ContextualTelescope.context D (CheckedEqualityLayers.CheckedEqualityLayers.signature R)); [apply ContextualTelescope.ContextualTelescope.context_ren, CheckedEqualityLayers.CheckedEqualityLayers.insertion_typed | exact Hz].
Qed.
Theorem transport_normal R rs (D : ContextualTelescope.ContextualTelescope.telescope (CheckedEqualityLayers.CheckedEqualityLayers.width R) rs) e a P z :
  normalb P = true -> normalb z = true -> normalb (transport R D e a P z) = true.
Proof.
  intros HP Hz; unfold transport, IndexedEquality.IndexedEquality.transport; cbn [normalb isLambda].
  rewrite field_application_normal; unfold lifted; rewrite !UniformTelescope.UniformTelescope.normalb_rename, HP, Hz.
  unfold field_application; rewrite UniformTelescope.UniformTelescope.apply_under_neutral by reflexivity; reflexivity.
Qed.
Theorem transport_neutral R rs (D : ContextualTelescope.ContextualTelescope.telescope (CheckedEqualityLayers.CheckedEqualityLayers.width R) rs) e a P z :
  isLambda (transport R D e a P z) = false.
Proof. reflexivity. Qed.
Theorem transport_erases R rs (D : ContextualTelescope.ContextualTelescope.telescope (CheckedEqualityLayers.CheckedEqualityLayers.width R) rs) e a P z :
  reduces_to nat _ (replace (ContextualTelescope.ContextualTelescope.lift_sub rs (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill (new_base R D e)))
    (transport R D e a P z)) (ContextualEqualityExtension.ContextualEqualityExtension.filled (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R) z).
Proof.
  unfold transport; rewrite IndexedEquality.IndexedEquality.transport_replace, !filled_lifted.
  unfold field_application; rewrite UniformTelescope.UniformTelescope.apply_under_replace, filled_new_domains; cbn [replace].
  pose proof (CheckedEqualityLayers.CheckedEqualityLayers.allocated_fill R (CheckedContextualFields.CheckedContextualFields.pack D e) a) as HF; rewrite value_pack in HF.
  pose proof (ContextualEqualityRealizer.ContextualEqualityRealizer.normal_witness_erases (CheckedEqualityFields.CheckedEqualityFields.level e) 0 rs ε (ContextualEqualityExtension.ContextualEqualityExtension.filled_domains D (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R))
    (ContextualEqualityExtension.ContextualEqualityExtension.filled (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R) (CheckedEqualityFields.CheckedEqualityFields.carrier e)) (ContextualEqualityExtension.ContextualEqualityExtension.filled (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R) (CheckedEqualityFields.CheckedEqualityFields.left e))
    (ContextualTelescope.ContextualTelescope.scope rs 0) (fun i => var i) (ContextualEqualityExtension.ContextualEqualityExtension.filled (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R) P) (ContextualEqualityExtension.ContextualEqualityExtension.filled (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R) z)) as H.
  rewrite ContextualTelescopeRun.ContextualTelescopeRun.run_apply_under, replace_var in H.
  exact (eq_ind_r (fun q : Term nat 0 => reduces_to nat _
    (IndexedEquality.IndexedEquality.transport (UniformTelescope.UniformTelescope.apply_under (ContextualEqualityExtension.ContextualEqualityExtension.filled_domains D (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R)) q)
      (ContextualEqualityExtension.ContextualEqualityExtension.filled (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R) P) (ContextualEqualityExtension.ContextualEqualityExtension.filled (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R) z))
    (ContextualEqualityExtension.ContextualEqualityExtension.filled (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R) z)) H HF).
Qed.

Definition inherited_environment k R rs (D : ContextualTelescope.ContextualTelescope.telescope (CheckedEqualityLayers.CheckedEqualityLayers.width R) rs) e
    (E : TarskiContext.TarskiContext.environment k _ (ContextualTelescope.ContextualTelescope.context D (CheckedEqualityLayers.CheckedEqualityLayers.signature R))) :=
  TarskiContext.TarskiContext.rename_environment k _ _ (ContextualTelescope.ContextualTelescope.context D (CheckedEqualityLayers.CheckedEqualityLayers.signature R))
    (ContextualTelescope.ContextualTelescope.context (new_domains R D e) (CheckedEqualityLayers.CheckedEqualityLayers.signature (new_base R D e))) E
    (ContextualTelescope.ContextualTelescope.lift_ren rs (insertion R D e))
    (ContextualTelescope.ContextualTelescope.context_ren _ rs D (CheckedEqualityLayers.CheckedEqualityLayers.signature R) _ (CheckedEqualityLayers.CheckedEqualityLayers.signature (new_base R D e))
      (insertion R D e) (CheckedEqualityLayers.CheckedEqualityLayers.insertion_typed (CheckedEqualityLayers.CheckedEqualityLayers.request_budget (CheckedContextualFields.CheckedContextualFields.pack D e)) R)).

Definition preserve_realization k R rs (D : ContextualTelescope.ContextualTelescope.telescope (CheckedEqualityLayers.CheckedEqualityLayers.width R) rs) e E
    (K : Ctx nat (ContextualTelescope.ContextualTelescope.scope rs 0)) (Q : QuotationCache.QuotationCache.realization E (ContextualTelescope.ContextualTelescope.lift_sub rs (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R)) K)
    (HD : ContextualTelescope.ContextualTelescope.formed (CheckedEqualityLayers.CheckedEqualityLayers.signature R) D) :
    QuotationCache.QuotationCache.realization (inherited_environment k R rs D e E)
      (ContextualTelescope.ContextualTelescope.lift_sub rs (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill (new_base R D e))) K :=
  GlobalEqualityInsertion.GlobalEqualityInsertion.base_extension_realization k _ _ rs (CheckedEqualityLayers.CheckedEqualityLayers.signature R) (CheckedEqualityLayers.CheckedEqualityLayers.signature (new_base R D e)) D E
    (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R) (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill (new_base R D e)) K Q (insertion R D e)
    (CheckedEqualityLayers.CheckedEqualityLayers.insertion_typed (CheckedEqualityLayers.CheckedEqualityLayers.request_budget (CheckedContextualFields.CheckedContextualFields.pack D e)) R)
    (CheckedEqualityLayers.CheckedEqualityLayers.insertion_index (CheckedEqualityLayers.CheckedEqualityLayers.request_budget (CheckedContextualFields.CheckedContextualFields.pack D e)) R)
    (CheckedEqualityLayers.CheckedEqualityLayers.insertion_fill (CheckedEqualityLayers.CheckedEqualityLayers.request_budget (CheckedContextualFields.CheckedContextualFields.pack D e)) R)
    (CheckedEqualityLayers.CheckedEqualityLayers.signature_wf (new_base R D e)) (CheckedEqualityLayers.CheckedEqualityLayers.identity_typed (new_base R D e)) HD.

Lemma lifted_decoder k R rs (D : ContextualTelescope.ContextualTelescope.telescope (CheckedEqualityLayers.CheckedEqualityLayers.width R) rs) e E r :
  lifted R D e (TarskiContext.TarskiContext.decoder E r) = TarskiContext.TarskiContext.decoder (inherited_environment k R rs D e E) r.
Proof. unfold lifted, TarskiContext.TarskiContext.decoder, inherited_environment, TarskiContext.TarskiContext.rename_environment; cbn [TarskiContext.TarskiContext.ren]; rewrite rename_comp; reflexivity. Qed.

Definition code_descriptor {k n G} (E : TarskiContext.TarskiContext.environment k n G) r a b :=
  CheckedEqualityFields.CheckedEqualityFields.Desc r (TarskiContext.TarskiContext.carrier E r) a b.
Definition allocate_codes k R rs (D : ContextualTelescope.ContextualTelescope.telescope (CheckedEqualityLayers.CheckedEqualityLayers.width R) rs)
    (E : TarskiContext.TarskiContext.environment k _ (ContextualTelescope.ContextualTelescope.context D (CheckedEqualityLayers.CheckedEqualityLayers.signature R))) r a b
    (HD : ContextualTelescope.ContextualTelescope.formed (CheckedEqualityLayers.CheckedEqualityLayers.signature R) D) (HN : ContextualTelescope.ContextualTelescope.normal_annotations D = true) (Hr : r <= S k)
    (Ha : @typ nat RankSorts _ (ContextualTelescope.ContextualTelescope.context D (CheckedEqualityLayers.CheckedEqualityLayers.signature R)) a (TarskiContext.TarskiContext.carrier E r))
    (Hb : @typ nat RankSorts _ (ContextualTelescope.ContextualTelescope.context D (CheckedEqualityLayers.CheckedEqualityLayers.signature R)) b (TarskiContext.TarskiContext.carrier E r))
    (HNa : normalb a = true) (HNb : normalb b = true)
    (Heq : def_equiv nat _ (ContextualEqualityExtension.ContextualEqualityExtension.filled (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R) a) (ContextualEqualityExtension.ContextualEqualityExtension.filled (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R) b)) :
    CheckedEqualityLayers.CheckedEqualityLayers.allocation R (CheckedContextualFields.CheckedContextualFields.pack D (code_descriptor E r a b)).
Proof.
  refine (CheckedEqualityLayers.CheckedEqualityLayers.allocate_original 0 R rs D (code_descriptor E r a b) HD HN _ Ha Hb _ HNa HNb Heq).
  - apply TarskiContext.TarskiContext.carrier_typed; exact Hr.
  - reflexivity.
Defined.

Definition align k R rs (D : ContextualTelescope.ContextualTelescope.telescope (CheckedEqualityLayers.CheckedEqualityLayers.width R) rs)
    (E : TarskiContext.TarskiContext.environment k _ (ContextualTelescope.ContextualTelescope.context D (CheckedEqualityLayers.CheckedEqualityLayers.signature R))) r a b
    (slot : CheckedEqualityLayers.CheckedEqualityLayers.allocation R (CheckedContextualFields.CheckedContextualFields.pack D (code_descriptor E r a b))) q :=
  transport R D (code_descriptor E r a b) slot (TarskiContext.TarskiContext.decoder E r) q.
Theorem align_typed k R rs (D : ContextualTelescope.ContextualTelescope.telescope (CheckedEqualityLayers.CheckedEqualityLayers.width R) rs) E r a b slot q :
  r <= S k -> @typ nat RankSorts _ (ContextualTelescope.ContextualTelescope.context D (CheckedEqualityLayers.CheckedEqualityLayers.signature R)) q (app (TarskiContext.TarskiContext.decoder E r) a) ->
  @typ nat RankSorts _
    (ContextualTelescope.ContextualTelescope.context (new_domains R D (code_descriptor E r a b))
      (CheckedEqualityLayers.CheckedEqualityLayers.signature (new_base R D (code_descriptor E r a b))))
    (align k R rs D E r a b slot q)
    (app (TarskiContext.TarskiContext.decoder (inherited_environment k R rs D (code_descriptor E r a b) E) r)
      (lifted R D (code_descriptor E r a b) b)).
Proof.
  intros Hr Hq; unfold align.
  rewrite <- lifted_decoder.
  change (app (lifted R D (code_descriptor E r a b) (TarskiContext.TarskiContext.decoder E r))
    (lifted R D (code_descriptor E r a b) b)) with
    (lifted R D (code_descriptor E r a b) (app (TarskiContext.TarskiContext.decoder E r) b)).
  apply transport_typed; [apply TarskiContext.TarskiContext.decoder_typed; exact Hr | exact Hq].
Qed.
Theorem align_normal k R rs (D : ContextualTelescope.ContextualTelescope.telescope (CheckedEqualityLayers.CheckedEqualityLayers.width R) rs) E r a b slot q :
  normalb q = true -> normalb (align k R rs D E r a b slot q) = true.
Proof. intro Hq; apply transport_normal; [reflexivity | exact Hq]. Qed.
Theorem align_neutral k R rs (D : ContextualTelescope.ContextualTelescope.telescope (CheckedEqualityLayers.CheckedEqualityLayers.width R) rs) E r a b slot q :
  isLambda (align k R rs D E r a b slot q) = false.
Proof. reflexivity. Qed.
Theorem align_erases k R rs (D : ContextualTelescope.ContextualTelescope.telescope (CheckedEqualityLayers.CheckedEqualityLayers.width R) rs) E r a b slot q :
  reduces_to nat _
    (replace (ContextualTelescope.ContextualTelescope.lift_sub rs (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill (new_base R D (code_descriptor E r a b))))
      (align k R rs D E r a b slot q)) (ContextualEqualityExtension.ContextualEqualityExtension.filled (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R) q).
Proof. apply transport_erases. Qed.
Theorem align_preserves_recovery k R rs (D : ContextualTelescope.ContextualTelescope.telescope (CheckedEqualityLayers.CheckedEqualityLayers.width R) rs) E r a b slot q t :
  reduces_to nat _ (ContextualEqualityExtension.ContextualEqualityExtension.filled (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R) q) t ->
  reduces_to nat _
    (replace (ContextualTelescope.ContextualTelescope.lift_sub rs (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill (new_base R D (code_descriptor E r a b))))
      (align k R rs D E r a b slot q)) t.
Proof. intro H; eapply rtc_trans; [apply align_erases | exact H]. Qed.

Print Assumptions preserve_realization.
Print Assumptions lifted_decoder.
Print Assumptions allocate_codes.
Print Assumptions align_typed.
Print Assumptions align_normal.
Print Assumptions align_neutral.
Print Assumptions align_erases.
Print Assumptions align_preserves_recovery.
Print Assumptions unpack_pack.
Print Assumptions value_pack.
Print Assumptions field_application_typed.
Print Assumptions field_application_normal.
Print Assumptions filled_new_domains.
Print Assumptions filled_lifted.
Print Assumptions transport_typed.
Print Assumptions transport_normal.
Print Assumptions transport_neutral.
Print Assumptions transport_erases.
End LayerCodeAlignment.
