From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting Congruence DefEq.
From PTSrk.NormalizationComplexity Require Import Greedy Morphisms.
From PTSrk.SelfInterpreter Require Import ContextualTelescope
  ContextualTelescopeRun ContextReification DependentProgramDecoder
  ClosedQuotationPackage FullDependentInterpreter IndexedProgramInterpreter
  FullQuotation QuotationJudgment QuotationCache FullSource ChurchSyntaxFaithful Algebra
  SourceClosure SourceValidity.
Import Context ListNotations.

(** One interface for a dependent algebra and its fold.  Its fields are
    ORIGINAL PTS terms with an ORIGINAL typed simultaneous substitution.
    The same algebra interprets types, terms and the coherence fields.
    No raw-HOAS fidelity envelope and no numeral conversion occurs here.

    A signature may still depend on a finite quotation plan.  This module
    does not identify all those signatures with one rank-only signature,
    and an arbitrary filling must establish its actual coherence fields. *)
Module UnifiedAlgebra.
Include Algebra.Algebra.
Module CP := ClosedQuotationPackage.ClosedQuotationPackage.
Module FD := FullDependentInterpreter.FullDependentInterpreter.
Module IP := IndexedProgramInterpreter.IndexedProgramInterpreter.
Module FQ := FullQuotation.FullQuotation.
Module QJ := QuotationJudgment.QuotationJudgment.
Module QC := QuotationCache.QuotationCache.
Module FS := FullSource.FullSource.

(** All-source instantiation of the common API.  The existing independent
    six-rule derivation drives quotation; the raw tag is never projected,
    inspected, or used to establish these contracts. *)
Definition quotation {t T} (d : FS.derivation 0 ε t T) := FD.closed_quote d.
Definition plan {t T} (d : FS.derivation 0 ε t T) := FQ.result_plan (quotation d).
Definition signature {t T} (d : FS.derivation 0 ε t T) :=
  IP.signature (FD.closed_budget d) (plan d).
Definition interface {t T} (d : FS.derivation 0 ε t T) := CP.domains (signature d).
Definition judgment {t T} (d : FS.derivation 0 ε t T) :=
  FQ.result_judgment (quotation d).
Definition result_rank {t T} (d : FS.derivation 0 ε t T) := QJ.result_rank (judgment d).
Definition carrier {t T} (d : FS.derivation 0 ε t T) :=
  CP.carrier (IP.environment (FD.closed_budget d) (plan d)) (result_rank d).
Definition element {t T} (d : FS.derivation 0 ε t T) :=
  CP.element (IP.environment (FD.closed_budget d) (plan d)) (result_rank d).
Definition type_program {t T} (d : FS.derivation 0 ε t T) := CP.type_program (judgment d).
Definition term_program {t T} (d : FS.derivation 0 ε t T) := CP.payload (judgment d).

Definition identity_algebra {t T} (d : FS.derivation 0 ε t T) : algebra (interface d).
Proof.
  refine {| fields := CP.identity (signature d)
    (IP.identity (FD.closed_budget d) (plan d)) |}.
  apply CR.fill_typed.
  exact (QC.realization_typed _ _ _
    (IP.original_realization (FD.closed_budget d) (plan d))).
Defined.

Theorem interface_formed t T (d : FS.derivation 0 ε t T) :
  CT.formed ε (interface d).
Proof.
  apply CR.reify_formed.
  exact (QC.realization_target_wf _ _ _
    (IP.original_realization (FD.closed_budget d) (plan d))).
Qed.

Theorem type_program_typed t T (d : FS.derivation 0 ε t T) :
  @typ nat RankSorts 0 ε (type_program d)
    (DP.type_program_type (interface d) (carrier d)).
Proof. apply CP.type_program_typed, IP.original_realization. Qed.

Theorem term_program_typed t T (d : FS.derivation 0 ε t T) :
  @typ nat RankSorts 0 ε (term_program d)
    (DP.term_program_type (interface d) (element d) (type_program d)).
Proof.
  apply DP.package_typed with (s := result_rank d) (C := carrier d).
  - apply interface_formed.
  - apply CP.element_typed, CP.result_bound.
  - apply CP.type_body_typed.
  - apply CP.term_body_typed.
Qed.

Theorem programs_normal t T (d : FS.derivation 0 ε t T) :
  normalb (type_program d) = true /\ normalb (term_program d) = true.
Proof.
  split; [apply CP.type_program_normal | apply CP.payload_normal];
    apply IP.signature_normal.
Qed.

Definition interpreted_type {t T} (d : FS.derivation 0 ε t T)
    (A : algebra (interface d)) :=
  DP.result_type (interface d) (fields A) (element d) (type_program d).

Theorem arbitrary_algebra_typed t T (d : FS.derivation 0 ε t T)
    (A : algebra (interface d)) :
  @typ nat RankSorts 0 ε (fold A (term_program d)) (interpreted_type d A).
Proof. apply fold_typed, term_program_typed. Qed.

Theorem identity_term_recovers t T (d : FS.derivation 0 ε t T) :
  reduces_to nat 0 (fold (identity_algebra d) (term_program d)) t.
Proof.
  eapply rtc_trans; [apply fold_closure |].
  change (reduces_to nat 0
    (replace (CP.identity (signature d) (IP.identity (FD.closed_budget d) (plan d)))
      (CP.term_body (judgment d))) t).
  unfold CP.identity, CP.term_body; rewrite CR.filled_body.
  apply QJ.term_recovers.
Qed.

Theorem identity_type_recovers t T (d : FS.derivation 0 ε t T) :
  reduces_to nat 0 (fold (identity_algebra d) (type_program d)) T.
Proof. apply CP.type_program_recovers. Qed.

Theorem identity_result_recovers t T (d : FS.derivation 0 ε t T) :
  reduces_to nat 0 (interpreted_type d (identity_algebra d)) T.
Proof. apply CP.output_recovers, IP.original_realization. Qed.

Theorem identity_original_type t T (d : FS.derivation 0 ε t T) :
  @typ nat RankSorts 0 ε (fold (identity_algebra d) (term_program d)) T.
Proof.
  eapply typ_conv with (T := interpreted_type d (identity_algebra d))
    (ℓ := result_rank d).
  - apply arbitrary_algebra_typed.
  - apply CP.source_type_sort, IP.original_realization.
  - apply def_equiv_prop; exists T; split; [apply identity_result_recovers | reflexivity].
Qed.

(** One actual normal fold head for any selected algebra. Its ordinary
    inputs are represented TYPE P and TERM Q, with no fidelity envelope. *)
Definition head {t T} (d : FS.derivation 0 ε t T) (A : algebra (interface d)) :=
  DP.decoder (interface d) (fields A) (carrier d) (element d).
Definition head_type {t T} (d : FS.derivation 0 ε t T) (A : algebra (interface d)) :=
  DP.decoder_type (interface d) (fields A) (carrier d) (element d).

Theorem head_typed t T (d : FS.derivation 0 ε t T) (A : algebra (interface d)) :
  @typ nat RankSorts 0 ε (head d A) (head_type d A).
Proof.
  apply DP.decoder_typed with (s := result_rank d).
  - apply interface_formed.
  - apply CP.carrier_typed, CP.result_bound.
  - apply CP.element_typed, CP.result_bound.
  - apply fields_typed.
Qed.

Theorem head_computes t T (d : FS.derivation 0 ε t T)
    (A : algebra (interface d)) P Q :
  reduces_to nat 0 (app (app (head d A) P) Q) (fold A Q).
Proof. apply DP.decode_reduces. Qed.

Theorem head_normal t T (d : FS.derivation 0 ε t T) (A : algebra (interface d)) :
  (forall i, normalb (fields A i) = true) -> normalb (head d A) = true.
Proof.
  intro HA; apply DP.decoder_normal.
  - unfold interface, CP.domains; rewrite CR.reify_normal; apply IP.signature_normal.
  - unfold carrier, CP.carrier; rewrite CR.body_normal; reflexivity.
  - apply CP.element_normal.
  - apply CP.element_neutral.
  - exact HA.
Qed.

Theorem identity_fields_normal t T (d : FS.derivation 0 ε t T) i :
  normalb (fields (identity_algebra d) i) = true.
Proof. apply CR.fill_normal, IP.identity_normal. Qed.

Definition interpret {t T} (d : FS.derivation 0 ε t T)
    (A : algebra (interface d)) :=
  app (app (head d A) (type_program d)) (term_program d).

Theorem interpret_typed t T (d : FS.derivation 0 ε t T)
    (A : algebra (interface d)) :
  @typ nat RankSorts 0 ε (interpret d A) (interpreted_type d A).
Proof.
  apply DP.decode_typed with (s := result_rank d).
  - apply interface_formed.
  - apply CP.carrier_typed, CP.result_bound.
  - apply CP.element_typed, CP.result_bound.
  - apply fields_typed.
  - apply type_program_typed.
  - apply term_program_typed.
Qed.

Theorem interpret_recovers t T (d : FS.derivation 0 ε t T) :
  reduces_to nat 0 (interpret d (identity_algebra d)) t.
Proof. eapply rtc_trans; [apply head_computes | apply identity_term_recovers]. Qed.

Theorem interpret_original_type t T (d : FS.derivation 0 ε t T) :
  @typ nat RankSorts 0 ε (interpret d (identity_algebra d)) T.
Proof.
  eapply typ_conv with (T := interpreted_type d (identity_algebra d))
    (ℓ := result_rank d).
  - apply interpret_typed.
  - apply CP.source_type_sort, IP.original_realization.
  - apply def_equiv_prop; exists T; split; [apply identity_result_recovers | reflexivity].
Qed.

(** Open sources use literal annotated closure and reopening. They retain
    the common algebra API; no semantic source normalization is inserted. *)
Definition open_interpret {n G t T}
    (c : SourceValidity.SourceValidity.context_data n G)
    (d : FS.derivation n G t T) :=
  let q := SourceClosure.SourceClosure.close c t T d in
  SourceClosure.SourceClosure.reopen G (interpret q (identity_algebra q)).

Theorem open_recovers n G t T (c : SourceValidity.SourceValidity.context_data n G)
    (d : FS.derivation n G t T) :
  reduces_to nat n (open_interpret c d) t.
Proof. apply SourceClosure.SourceClosure.reopen_recovers, interpret_recovers. Qed.

Theorem open_original_type n G t T (c : SourceValidity.SourceValidity.context_data n G)
    (d : FS.derivation n G t T) :
  @typ nat RankSorts n G (open_interpret c d) T.
Proof. apply SourceClosure.SourceClosure.reopen_typed, interpret_original_type. Qed.

Theorem every_closed_original t T : @typ nat RankSorts 0 ε t T ->
  exists d : FS.derivation 0 ε t T,
    normalb (type_program d) = true /\ normalb (term_program d) = true /\
    normalb (head d (identity_algebra d)) = true /\
    @typ nat RankSorts 0 ε (fold (identity_algebra d) (term_program d)) T /\
    reduces_to nat 0 (fold (identity_algebra d) (term_program d)) t /\
    reduces_to nat 0 (fold (identity_algebra d) (type_program d)) T.
Proof.
  intro HT; destruct (FS.derivation_complete _ _ _ _ HT) as [d]; exists d.
  destruct (programs_normal _ _ d) as [HP HQ]; repeat split; try assumption.
  - apply head_normal, identity_fields_normal.
  - apply identity_original_type.
  - apply identity_term_recovers.
  - apply identity_type_recovers.
Qed.

(** Recovery reflects conversion through a COMMON algebra. Normal source
    representatives therefore need no separate syntax tag. This does NOT
    assert literal fidelity for arbitrary unreduced source syntax, nor for
    unrelated signatures/fillings. The legacy faithful API keeps that
    stronger cross-plan contract until an intrinsic parser is proved. *)
Theorem recovery_reflects_conversion rs (D : CT.telescope 0 rs) (A : algebra D)
    (Q R t u : Term nat 0) :
  reduces_to nat 0 (fold A Q) t -> reduces_to nat 0 (fold A R) u ->
  def_equiv nat 0 Q R -> def_equiv nat 0 t u.
Proof.
  intros Ht Hu HQR.
  transitivity (fold A Q).
  - apply def_equiv_prop; exists t; split; [reflexivity | exact Ht].
  - transitivity (fold A R); [apply fold_conversion; exact HQR |].
    apply def_equiv_prop; exists u; split; [exact Hu | reflexivity].
Qed.

Theorem normal_recovery_injective rs (D : CT.telescope 0 rs) (A : algebra D)
    (Q R t u : Term nat 0) :
  reduces_to nat 0 (fold A Q) t -> reduces_to nat 0 (fold A R) u ->
  normalb t = true -> normalb u = true -> def_equiv nat 0 Q R -> t = u.
Proof.
  intros Ht Hu HNt HNu HE; apply normal_conversion_identity; try assumption.
  eapply recovery_reflects_conversion; eassumption.
Qed.

Print Assumptions identity_algebra.
Print Assumptions interface_formed.
Print Assumptions type_program_typed.
Print Assumptions term_program_typed.
Print Assumptions programs_normal.
Print Assumptions arbitrary_algebra_typed.
Print Assumptions identity_term_recovers.
Print Assumptions identity_type_recovers.
Print Assumptions identity_result_recovers.
Print Assumptions identity_original_type.
Print Assumptions head_typed.
Print Assumptions head_computes.
Print Assumptions head_normal.
Print Assumptions identity_fields_normal.
Print Assumptions interpret_typed.
Print Assumptions interpret_recovers.
Print Assumptions interpret_original_type.
Print Assumptions open_recovers.
Print Assumptions open_original_type.
Print Assumptions every_closed_original.
Print Assumptions recovery_reflects_conversion.
Print Assumptions normal_recovery_injective.
End UnifiedAlgebra.
