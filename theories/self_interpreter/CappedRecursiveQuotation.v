From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting Congruence DefEq.
From PTSrk.NormalizationComplexity Require Import Greedy Morphisms.
From PTSrk.SelfInterpreter Require FullSource SourceValidity SourceQuotationBudget
  QuotationCache QuotationJudgment QuotationViewRenaming QuotationViewSubstitution
  CheckedEqualityLayers LocalQuotationSpine TarskiContext ScopedTarski CappedFullQuotation
  CappedCodeAlignment TarskiSignature CappedApplicationQuotation CappedQuotationState.
Import Context ListNotations.

(** Structural recursion on ALL SIX independent original source rules.
    State and variable environments are maintained execution invariants;
    concrete empty initialization discharges them for closed inputs.
    No generated validity derivation or target quotation is an input. *)
Module CappedRecursiveQuotation.
Lemma advance_inherited k R n H (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) p
    (t : Term nat (TarskiSignature.TarskiSignature.width k)) :
  rename (LocalQuotationSpine.LocalQuotationSpine.lift_ren n (CappedFullQuotation.CappedFullQuotation.embedding k p R)) (rename (TarskiContext.TarskiContext.ren (CappedFullQuotation.CappedFullQuotation.environment st)) t) =
  rename (TarskiContext.TarskiContext.ren (CappedFullQuotation.CappedFullQuotation.environment (CappedFullQuotation.CappedFullQuotation.advance st p))) t.
Proof.
  rewrite rename_comp; apply rename_ext; intro i; symmetry.
  exact (LocalQuotationSpine.LocalQuotationSpine.environment_lifted_ren k _ n _ (LocalQuotationSpine.LocalQuotationSpine.domains st) (LocalQuotationSpine.LocalQuotationSpine.base_environment st)
    _ _ (CappedFullQuotation.CappedFullQuotation.embedding k p R) (CappedFullQuotation.CappedFullQuotation.embedding_typed k p R) i).
Qed.

Definition aligned_result {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) t T U
    (j : CappedFullQuotation.CappedFullQuotation.judgment st t T) r root (v : CappedFullQuotation.CappedFullQuotation.view st U r root)
    (HE : def_equiv nat n T U) (HBnd : CappedQuotationState.CappedQuotationState.bounded st) : CappedFullQuotation.CappedFullQuotation.result st t U.
Proof.
  pose (a := CappedCodeAlignment.CappedCodeAlignment.align_judgment st t T U j r root v HE HBnd).
  exact {| CappedFullQuotation.CappedFullQuotation.result_plan := CappedFullQuotation.CappedFullQuotation.request (CappedCodeAlignment.CappedCodeAlignment.alignment_budget a);
    CappedFullQuotation.CappedFullQuotation.result_judgment := CappedFullQuotation.CappedFullQuotation.reframe_judgment (CappedFullQuotation.CappedFullQuotation.request_state k R n H st (CappedCodeAlignment.CappedCodeAlignment.alignment_budget a))
      (CappedCodeAlignment.CappedCodeAlignment.aligned a) |}.
Defined.

(** This is a nonrecursive terminal-mode repair. The finite typed view of
    t is built from its retained source shape, never by re-quoting a
    validity derivation. The equality field is computed independently. *)
Definition type_of_sort {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) t r
    (j : CappedFullQuotation.CappedFullQuotation.judgment st t (𝓤 r)) (Hr : r <= S k) (HBnd : CappedQuotationState.CappedQuotationState.bounded st) : CappedFullQuotation.CappedFullQuotation.type_result st t r.
Proof.
  pose (a := CappedCodeAlignment.CappedCodeAlignment.align_judgment st t (𝓤 r) (𝓤 r) j 0 (TarskiContext.TarskiContext.universe (CappedFullQuotation.CappedFullQuotation.environment st) r)
    (QuotationJudgment.QuotationJudgment.universe_view (LocalQuotationSpine.LocalQuotationSpine.realized st) r Hr) ltac:(reflexivity) HBnd).
  pose (p := CappedFullQuotation.CappedFullQuotation.request (CappedCodeAlignment.CappedCodeAlignment.alignment_budget a)).
  pose (new := CappedFullQuotation.CappedFullQuotation.advance st p).
  pose (q := CappedFullQuotation.CappedFullQuotation.reframe_judgment (CappedFullQuotation.CappedFullQuotation.request_state k R n H st (CappedCodeAlignment.CappedCodeAlignment.alignment_budget a)) (CappedCodeAlignment.CappedCodeAlignment.aligned a)).
  assert (HQ : @typ nat RankSorts _ (LocalQuotationSpine.LocalQuotationSpine.context (LocalQuotationSpine.LocalQuotationSpine.domains new) (CheckedEqualityLayers.CheckedEqualityLayers.signature (CappedFullQuotation.CappedFullQuotation.run k p R)))
    (QuotationJudgment.QuotationJudgment.term_code q) (ScopedTarski.ScopedTarski.decoded_universe (CappedFullQuotation.CappedFullQuotation.environment new) r)).
  { pose proof (QuotationJudgment.QuotationJudgment.term_typing q) as HT.
    change (typ (LocalQuotationSpine.LocalQuotationSpine.context (LocalQuotationSpine.LocalQuotationSpine.domains new) (CheckedEqualityLayers.CheckedEqualityLayers.signature (CappedFullQuotation.CappedFullQuotation.run k p R)))
      (QuotationJudgment.QuotationJudgment.term_code q)
      (app (TarskiContext.TarskiContext.decoder (CappedFullQuotation.CappedFullQuotation.environment new) (QuotationJudgment.QuotationJudgment.result_rank (CappedCodeAlignment.CappedCodeAlignment.aligned a)))
        (QuotationJudgment.QuotationJudgment.type_code (CappedCodeAlignment.CappedCodeAlignment.aligned a)))) in HT.
    rewrite (CappedCodeAlignment.CappedCodeAlignment.aligned_rank a), (CappedCodeAlignment.CappedCodeAlignment.aligned_code a) in HT.
    unfold ScopedTarski.ScopedTarski.decoded_universe; unfold TarskiContext.TarskiContext.universe in HT |- *.
    change (rename (LocalQuotationSpine.LocalQuotationSpine.lift_ren n (CappedCodeAlignment.CappedCodeAlignment.insertion k (CappedCodeAlignment.CappedCodeAlignment.alignment_budget a) R))
      (rename (TarskiContext.TarskiContext.ren (CappedFullQuotation.CappedFullQuotation.environment st)) (TarskiSignature.TarskiSignature.universe k r))) with
      (rename (LocalQuotationSpine.LocalQuotationSpine.lift_ren n (CappedFullQuotation.CappedFullQuotation.embedding k p R))
        (rename (TarskiContext.TarskiContext.ren (CappedFullQuotation.CappedFullQuotation.environment st)) (TarskiSignature.TarskiSignature.universe k r))) in HT.
    rewrite (advance_inherited k R n H st p) in HT; exact HT. }
  exact {| CappedFullQuotation.CappedFullQuotation.type_plan := p;
    CappedFullQuotation.CappedFullQuotation.result_code := ScopedTarski.ScopedTarski.term_to_code (CappedFullQuotation.CappedFullQuotation.environment new) r (QuotationJudgment.QuotationJudgment.term_code q);
    CappedFullQuotation.CappedFullQuotation.result_view := QuotationJudgment.QuotationJudgment.term_as_code (LocalQuotationSpine.LocalQuotationSpine.realized new) r Hr (QuotationJudgment.QuotationJudgment.term_code q)
      (QuotationJudgment.QuotationJudgment.term_shape q) HQ (QuotationJudgment.QuotationJudgment.term_normal q) (QuotationJudgment.QuotationJudgment.term_recovers q) |}.
Defined.

Print Assumptions advance_inherited.
Print Assumptions aligned_result.
Print Assumptions type_of_sort.
(** The ONLY recursive argument is the independent source derivation.
    Synthesized validity/substitution proofs are never quoted recursively. *)
Ltac bounded_spine :=
  first [assumption
    | apply CappedFullQuotation.CappedFullQuotation.advance_bounded; bounded_spine
    | apply CappedFullQuotation.CappedFullQuotation.push_bounded; [bounded_spine|lia]].

Fixpoint quote_derivation {n H t T} (d : FullSource.FullSource.derivation n H t T)
    (c : SourceValidity.SourceValidity.context_data n H) {k R} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H)
    (env : CappedFullQuotation.CappedFullQuotation.variables st) (HK : SourceQuotationBudget.SourceQuotationBudget.budget c d <= k)
    (HBnd : CappedQuotationState.CappedQuotationState.bounded st) {struct d} :
    CappedFullQuotation.CappedFullQuotation.result st t T.
Proof.
  destruct d.
  - assert (Hr : r <= S k).
    { pose proof (SourceQuotationBudget.SourceQuotationBudget.judgment_literals_bounded _ _ _ _ (FullSource.FullSource.d_sort G r) c) as [_ [HL _]].
      change (r <= SourceQuotationBudget.SourceQuotationBudget.budget c (FullSource.FullSource.d_sort G r)) in HL; lia. }
    exact (CappedFullQuotation.CappedFullQuotation.unchanged st _ _ (QuotationJudgment.QuotationJudgment.sort_case (LocalQuotationSpine.LocalQuotationSpine.realized st) r Hr)).
  - destruct (SourceQuotationBudget.SourceQuotationBudget.pi_children _ _ _ _ _ _ d1 d2 c) as [H1 [H2 [Ha Hb]]].
    pose (HK1 := Nat.le_trans _ _ _ H1 HK).
    pose (HK2 := Nat.le_trans _ _ _ H2 HK).
    pose (HA := Nat.le_trans _ _ _ Ha HK).
    pose (HB := Nat.le_trans _ _ _ Hb HK).
    pose (qa := @quote_derivation _ _ _ _ d1 c k R st env HK1 ltac:(bounded_spine)).
    pose (st1 := CappedFullQuotation.CappedFullQuotation.advance st (CappedFullQuotation.CappedFullQuotation.result_plan qa)).
    pose (va := type_of_sort st1 A a (CappedFullQuotation.CappedFullQuotation.result_judgment qa) ltac:(lia) ltac:(bounded_spine)).
    pose (st2 := CappedFullQuotation.CappedFullQuotation.advance st1 (CappedFullQuotation.CappedFullQuotation.type_plan va)).
    pose (env2 := CappedFullQuotation.CappedFullQuotation.advance_variables st1 (CappedFullQuotation.CappedFullQuotation.type_plan va)
      (CappedFullQuotation.CappedFullQuotation.advance_variables st (CappedFullQuotation.CappedFullQuotation.result_plan qa) env)).
    pose (child := CappedFullQuotation.CappedFullQuotation.push st2 A a (CappedFullQuotation.CappedFullQuotation.result_code va) (CappedFullQuotation.CappedFullQuotation.result_view va)).
    pose (qb := @quote_derivation _ _ _ _ d2 (SourceValidity.SourceValidity.cd_cons a c d1) k _ child
      (CappedFullQuotation.CappedFullQuotation.push_variables (CappedFullQuotation.CappedFullQuotation.result_view va) env2) HK2 ltac:(bounded_spine)).
    pose (vb := type_of_sort (CappedFullQuotation.CappedFullQuotation.advance child (CappedFullQuotation.CappedFullQuotation.result_plan qb)) B b
      (CappedFullQuotation.CappedFullQuotation.result_judgment qb) ltac:(lia) ltac:(bounded_spine)).
    pose (closed := CappedFullQuotation.CappedFullQuotation.product_result st2 A B a b (CappedFullQuotation.CappedFullQuotation.result_code va) (CappedFullQuotation.CappedFullQuotation.result_view va) HA HB
      (CappedFullQuotation.CappedFullQuotation.sequence_type child (CappedFullQuotation.CappedFullQuotation.result_plan qb) B b vb)).
    exact (CappedFullQuotation.CappedFullQuotation.sequence st (CappedFullQuotation.CappedFullQuotation.result_plan qa) _ _
      (CappedFullQuotation.CappedFullQuotation.sequence st1 (CappedFullQuotation.CappedFullQuotation.type_plan va) _ _ closed)).
  - exact (CappedFullQuotation.CappedFullQuotation.unchanged st _ _ (env i)).
  - destruct (SourceQuotationBudget.SourceQuotationBudget.lambda_children _ _ _ _ _ _ d1 d2 c) as [H1 [H2 Ha]].
    pose (HK1 := Nat.le_trans _ _ _ H1 HK).
    pose (HK2 := Nat.le_trans _ _ _ H2 HK).
    pose (HA := Nat.le_trans _ _ _ Ha HK).
    pose (qa := @quote_derivation _ _ _ _ d1 c k R st env HK1 ltac:(bounded_spine)).
    pose (st1 := CappedFullQuotation.CappedFullQuotation.advance st (CappedFullQuotation.CappedFullQuotation.result_plan qa)).
    pose (va := type_of_sort st1 A a (CappedFullQuotation.CappedFullQuotation.result_judgment qa) ltac:(lia) ltac:(bounded_spine)).
    pose (st2 := CappedFullQuotation.CappedFullQuotation.advance st1 (CappedFullQuotation.CappedFullQuotation.type_plan va)).
    pose (env2 := CappedFullQuotation.CappedFullQuotation.advance_variables st1 (CappedFullQuotation.CappedFullQuotation.type_plan va)
      (CappedFullQuotation.CappedFullQuotation.advance_variables st (CappedFullQuotation.CappedFullQuotation.result_plan qa) env)).
    pose (child := CappedFullQuotation.CappedFullQuotation.push st2 A a (CappedFullQuotation.CappedFullQuotation.result_code va) (CappedFullQuotation.CappedFullQuotation.result_view va)).
    pose (qb := @quote_derivation _ _ _ _ d2 (SourceValidity.SourceValidity.cd_cons a c d1) k _ child
      (CappedFullQuotation.CappedFullQuotation.push_variables (CappedFullQuotation.CappedFullQuotation.result_view va) env2) HK2 ltac:(bounded_spine)).
    pose (HB := CappedFullQuotation.CappedFullQuotation.judgment_rank_bounded k _ _ _
      (CappedFullQuotation.CappedFullQuotation.advance child (CappedFullQuotation.CappedFullQuotation.result_plan qb)) _ _ d2 (SourceValidity.SourceValidity.cd_cons a c d1) (CappedFullQuotation.CappedFullQuotation.result_judgment qb) HK2).
    pose (closed := CappedFullQuotation.CappedFullQuotation.lambda_result st2 A t B a (CappedFullQuotation.CappedFullQuotation.result_code va) (CappedFullQuotation.CappedFullQuotation.result_view va) HA qb HB).
    exact (CappedFullQuotation.CappedFullQuotation.sequence st (CappedFullQuotation.CappedFullQuotation.result_plan qa) _ _
      (CappedFullQuotation.CappedFullQuotation.sequence st1 (CappedFullQuotation.CappedFullQuotation.type_plan va) _ _ closed)).
  - destruct (SourceQuotationBudget.SourceQuotationBudget.application_children _ _ _ _ _ _ d1 d2 c) as [H1 H2].
    pose (HK1 := Nat.le_trans _ _ _ H1 HK).
    pose (HK2 := Nat.le_trans _ _ _ H2 HK).
    pose (qf := @quote_derivation _ _ _ _ d1 c k R st env HK1 ltac:(bounded_spine)).
    pose (st1 := CappedFullQuotation.CappedFullQuotation.advance st (CappedFullQuotation.CappedFullQuotation.result_plan qf)).
    pose (qu := @quote_derivation _ _ _ _ d2 c k _ st1
      (CappedFullQuotation.CappedFullQuotation.advance_variables st (CappedFullQuotation.CappedFullQuotation.result_plan qf) env) HK2 ltac:(bounded_spine)).
    pose (st2 := CappedFullQuotation.CappedFullQuotation.advance st1 (CappedFullQuotation.CappedFullQuotation.result_plan qu)).
    pose (applied := CappedApplicationQuotation.CappedApplicationQuotation.application_result st2 f u A B
      (CappedFullQuotation.CappedFullQuotation.advance_judgment st1 (CappedFullQuotation.CappedFullQuotation.result_plan qu) _ _ (CappedFullQuotation.CappedFullQuotation.result_judgment qf))
      (CappedFullQuotation.CappedFullQuotation.result_judgment qu) ltac:(bounded_spine)).
    exact (CappedFullQuotation.CappedFullQuotation.sequence st (CappedFullQuotation.CappedFullQuotation.result_plan qf) _ _
      (CappedFullQuotation.CappedFullQuotation.sequence st1 (CappedFullQuotation.CappedFullQuotation.result_plan qu) _ _ applied)).
  - destruct (SourceQuotationBudget.SourceQuotationBudget.conversion_children _ _ _ _ _ _ d1 d2 c0 c) as [H1 [H2 Hb]].
    pose (HK1 := Nat.le_trans _ _ _ H1 HK).
    pose (HK2 := Nat.le_trans _ _ _ H2 HK).
    pose (HB := Nat.le_trans _ _ _ Hb HK).
    pose (qt := @quote_derivation _ _ _ _ d1 c k R st env HK1 ltac:(bounded_spine)).
    pose (st1 := CappedFullQuotation.CappedFullQuotation.advance st (CappedFullQuotation.CappedFullQuotation.result_plan qt)).
    pose (qb := @quote_derivation _ _ _ _ d2 c k _ st1
      (CappedFullQuotation.CappedFullQuotation.advance_variables st (CappedFullQuotation.CappedFullQuotation.result_plan qt) env) HK2 ltac:(bounded_spine)).
    pose (st2 := CappedFullQuotation.CappedFullQuotation.advance st1 (CappedFullQuotation.CappedFullQuotation.result_plan qb)).
    pose (vb := type_of_sort st2 B b (CappedFullQuotation.CappedFullQuotation.result_judgment qb) ltac:(lia) ltac:(bounded_spine)).
    pose (st3 := CappedFullQuotation.CappedFullQuotation.advance st2 (CappedFullQuotation.CappedFullQuotation.type_plan vb)).
    pose (old := CappedFullQuotation.CappedFullQuotation.advance_judgment st2 (CappedFullQuotation.CappedFullQuotation.type_plan vb) _ _
      (CappedFullQuotation.CappedFullQuotation.advance_judgment st1 (CappedFullQuotation.CappedFullQuotation.result_plan qb) _ _ (CappedFullQuotation.CappedFullQuotation.result_judgment qt))).
    pose (converted := aligned_result st3 t A B old b (CappedFullQuotation.CappedFullQuotation.result_code vb) (CappedFullQuotation.CappedFullQuotation.result_view vb)
      (FullSource.FullSource.conversion_sound _ _ _ c0) ltac:(bounded_spine)).
    exact (CappedFullQuotation.CappedFullQuotation.sequence st (CappedFullQuotation.CappedFullQuotation.result_plan qt) _ _
      (CappedFullQuotation.CappedFullQuotation.sequence st1 (CappedFullQuotation.CappedFullQuotation.result_plan qb) _ _
        (CappedFullQuotation.CappedFullQuotation.sequence st2 (CappedFullQuotation.CappedFullQuotation.type_plan vb) _ _ converted))).
Defined.

Print Assumptions quote_derivation.
End CappedRecursiveQuotation.
