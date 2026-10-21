From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting Congruence DefEq.
From PTSrk.NormalizationComplexity Require Import Greedy Morphisms.
From PTSrk.SelfInterpreter Require FullSource SourceValidity SourceQuotationBudget
  QuotationCache QuotationJudgment QuotationViewRenaming QuotationViewSubstitution
  CheckedEqualityLayers LocalQuotationSpine TarskiContext ScopedTarski FullQuotation
  LocalCodeAlignment TarskiSignature ApplicationQuotation.
Import Context ListNotations.

(** Structural recursion on ALL SIX independent original source rules.
    State and variable environments are maintained execution invariants;
    concrete empty initialization discharges them for closed inputs.
    No generated validity derivation or target quotation is an input. *)
Module RecursiveQuotation.
Lemma advance_inherited k R n H (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) p
    (t : Term nat (TarskiSignature.TarskiSignature.width k)) :
  rename (LocalQuotationSpine.LocalQuotationSpine.lift_ren n (FullQuotation.FullQuotation.embedding p R)) (rename (TarskiContext.TarskiContext.ren (FullQuotation.FullQuotation.environment st)) t) =
  rename (TarskiContext.TarskiContext.ren (FullQuotation.FullQuotation.environment (FullQuotation.FullQuotation.advance st p))) t.
Proof.
  rewrite rename_comp; apply rename_ext; intro i; symmetry.
  exact (LocalQuotationSpine.LocalQuotationSpine.environment_lifted_ren k _ n _ (LocalQuotationSpine.LocalQuotationSpine.domains st) (LocalQuotationSpine.LocalQuotationSpine.base_environment st)
    _ _ (FullQuotation.FullQuotation.embedding p R) (FullQuotation.FullQuotation.embedding_typed p R) i).
Qed.

Definition aligned_result {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) t T U
    (j : FullQuotation.FullQuotation.judgment st t T) r root (v : FullQuotation.FullQuotation.view st U r root)
    (HE : def_equiv nat n T U) : FullQuotation.FullQuotation.result st t U.
Proof.
  pose (a := LocalCodeAlignment.LocalCodeAlignment.align_judgment st t T U j r root v HE).
  exact {| FullQuotation.FullQuotation.result_plan := FullQuotation.FullQuotation.request (LocalCodeAlignment.LocalCodeAlignment.alignment_budget a);
    FullQuotation.FullQuotation.result_judgment := FullQuotation.FullQuotation.reframe_judgment (FullQuotation.FullQuotation.request_state k R n H st (LocalCodeAlignment.LocalCodeAlignment.alignment_budget a))
      (LocalCodeAlignment.LocalCodeAlignment.aligned a) |}.
Defined.

(** This is a nonrecursive terminal-mode repair. The finite typed view of
    t is built from its retained source shape, never by re-quoting a
    validity derivation. The equality field is computed independently. *)
Definition type_of_sort {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) t r
    (j : FullQuotation.FullQuotation.judgment st t (𝓤 r)) (Hr : r <= S k) : FullQuotation.FullQuotation.type_result st t r.
Proof.
  pose (a := LocalCodeAlignment.LocalCodeAlignment.align_judgment st t (𝓤 r) (𝓤 r) j 0 (TarskiContext.TarskiContext.universe (FullQuotation.FullQuotation.environment st) r)
    (QuotationJudgment.QuotationJudgment.universe_view (LocalQuotationSpine.LocalQuotationSpine.realized st) r Hr) ltac:(reflexivity)).
  pose (p := FullQuotation.FullQuotation.request (LocalCodeAlignment.LocalCodeAlignment.alignment_budget a)).
  pose (new := FullQuotation.FullQuotation.advance st p).
  pose (q := FullQuotation.FullQuotation.reframe_judgment (FullQuotation.FullQuotation.request_state k R n H st (LocalCodeAlignment.LocalCodeAlignment.alignment_budget a)) (LocalCodeAlignment.LocalCodeAlignment.aligned a)).
  assert (HQ : @typ nat RankSorts _ (LocalQuotationSpine.LocalQuotationSpine.context (LocalQuotationSpine.LocalQuotationSpine.domains new) (CheckedEqualityLayers.CheckedEqualityLayers.signature (FullQuotation.FullQuotation.run p R)))
    (QuotationJudgment.QuotationJudgment.term_code q) (ScopedTarski.ScopedTarski.decoded_universe (FullQuotation.FullQuotation.environment new) r)).
  { pose proof (QuotationJudgment.QuotationJudgment.term_typing q) as HT.
    change (typ (LocalQuotationSpine.LocalQuotationSpine.context (LocalQuotationSpine.LocalQuotationSpine.domains new) (CheckedEqualityLayers.CheckedEqualityLayers.signature (FullQuotation.FullQuotation.run p R)))
      (QuotationJudgment.QuotationJudgment.term_code q)
      (app (TarskiContext.TarskiContext.decoder (FullQuotation.FullQuotation.environment new) (QuotationJudgment.QuotationJudgment.result_rank (LocalCodeAlignment.LocalCodeAlignment.aligned a)))
        (QuotationJudgment.QuotationJudgment.type_code (LocalCodeAlignment.LocalCodeAlignment.aligned a)))) in HT.
    rewrite (LocalCodeAlignment.LocalCodeAlignment.aligned_rank a), (LocalCodeAlignment.LocalCodeAlignment.aligned_code a) in HT.
    unfold ScopedTarski.ScopedTarski.decoded_universe; unfold TarskiContext.TarskiContext.universe in HT |- *.
    change (rename (LocalQuotationSpine.LocalQuotationSpine.lift_ren n (CheckedEqualityLayers.CheckedEqualityLayers.insertion (LocalCodeAlignment.LocalCodeAlignment.alignment_budget a) R))
      (rename (TarskiContext.TarskiContext.ren (FullQuotation.FullQuotation.environment st)) (TarskiSignature.TarskiSignature.universe k r))) with
      (rename (LocalQuotationSpine.LocalQuotationSpine.lift_ren n (FullQuotation.FullQuotation.embedding p R))
        (rename (TarskiContext.TarskiContext.ren (FullQuotation.FullQuotation.environment st)) (TarskiSignature.TarskiSignature.universe k r))) in HT.
    rewrite (advance_inherited k R n H st p) in HT; exact HT. }
  exact {| FullQuotation.FullQuotation.type_plan := p;
    FullQuotation.FullQuotation.result_code := ScopedTarski.ScopedTarski.term_to_code (FullQuotation.FullQuotation.environment new) r (QuotationJudgment.QuotationJudgment.term_code q);
    FullQuotation.FullQuotation.result_view := QuotationJudgment.QuotationJudgment.term_as_code (LocalQuotationSpine.LocalQuotationSpine.realized new) r Hr (QuotationJudgment.QuotationJudgment.term_code q)
      (QuotationJudgment.QuotationJudgment.term_shape q) HQ (QuotationJudgment.QuotationJudgment.term_normal q) (QuotationJudgment.QuotationJudgment.term_recovers q) |}.
Defined.

Print Assumptions advance_inherited.
Print Assumptions aligned_result.
Print Assumptions type_of_sort.
(** The ONLY recursive argument is the independent source derivation.
    Synthesized validity/substitution proofs are never quoted recursively. *)
Fixpoint quote_derivation {n H t T} (d : FullSource.FullSource.derivation n H t T)
    (c : SourceValidity.SourceValidity.context_data n H) {k R} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H)
    (env : FullQuotation.FullQuotation.variables st) (HK : SourceQuotationBudget.SourceQuotationBudget.budget c d <= k) {struct d} :
    FullQuotation.FullQuotation.result st t T.
Proof.
  destruct d.
  - assert (Hr : r <= S k).
    { pose proof (SourceQuotationBudget.SourceQuotationBudget.judgment_literals_bounded _ _ _ _ (FullSource.FullSource.d_sort G r) c) as [_ [HL _]].
      change (r <= SourceQuotationBudget.SourceQuotationBudget.budget c (FullSource.FullSource.d_sort G r)) in HL; lia. }
    exact (FullQuotation.FullQuotation.unchanged st _ _ (QuotationJudgment.QuotationJudgment.sort_case (LocalQuotationSpine.LocalQuotationSpine.realized st) r Hr)).
  - destruct (SourceQuotationBudget.SourceQuotationBudget.pi_children _ _ _ _ _ _ d1 d2 c) as [H1 [H2 [Ha Hb]]].
    pose (HK1 := Nat.le_trans _ _ _ H1 HK).
    pose (HK2 := Nat.le_trans _ _ _ H2 HK).
    pose (HA := Nat.le_trans _ _ _ Ha HK).
    pose (HB := Nat.le_trans _ _ _ Hb HK).
    pose (qa := @quote_derivation _ _ _ _ d1 c k R st env HK1).
    pose (st1 := FullQuotation.FullQuotation.advance st (FullQuotation.FullQuotation.result_plan qa)).
    pose (va := type_of_sort st1 A a (FullQuotation.FullQuotation.result_judgment qa) ltac:(lia)).
    pose (st2 := FullQuotation.FullQuotation.advance st1 (FullQuotation.FullQuotation.type_plan va)).
    pose (env2 := FullQuotation.FullQuotation.advance_variables st1 (FullQuotation.FullQuotation.type_plan va)
      (FullQuotation.FullQuotation.advance_variables st (FullQuotation.FullQuotation.result_plan qa) env)).
    pose (child := FullQuotation.FullQuotation.push st2 A a (FullQuotation.FullQuotation.result_code va) (FullQuotation.FullQuotation.result_view va)).
    pose (qb := @quote_derivation _ _ _ _ d2 (SourceValidity.SourceValidity.cd_cons a c d1) k _ child
      (FullQuotation.FullQuotation.push_variables (FullQuotation.FullQuotation.result_view va) env2) HK2).
    pose (vb := type_of_sort (FullQuotation.FullQuotation.advance child (FullQuotation.FullQuotation.result_plan qb)) B b
      (FullQuotation.FullQuotation.result_judgment qb) ltac:(lia)).
    pose (closed := FullQuotation.FullQuotation.product_result st2 A B a b (FullQuotation.FullQuotation.result_code va) (FullQuotation.FullQuotation.result_view va) HA HB
      (FullQuotation.FullQuotation.sequence_type child (FullQuotation.FullQuotation.result_plan qb) B b vb)).
    exact (FullQuotation.FullQuotation.sequence st (FullQuotation.FullQuotation.result_plan qa) _ _
      (FullQuotation.FullQuotation.sequence st1 (FullQuotation.FullQuotation.type_plan va) _ _ closed)).
  - exact (FullQuotation.FullQuotation.unchanged st _ _ (env i)).
  - destruct (SourceQuotationBudget.SourceQuotationBudget.lambda_children _ _ _ _ _ _ d1 d2 c) as [H1 [H2 Ha]].
    pose (HK1 := Nat.le_trans _ _ _ H1 HK).
    pose (HK2 := Nat.le_trans _ _ _ H2 HK).
    pose (HA := Nat.le_trans _ _ _ Ha HK).
    pose (qa := @quote_derivation _ _ _ _ d1 c k R st env HK1).
    pose (st1 := FullQuotation.FullQuotation.advance st (FullQuotation.FullQuotation.result_plan qa)).
    pose (va := type_of_sort st1 A a (FullQuotation.FullQuotation.result_judgment qa) ltac:(lia)).
    pose (st2 := FullQuotation.FullQuotation.advance st1 (FullQuotation.FullQuotation.type_plan va)).
    pose (env2 := FullQuotation.FullQuotation.advance_variables st1 (FullQuotation.FullQuotation.type_plan va)
      (FullQuotation.FullQuotation.advance_variables st (FullQuotation.FullQuotation.result_plan qa) env)).
    pose (child := FullQuotation.FullQuotation.push st2 A a (FullQuotation.FullQuotation.result_code va) (FullQuotation.FullQuotation.result_view va)).
    pose (qb := @quote_derivation _ _ _ _ d2 (SourceValidity.SourceValidity.cd_cons a c d1) k _ child
      (FullQuotation.FullQuotation.push_variables (FullQuotation.FullQuotation.result_view va) env2) HK2).
    pose (HB := FullQuotation.FullQuotation.judgment_rank_bounded k _ _ _
      (FullQuotation.FullQuotation.advance child (FullQuotation.FullQuotation.result_plan qb)) _ _ d2 (SourceValidity.SourceValidity.cd_cons a c d1) (FullQuotation.FullQuotation.result_judgment qb) HK2).
    pose (closed := FullQuotation.FullQuotation.lambda_result st2 A t B a (FullQuotation.FullQuotation.result_code va) (FullQuotation.FullQuotation.result_view va) HA qb HB).
    exact (FullQuotation.FullQuotation.sequence st (FullQuotation.FullQuotation.result_plan qa) _ _
      (FullQuotation.FullQuotation.sequence st1 (FullQuotation.FullQuotation.type_plan va) _ _ closed)).
  - destruct (SourceQuotationBudget.SourceQuotationBudget.application_children _ _ _ _ _ _ d1 d2 c) as [H1 H2].
    pose (HK1 := Nat.le_trans _ _ _ H1 HK).
    pose (HK2 := Nat.le_trans _ _ _ H2 HK).
    pose (qf := @quote_derivation _ _ _ _ d1 c k R st env HK1).
    pose (st1 := FullQuotation.FullQuotation.advance st (FullQuotation.FullQuotation.result_plan qf)).
    pose (qu := @quote_derivation _ _ _ _ d2 c k _ st1
      (FullQuotation.FullQuotation.advance_variables st (FullQuotation.FullQuotation.result_plan qf) env) HK2).
    pose (st2 := FullQuotation.FullQuotation.advance st1 (FullQuotation.FullQuotation.result_plan qu)).
    pose (applied := ApplicationQuotation.ApplicationQuotation.application_result st2 f u A B
      (FullQuotation.FullQuotation.advance_judgment st1 (FullQuotation.FullQuotation.result_plan qu) _ _ (FullQuotation.FullQuotation.result_judgment qf))
      (FullQuotation.FullQuotation.result_judgment qu)).
    exact (FullQuotation.FullQuotation.sequence st (FullQuotation.FullQuotation.result_plan qf) _ _
      (FullQuotation.FullQuotation.sequence st1 (FullQuotation.FullQuotation.result_plan qu) _ _ applied)).
  - destruct (SourceQuotationBudget.SourceQuotationBudget.conversion_children _ _ _ _ _ _ d1 d2 c0 c) as [H1 [H2 Hb]].
    pose (HK1 := Nat.le_trans _ _ _ H1 HK).
    pose (HK2 := Nat.le_trans _ _ _ H2 HK).
    pose (HB := Nat.le_trans _ _ _ Hb HK).
    pose (qt := @quote_derivation _ _ _ _ d1 c k R st env HK1).
    pose (st1 := FullQuotation.FullQuotation.advance st (FullQuotation.FullQuotation.result_plan qt)).
    pose (qb := @quote_derivation _ _ _ _ d2 c k _ st1
      (FullQuotation.FullQuotation.advance_variables st (FullQuotation.FullQuotation.result_plan qt) env) HK2).
    pose (st2 := FullQuotation.FullQuotation.advance st1 (FullQuotation.FullQuotation.result_plan qb)).
    pose (vb := type_of_sort st2 B b (FullQuotation.FullQuotation.result_judgment qb) ltac:(lia)).
    pose (st3 := FullQuotation.FullQuotation.advance st2 (FullQuotation.FullQuotation.type_plan vb)).
    pose (old := FullQuotation.FullQuotation.advance_judgment st2 (FullQuotation.FullQuotation.type_plan vb) _ _
      (FullQuotation.FullQuotation.advance_judgment st1 (FullQuotation.FullQuotation.result_plan qb) _ _ (FullQuotation.FullQuotation.result_judgment qt))).
    pose (converted := aligned_result st3 t A B old b (FullQuotation.FullQuotation.result_code vb) (FullQuotation.FullQuotation.result_view vb)
      (FullSource.FullSource.conversion_sound _ _ _ c0)).
    exact (FullQuotation.FullQuotation.sequence st (FullQuotation.FullQuotation.result_plan qt) _ _
      (FullQuotation.FullQuotation.sequence st1 (FullQuotation.FullQuotation.result_plan qb) _ _
        (FullQuotation.FullQuotation.sequence st2 (FullQuotation.FullQuotation.type_plan vb) _ _ converted))).
Defined.

Print Assumptions quote_derivation.
End RecursiveQuotation.
