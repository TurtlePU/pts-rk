From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting DefEq.
From PTSrk.NormalizationComplexity Require Import Greedy Morphisms.
From PTSrk.SelfInterpreter Require Import CappedFullQuotation LocalQuotationSpine
  QuotationCache QuotationJudgment QuotationViewRenaming TarskiContext ScopedTarski
  CheckedEqualityLayers UniformTelescope CappedCodeAlignment CappedQuotationState.
Import Context ListNotations.

(** Application of independently obtained quotation judgments. The argument
    and function are aligned by actual checked equality-only layers; no
    source-specific internal equality or quotation oracle is an input. *)
Module CappedApplicationQuotation.

Definition advance_codomain {k R n H}
    (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H)
    A B a b Ac Bc (va : CappedFullQuotation.CappedFullQuotation.view st A a Ac)
    (vb : CappedFullQuotation.CappedFullQuotation.view (CappedFullQuotation.CappedFullQuotation.push st A a Ac va) B b Bc)
    p : CappedFullQuotation.CappedFullQuotation.view
      (CappedFullQuotation.CappedFullQuotation.push (CappedFullQuotation.CappedFullQuotation.advance st p) A a
        (rename (LocalQuotationSpine.LocalQuotationSpine.lift_ren n (CappedFullQuotation.CappedFullQuotation.embedding k p R)) Ac)
        (CappedFullQuotation.CappedFullQuotation.advance_view st p A a Ac va)) B b
      (rename (LocalQuotationSpine.LocalQuotationSpine.lift_ren (S n) (CappedFullQuotation.CappedFullQuotation.embedding k p R)) Bc) :=
  CappedFullQuotation.CappedFullQuotation.reframe_view
    (CappedFullQuotation.CappedFullQuotation.advance_push k R n H st A a Ac va p)
    (CappedFullQuotation.CappedFullQuotation.advance_view (CappedFullQuotation.CappedFullQuotation.push st A a Ac va) p B b Bc vb).

Lemma product_renames k R n H
    (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) p a b :
  rename (LocalQuotationSpine.LocalQuotationSpine.lift_ren n (CappedFullQuotation.CappedFullQuotation.embedding k p R))
    (TarskiContext.TarskiContext.product (CappedFullQuotation.CappedFullQuotation.environment st) a b) =
  TarskiContext.TarskiContext.product (CappedFullQuotation.CappedFullQuotation.environment (CappedFullQuotation.CappedFullQuotation.advance st p)) a b.
Proof.
  unfold TarskiContext.TarskiContext.product; rewrite rename_comp.
  apply rename_ext; intro i; unfold CappedFullQuotation.CappedFullQuotation.environment.
  cbn [CappedFullQuotation.CappedFullQuotation.advance LocalQuotationSpine.LocalQuotationSpine.domains
    LocalQuotationSpine.LocalQuotationSpine.base_environment].
  rewrite LocalQuotationSpine.LocalQuotationSpine.environment_lifted_ren; reflexivity.
Qed.

Lemma constructor_renames k R n H
    (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) p a b Ac Bc :
  rename (LocalQuotationSpine.LocalQuotationSpine.lift_ren n (CappedFullQuotation.CappedFullQuotation.embedding k p R))
    (QuotationCache.QuotationCache.constructed_product (CappedFullQuotation.CappedFullQuotation.environment st) a b Ac Bc) =
  QuotationCache.QuotationCache.constructed_product
    (CappedFullQuotation.CappedFullQuotation.environment (CappedFullQuotation.CappedFullQuotation.advance st p)) a b
    (rename (LocalQuotationSpine.LocalQuotationSpine.lift_ren n (CappedFullQuotation.CappedFullQuotation.embedding k p R)) Ac)
    (rename (LocalQuotationSpine.LocalQuotationSpine.lift_ren (S n) (CappedFullQuotation.CappedFullQuotation.embedding k p R)) Bc).
Proof.
  unfold QuotationCache.QuotationCache.constructed_product, TarskiContext.TarskiContext.product_code,
    ScopedTarski.ScopedTarski.family; cbn [rename].
  rewrite product_renames.
  rewrite (QuotationViewRenaming.QuotationViewRenaming.decoders _ _ _
    (CappedFullQuotation.CappedFullQuotation.advance_compatible k R n H st p)); reflexivity.
Qed.

Print Assumptions advance_codomain.
Print Assumptions constructor_renames.

Lemma advance_program_typed k R n H
    (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) p r code q :
  @typ nat RankSorts _
    (LocalQuotationSpine.LocalQuotationSpine.context (LocalQuotationSpine.LocalQuotationSpine.domains st)
      (CheckedEqualityLayers.CheckedEqualityLayers.signature R)) q
    (app (TarskiContext.TarskiContext.decoder (CappedFullQuotation.CappedFullQuotation.environment st) r) code) ->
  @typ nat RankSorts _
    (LocalQuotationSpine.LocalQuotationSpine.context
      (LocalQuotationSpine.LocalQuotationSpine.domains (CappedFullQuotation.CappedFullQuotation.advance st p))
      (CheckedEqualityLayers.CheckedEqualityLayers.signature (CappedFullQuotation.CappedFullQuotation.run k p R)))
    (rename (LocalQuotationSpine.LocalQuotationSpine.lift_ren n (CappedFullQuotation.CappedFullQuotation.embedding k p R)) q)
    (app (TarskiContext.TarskiContext.decoder (CappedFullQuotation.CappedFullQuotation.environment (CappedFullQuotation.CappedFullQuotation.advance st p)) r)
      (rename (LocalQuotationSpine.LocalQuotationSpine.lift_ren n (CappedFullQuotation.CappedFullQuotation.embedding k p R)) code)).
Proof.
  intro HQ.
  rewrite <- (QuotationViewRenaming.QuotationViewRenaming.decoders _ _ _
    (CappedFullQuotation.CappedFullQuotation.advance_compatible k R n H st p)).
  change (typ
    (LocalQuotationSpine.LocalQuotationSpine.context
      (LocalQuotationSpine.LocalQuotationSpine.domains (CappedFullQuotation.CappedFullQuotation.advance st p))
      (CheckedEqualityLayers.CheckedEqualityLayers.signature (CappedFullQuotation.CappedFullQuotation.run k p R)))
    (rename (LocalQuotationSpine.LocalQuotationSpine.lift_ren n (CappedFullQuotation.CappedFullQuotation.embedding k p R)) q)
    (rename (LocalQuotationSpine.LocalQuotationSpine.lift_ren n (CappedFullQuotation.CappedFullQuotation.embedding k p R))
      (app (TarskiContext.TarskiContext.decoder (CappedFullQuotation.CappedFullQuotation.environment st) r) code))).
  eapply typing_rename; [| exact HQ].
  apply LocalQuotationSpine.LocalQuotationSpine.context_ren,
    CappedFullQuotation.CappedFullQuotation.embedding_typed.
Qed.

Lemma advance_program_recovers k R n H
    (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) p q t :
  reduces_to nat n (replace (CappedFullQuotation.CappedFullQuotation.source_fill n R) q) t ->
  reduces_to nat n (replace (CappedFullQuotation.CappedFullQuotation.source_fill n (CappedFullQuotation.CappedFullQuotation.run k p R))
    (rename (LocalQuotationSpine.LocalQuotationSpine.lift_ren n (CappedFullQuotation.CappedFullQuotation.embedding k p R)) q)) t.
Proof.
  intro HQ.
  rewrite (QuotationViewRenaming.QuotationViewRenaming.square_replace _ _ _ _ _ _ _ _ _
    (CappedFullQuotation.CappedFullQuotation.advance_square k R n H st p)), rename_id; exact HQ.
Qed.

Print Assumptions advance_program_typed.
Print Assumptions advance_program_recovers.

(** Reframing the actual single-layer allocator changes no program or root
    code. Only original contexts and inherited variable maps are compared. *)
Definition aligned_judgment {k R n H}
    (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) t U r root
    (al : CappedCodeAlignment.CappedCodeAlignment.alignment st t U r root) :
  CappedFullQuotation.CappedFullQuotation.judgment
    (CappedFullQuotation.CappedFullQuotation.advance st
      (CappedFullQuotation.CappedFullQuotation.request (CappedCodeAlignment.CappedCodeAlignment.alignment_budget al))) t U :=
  CappedFullQuotation.CappedFullQuotation.reframe_judgment
    (CappedFullQuotation.CappedFullQuotation.request_state k R n H st
      (CappedCodeAlignment.CappedCodeAlignment.alignment_budget al))
    (CappedCodeAlignment.CappedCodeAlignment.aligned al).

Lemma aligned_code k R n H (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H)
    t U r root (al : CappedCodeAlignment.CappedCodeAlignment.alignment st t U r root) :
  QuotationJudgment.QuotationJudgment.type_code (aligned_judgment st t U r root al) =
  rename (LocalQuotationSpine.LocalQuotationSpine.lift_ren n
    (CappedFullQuotation.CappedFullQuotation.embedding k
      (CappedFullQuotation.CappedFullQuotation.request (CappedCodeAlignment.CappedCodeAlignment.alignment_budget al)) R)) root.
Proof. exact (CappedCodeAlignment.CappedCodeAlignment.aligned_code al). Qed.

Lemma aligned_rank k R n H (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H)
    t U r root (al : CappedCodeAlignment.CappedCodeAlignment.alignment st t U r root) :
  QuotationJudgment.QuotationJudgment.result_rank (aligned_judgment st t U r root al) = r.
Proof. exact (CappedCodeAlignment.CappedCodeAlignment.aligned_rank al). Qed.

Definition application_result {k R n H}
    (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) f u A B
    (jf : CappedFullQuotation.CappedFullQuotation.judgment st f (Π A B))
    (ju : CappedFullQuotation.CappedFullQuotation.judgment st u A)
    (HBnd : CappedQuotationState.CappedQuotationState.bounded st) :
  CappedFullQuotation.CappedFullQuotation.result st (app f u) (subst B u).
Proof.
  destruct (QuotationJudgment.QuotationJudgment.invert_product
    (QuotationJudgment.QuotationJudgment.type_view jf))
    as [a b Ac Bc Ha Hb Hrank va vb].
  assert (HAeq : def_equiv nat n A A) by reflexivity.
  pose (au := CappedCodeAlignment.CappedCodeAlignment.align_judgment st u A A ju a Ac va HAeq HBnd).
  pose (p1 := CappedFullQuotation.CappedFullQuotation.request (CappedCodeAlignment.CappedCodeAlignment.alignment_budget au)).
  pose (st1 := CappedFullQuotation.CappedFullQuotation.advance st p1).
  pose (Ac1 := rename (LocalQuotationSpine.LocalQuotationSpine.lift_ren n
    (CappedFullQuotation.CappedFullQuotation.embedding k p1 R)) Ac).
  pose (Bc1 := rename (LocalQuotationSpine.LocalQuotationSpine.lift_ren (S n)
    (CappedFullQuotation.CappedFullQuotation.embedding k p1 R)) Bc).
  pose (va1 := CappedFullQuotation.CappedFullQuotation.advance_view st p1 A a Ac va).
  pose (vb1 := advance_codomain st A B a b Ac Bc va vb p1).
  pose (vp1 := QuotationCache.QuotationCache.build_product_view Ha Hb va1 vb1
    (QuotationCache.QuotationCache.realization_product _ _ _ _ _ _ _
      (LocalQuotationSpine.LocalQuotationSpine.realized st1) a b Ha Hb)).
  pose (jf1 := CappedFullQuotation.CappedFullQuotation.advance_judgment st p1 f (Π A B) jf).
  assert (HPeq : def_equiv nat n (Π A B) (Π A B)) by reflexivity.
  pose (af := CappedCodeAlignment.CappedCodeAlignment.align_judgment st1 f (Π A B) (Π A B) jf1
    (Nat.max (S a) b)
    (QuotationCache.QuotationCache.constructed_product (CappedFullQuotation.CappedFullQuotation.environment st1) a b Ac1 Bc1)
    vp1 HPeq ltac:(apply CappedFullQuotation.CappedFullQuotation.advance_bounded; exact HBnd)).
  pose (p2 := CappedFullQuotation.CappedFullQuotation.request (CappedCodeAlignment.CappedCodeAlignment.alignment_budget af)).
  pose (st2 := CappedFullQuotation.CappedFullQuotation.advance st1 p2).
  pose (va2 := CappedFullQuotation.CappedFullQuotation.advance_view st1 p2 A a Ac1 va1).
  pose (vb2 := advance_codomain st1 A B a b Ac1 Bc1 va1 vb1 p2).
  pose (ju1 := aligned_judgment st u A a Ac au).
  pose (jf2 := aligned_judgment st1 f (Π A B) (Nat.max (S a) b)
    (QuotationCache.QuotationCache.constructed_product (CappedFullQuotation.CappedFullQuotation.environment st1) a b Ac1 Bc1) af).
  pose (ju2 := CappedFullQuotation.CappedFullQuotation.advance_judgment st1 p2 u A ju1).
  pose (qu2 := rename (LocalQuotationSpine.LocalQuotationSpine.lift_ren n
    (CappedFullQuotation.CappedFullQuotation.embedding k p2 (CappedFullQuotation.CappedFullQuotation.run k p1 R)))
    (QuotationJudgment.QuotationJudgment.term_code ju1)).
  pose proof (QuotationJudgment.QuotationJudgment.term_typing ju1) as Hu1.
  change (typ (LocalQuotationSpine.LocalQuotationSpine.context
      (LocalQuotationSpine.LocalQuotationSpine.domains st1)
      (CheckedEqualityLayers.CheckedEqualityLayers.signature (CappedFullQuotation.CappedFullQuotation.run k p1 R)))
    (QuotationJudgment.QuotationJudgment.term_code ju1)
    (app (TarskiContext.TarskiContext.decoder (CappedFullQuotation.CappedFullQuotation.environment st1)
      (QuotationJudgment.QuotationJudgment.result_rank (aligned_judgment st u A a Ac au)))
      (QuotationJudgment.QuotationJudgment.type_code (aligned_judgment st u A a Ac au)))) in Hu1.
  rewrite aligned_rank, aligned_code in Hu1.
  pose proof (advance_program_typed k _ n H st1 p2 a Ac1
    (QuotationJudgment.QuotationJudgment.term_code ju1) Hu1) as Hu2.
  pose proof (QuotationJudgment.QuotationJudgment.term_typing jf2) as Hf2.
  change (typ (LocalQuotationSpine.LocalQuotationSpine.context
      (LocalQuotationSpine.LocalQuotationSpine.domains st2)
      (CheckedEqualityLayers.CheckedEqualityLayers.signature
        (CappedFullQuotation.CappedFullQuotation.run k p2 (CappedFullQuotation.CappedFullQuotation.run k p1 R))))
    (QuotationJudgment.QuotationJudgment.term_code jf2)
    (app (TarskiContext.TarskiContext.decoder (CappedFullQuotation.CappedFullQuotation.environment st2)
      (QuotationJudgment.QuotationJudgment.result_rank (aligned_judgment st1 f (Π A B) (Nat.max (S a) b)
        (QuotationCache.QuotationCache.constructed_product (CappedFullQuotation.CappedFullQuotation.environment st1) a b Ac1 Bc1) af)))
      (QuotationJudgment.QuotationJudgment.type_code (aligned_judgment st1 f (Π A B) (Nat.max (S a) b)
        (QuotationCache.QuotationCache.constructed_product (CappedFullQuotation.CappedFullQuotation.environment st1) a b Ac1 Bc1) af)))) in Hf2.
  rewrite aligned_rank, aligned_code, constructor_renames in Hf2.
  apply (CappedFullQuotation.CappedFullQuotation.sequence st p1 (app f u) (subst B u)).
  refine {| CappedFullQuotation.CappedFullQuotation.result_plan := p2 |}.
  refine (QuotationJudgment.QuotationJudgment.application_case
    (LocalQuotationSpine.LocalQuotationSpine.realized st2) Ha Hb va2 vb2
    (QuotationJudgment.QuotationJudgment.term_code jf2) qu2
    (QuotationJudgment.QuotationJudgment.term_shape jf2) (QuotationJudgment.QuotationJudgment.term_shape ju2)
    Hf2 Hu2 (QuotationJudgment.QuotationJudgment.term_normal jf2) _ _
    (QuotationJudgment.QuotationJudgment.term_recovers jf2) _).
  - unfold qu2; rewrite UniformTelescope.UniformTelescope.normalb_rename;
      exact (QuotationJudgment.QuotationJudgment.term_normal ju1).
  - unfold qu2; rewrite UniformTelescope.UniformTelescope.isLambda_rename;
      exact (QuotationJudgment.QuotationJudgment.term_neutral ju1).
  - exact (advance_program_recovers k _ n H st1 p2
      (QuotationJudgment.QuotationJudgment.term_code ju1) u
      (QuotationJudgment.QuotationJudgment.term_recovers ju1)).
Defined.

Theorem exactly_two_layers k R n H
    (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) f u A B
    (jf : CappedFullQuotation.CappedFullQuotation.judgment st f (Π A B))
    (ju : CappedFullQuotation.CappedFullQuotation.judgment st u A)
    (HBnd : CappedQuotationState.CappedQuotationState.bounded st) :
  List.length (CappedFullQuotation.CappedFullQuotation.flatten
    (CappedFullQuotation.CappedFullQuotation.result_plan (application_result st f u A B jf ju HBnd))) = 2.
Proof.
  unfold application_result.
  destruct (QuotationJudgment.QuotationJudgment.invert_product
    (QuotationJudgment.QuotationJudgment.type_view jf)); reflexivity.
Qed.

Print Assumptions aligned_judgment.
Print Assumptions aligned_code.
Print Assumptions aligned_rank.
Print Assumptions application_result.
Print Assumptions exactly_two_layers.
End CappedApplicationQuotation.
