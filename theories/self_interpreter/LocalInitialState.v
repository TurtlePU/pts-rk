From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks.
From PTSrk.NormalizationComplexity Require Import Morphisms Greedy.
From PTSrk.SelfInterpreter Require Import NormalEqualityFill LocalQuotationSpine
  CheckedEqualityLayers TarskiContext TarskiSignature QuotationCache QuotationJudgment.
Import Context ListNotations.

(** Concrete initialization at the LITERAL empty original source context.
    The target is the existing finite Tarski signature with its actual
    identity filling. No recursive quotation theorem is an input. *)
Module LocalInitialState.

Definition initial k : LocalQuotationSpine.LocalQuotationSpine.state k
    (NormalEqualityFill.NormalEqualityFill.base k) 0 ε :=
  LocalQuotationSpine.LocalQuotationSpine.initial_state k
    (NormalEqualityFill.NormalEqualityFill.base k)
    (TarskiContext.TarskiContext.base_environment k) (fun i => eq_refl).

Definition after k bs := LocalQuotationSpine.LocalQuotationSpine.extend_state (initial k) bs.
Definition signature k bs := CheckedEqualityLayers.CheckedEqualityLayers.signature
  (CheckedEqualityLayers.CheckedEqualityLayers.build bs (NormalEqualityFill.NormalEqualityFill.base k)).
Definition identity k bs := CheckedEqualityLayers.CheckedEqualityLayers.identity_fill
  (CheckedEqualityLayers.CheckedEqualityLayers.build bs (NormalEqualityFill.NormalEqualityFill.base k)).
Definition environment k bs := LocalQuotationSpine.LocalQuotationSpine.environment
  (LocalQuotationSpine.LocalQuotationSpine.domains (after k bs))
  (LocalQuotationSpine.LocalQuotationSpine.base_environment (after k bs)).

Definition initial_variables k := QuotationJudgment.QuotationJudgment.empty_environment
  (TarskiContext.TarskiContext.base_environment k) (@TarskiSignature.TarskiSignature.fill k 0).
Definition after_variables k bs := QuotationJudgment.QuotationJudgment.empty_environment
  (environment k bs) (identity k bs).

Theorem initial_domains k :
  LocalQuotationSpine.LocalQuotationSpine.domains (initial k) =
  @LocalQuotationSpine.LocalQuotationSpine.empty (TarskiSignature.TarskiSignature.width k).
Proof. reflexivity. Qed.
Theorem after_domains k bs :
  LocalQuotationSpine.LocalQuotationSpine.domains (after k bs) =
  @LocalQuotationSpine.LocalQuotationSpine.empty
    (CheckedEqualityLayers.CheckedEqualityLayers.width
      (CheckedEqualityLayers.CheckedEqualityLayers.build bs (NormalEqualityFill.NormalEqualityFill.base k))).
Proof. reflexivity. Qed.
Theorem original_wf k bs : @wf nat RankSorts _ (signature k bs).
Proof. apply CheckedEqualityLayers.CheckedEqualityLayers.signature_wf. Qed.
Theorem original_fill k bs : TypedSub (signature k bs) ε (identity k bs).
Proof. apply CheckedEqualityLayers.CheckedEqualityLayers.identity_typed. Qed.
Theorem signature_normal k bs : PHOASTelescope.PHOASTelescope.normal_context (signature k bs) = true.
Proof. apply CheckedEqualityLayers.CheckedEqualityLayers.signature_normal. Qed.
Theorem identity_normal k bs i : normalb (identity k bs i) = true.
Proof. apply NormalEqualityFill.NormalEqualityFill.concrete_normal. Qed.
Theorem environment_embedding k bs i : TarskiContext.TarskiContext.ren (environment k bs) i =
  CheckedEqualityLayers.CheckedEqualityLayers.embedding bs (NormalEqualityFill.NormalEqualityFill.base k) i.
Proof. reflexivity. Qed.
Theorem inherited_identity k bs i : identity k bs (TarskiContext.TarskiContext.ren (environment k bs) i) =
  @TarskiSignature.TarskiSignature.fill k 0 i.
Proof. apply CheckedEqualityLayers.CheckedEqualityLayers.embedding_fill. Qed.
Definition original_realization k bs : QuotationCache.QuotationCache.realization
    (environment k bs) (identity k bs) ε :=
  LocalQuotationSpine.LocalQuotationSpine.realized (after k bs).

Print Assumptions initial.
Print Assumptions initial_variables.
Print Assumptions after_variables.
Print Assumptions initial_domains.
Print Assumptions after_domains.
Print Assumptions original_wf.
Print Assumptions original_fill.
Print Assumptions signature_normal.
Print Assumptions identity_normal.
Print Assumptions environment_embedding.
Print Assumptions inherited_identity.
Print Assumptions original_realization.
End LocalInitialState.
