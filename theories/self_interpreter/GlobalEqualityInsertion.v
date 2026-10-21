From Stdlib Require Import Bool.Bool Lists.List.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting DefEq.
From PTSrk.NormalizationComplexity Require Import Morphisms Greedy.
From PTSrk.SelfInterpreter Require Import BrownPalsberg ContextualTelescope
  UniformTelescope ContextualTelescopeRun ContextualEqualityExtension
  CodeAlignment TarskiContext QuotationCache QuotationViewRenaming.
Import Context ListNotations.

(** Insert an independently realized GLOBAL equality field beneath all
    local binders while retaining the LITERAL original source context.
    No equality of that context with a substituted telescope is assumed. *)
Module GlobalEqualityInsertion.
Module BP := BrownPalsberg.BrownPalsberg.
Module CT := ContextualTelescope.ContextualTelescope.
Module UT := UniformTelescope.UniformTelescope.
Module TR := ContextualTelescopeRun.ContextualTelescopeRun.
Module EX := ContextualEqualityExtension.ContextualEqualityExtension.
Module CA := CodeAlignment.CodeAlignment.
Module CX := TarskiContext.TarskiContext.
Module QC := QuotationCache.QuotationCache.
Module VR := QuotationViewRenaming.QuotationViewRenaming.

Lemma context_index_renamed m rs (D : CT.telescope m rs) : forall n G H rho,
  (forall i, H !! rho i = rename rho (G !! i)) -> forall i,
  CT.context (CT.rename_telescope D n rho) H !! CT.lift_ren rs rho i =
    rename (CT.lift_ren rs rho) (CT.context D G !! i).
Proof.
  induction D; intros p G H rho HI i; cbn [CT.context CT.rename_telescope CT.lift_ren].
  - apply HI.
  - apply IHD; intro j; dependent elimination j as [fzero | fsucc j].
    + change (shift (rename rho A) = rename (weak rho) (shift A)); syntax_simp.
    + change (shift (H !! rho j) = rename (weak rho) (shift (G !! j))).
      rewrite HI; syntax_simp.
Qed.

Lemma lift_ren_cover rs : forall m n (rho : Fin m -> Fin n) hole,
  (forall j, j = hole \/ exists i, j = rho i) -> forall j,
  j = UT.base_ren rs hole \/ exists i, j = CT.lift_ren rs rho i.
Proof.
  induction rs; intros m n rho hole HC j; cbn [UT.base_ren CT.lift_ren].
  - apply HC.
  - apply IHrs; intro i; dependent elimination i as [fzero | fsucc i].
    + right; exists fzero; reflexivity.
    + destruct (HC i) as [HE | [x HE]]; subst i.
      * left; reflexivity.
      * right; exists (fsucc x); reflexivity.
Qed.

Lemma insertion_cover n rs (j : Fin (CT.scope rs (S n))) :
  j = UT.base_ren rs fzero \/ exists i, j = CT.lift_ren rs fsucc i.
Proof.
  apply lift_ren_cover; intro i; dependent elimination i as [fzero | fsucc i].
  - left; reflexivity.
  - right; exists i; reflexivity.
Qed.

Theorem insertion_typed n rs (G : Ctx nat n) (D : CT.telescope n rs)
    (H : Ctx nat (CT.scope rs 0)) sigma X w :
  TypedSub (CT.context D G) H (CT.lift_sub rs sigma) ->
  @typ nat RankSorts 0 ε w (replace sigma X) ->
  TypedSub (CT.context (EX.shifted_domains D) (G & X)) H
    (CT.lift_sub rs (fin_match w sigma)).
Proof.
  intros HS Hw j; destruct (insertion_cover n rs j) as [HE | [i HE]]; subst j.
  - rewrite TR.index_base, UT.lift_sub_base_variable, UT.lift_sub_base.
    change (typ H (rename (UT.base_ren rs) w)
      (rename (UT.base_ren rs) (replace (fin_match w sigma) (shift X)))).
    replace (replace (fin_match w sigma) (shift X)) with (replace sigma X)
      by (unfold shift; rewrite replace_rename; reflexivity).
    apply typing_rename with (G := ε); [intros i; dependent elimination i | exact Hw].
  - unfold EX.shifted_domains.
    rewrite (context_index_renamed n rs D (S n) G (G & X) fsucc (fun _ => eq_refl)).
    rewrite replace_rename.
    assert (HQ : forall i, CT.lift_sub rs (fin_match w sigma)
      (CT.lift_ren rs fsucc i) = CT.lift_sub rs sigma i).
    { apply CA.lift_sub_square; intro z; reflexivity. }
    rewrite HQ, (replace_ext _ _ HQ); apply HS.
Qed.

Definition equality_realization k c d n rs (G : Ctx nat n) (D : CT.telescope n rs)
    (E : CX.environment k _ (CT.context D G)) sigma (H : Ctx nat (CT.scope rs 0))
    (R : QC.realization E (CT.lift_sub rs sigma) H) C u v
    (HG : @wf nat RankSorts n G) (HS : TypedSub G ε sigma) (HD : CT.formed G D)
    (HC : @typ nat RankSorts _ (CT.context D G) C (𝓤 c))
    (Hu : @typ nat RankSorts _ (CT.context D G) u C)
    (Hv : @typ nat RankSorts _ (CT.context D G) v C)
    (Heq : def_equiv nat _ (EX.filled sigma u) (EX.filled sigma v)) :
    QC.realization (CA.aligned_environment k d n rs G D C u v E)
      (CT.lift_sub rs (EX.fill d D sigma C u)) H.
Proof.
  constructor.
  - exact (QC.realization_source_wf _ _ _ R).
  - apply EX.local_context_wf with (c := c); assumption.
  - apply insertion_typed; [exact (QC.realization_typed _ _ _ R) |].
    apply EX.value_typed with (c := c) (G := G) (v := v); assumption.
  - intro i; change (CT.lift_sub rs (EX.fill d D sigma C u)
      (CT.lift_ren rs fsucc (CX.ren E i)) = @QC.TS.fill k (CT.scope rs 0) i).
    rewrite (CA.lift_sub_square rs n (S n) 0 fsucc sigma
      (EX.fill d D sigma C u) (fun _ => eq_refl)).
    exact (QC.realization_fields _ _ _ R i).
Defined.

Lemma equality_square d n rs (D : CT.telescope n rs) sigma C u :
  VR.square (CT.lift_sub rs sigma) (CT.lift_sub rs (EX.fill d D sigma C u))
    (fun i => i) (CT.lift_ren rs fsucc).
Proof.
  intro i; rewrite rename_id; apply CA.lift_sub_square; intro j; reflexivity.
Qed.

Definition lift_view k d n rs (G : Ctx nat n) (D : CT.telescope n rs)
    E sigma C u v t r code
    (V : QC.code_view k (CT.scope rs 0) (CT.scope rs n) (CT.context D G) E
      (CT.lift_sub rs sigma) t r code) :
    QC.code_view k (CT.scope rs 0) (CT.scope rs (S n))
      (CT.context (EX.shifted_domains D) (EX.extension d G D C u v))
      (CA.aligned_environment k d n rs G D C u v E)
      (CT.lift_sub rs (EX.fill d D sigma C u)) t r (EX.lifted code).
Proof.
  pose proof (VR.rename_view V _ (CA.aligned_environment k d n rs G D C u v E)
    (CT.lift_sub rs (EX.fill d D sigma C u)) (fun i => i) (CT.lift_ren rs fsucc)
    (CT.context_ren n rs D G (S n) _ fsucc (typed_ren_shift G (EX.declaration d D C u v)))
    (VR.compatible_renaming k _ _ _ _ E _ _) (equality_square d n rs D sigma C u)) as W.
  rewrite rename_id in W; exact W.
Defined.

Definition lift_shape k d n rs (G : Ctx nat n) (D : CT.telescope n rs)
    E sigma C u v t
    (V : QC.shape_view k (CT.scope rs 0) (CT.scope rs n) (CT.context D G) E
      (CT.lift_sub rs sigma) t) :
    QC.shape_view k (CT.scope rs 0) (CT.scope rs (S n))
      (CT.context (EX.shifted_domains D) (EX.extension d G D C u v))
      (CA.aligned_environment k d n rs G D C u v E)
      (CT.lift_sub rs (EX.fill d D sigma C u)) t.
Proof.
  pose proof (VR.rename_shape V _ (CA.aligned_environment k d n rs G D C u v E)
    (CT.lift_sub rs (EX.fill d D sigma C u)) (fun i => i) (CT.lift_ren rs fsucc)
    (CT.context_ren n rs D G (S n) _ fsucc (typed_ren_shift G (EX.declaration d D C u v)))
    (VR.compatible_renaming k _ _ _ _ E _ _) (equality_square d n rs D sigma C u)) as W.
  rewrite rename_id in W; exact W.
Defined.

(** The same source-context-preserving argument works for an entire
    independently realized finite base extension, not only one field. *)
Lemma lift_ren_base rs : forall m n (rho : Fin m -> Fin n) i,
  CT.lift_ren rs rho (UT.base_ren rs i) = UT.base_ren rs (rho i).
Proof.
  induction rs; intros m n rho i; cbn [CT.lift_ren UT.base_ren]; [reflexivity |].
  rewrite IHrs; reflexivity.
Qed.

Lemma local_or_base rs : forall m n (rho : Fin m -> Fin n) j,
  (exists i, j = UT.base_ren rs i) \/ exists i, j = CT.lift_ren rs rho i.
Proof.
  induction rs; intros m n rho j; [left; exists j; reflexivity |].
  cbn [CT.lift_ren UT.base_ren].
  destruct (IHrs (S m) (S n) (weak rho) j) as [[i HE] | [i HE]].
  - dependent elimination i as [fzero | fsucc i].
    + right; exists (UT.base_ren rs fzero); rewrite lift_ren_base; exact HE.
    + left; exists i; exact HE.
  - right; exists i; exact HE.
Qed.

Theorem base_extension_typed m n rs (G : Ctx nat m) (B : Ctx nat n)
    (D : CT.telescope m rs) (K : Ctx nat (CT.scope rs 0)) rho sigma tau :
  (forall i, B !! rho i = rename rho (G !! i)) ->
  (forall i, tau (rho i) = sigma i) ->
  TypedSub (CT.context D G) K (CT.lift_sub rs sigma) -> TypedSub B ε tau ->
  TypedSub (CT.context (CT.rename_telescope D n rho) B) K (CT.lift_sub rs tau).
Proof.
  intros HI HF HS HT j; destruct (local_or_base rs m n rho j) as [[i HE] | [i HE]]; subst j.
  - rewrite TR.index_base, UT.lift_sub_base_variable, UT.lift_sub_base.
    apply typing_rename with (G := ε); [intros z; dependent elimination z | apply HT].
  - rewrite (context_index_renamed m rs D n G B rho HI), replace_rename.
    pose proof (CA.lift_sub_square rs m n 0 rho sigma tau HF) as HQ.
    rewrite HQ, (replace_ext _ _ HQ); apply HS.
Qed.

Definition base_extension_realization k m n rs (G : Ctx nat m) (B : Ctx nat n)
    (D : CT.telescope m rs) E sigma tau (K : Ctx nat (CT.scope rs 0))
    (R : QC.realization E (CT.lift_sub rs sigma) K) rho
    (HR : TypedRen G B rho)
    (HI : forall i, B !! rho i = rename rho (G !! i))
    (HF : forall i, tau (rho i) = sigma i)
    (HB : @wf nat RankSorts n B) (HT : TypedSub B ε tau) (HD : CT.formed G D) :
    QC.realization
      (CX.rename_environment k _ _ (CT.context D G)
        (CT.context (CT.rename_telescope D n rho) B) E (CT.lift_ren rs rho)
        (CT.context_ren m rs D G n B rho HR))
      (CT.lift_sub rs tau) K.
Proof.
  constructor.
  - exact (QC.realization_source_wf _ _ _ R).
  - apply CT.formed_wf; [exact HB | apply CT.formed_rename with (G := G); assumption].
  - apply base_extension_typed with (G := G) (sigma := sigma); try assumption.
    exact (QC.realization_typed _ _ _ R).
  - intro i; change (CT.lift_sub rs tau (CT.lift_ren rs rho (CX.ren E i)) =
      @QC.TS.fill k (CT.scope rs 0) i).
    rewrite (CA.lift_sub_square rs m n 0 rho sigma tau HF).
    exact (QC.realization_fields _ _ _ R i).
Defined.

Print Assumptions context_index_renamed.
Print Assumptions insertion_cover.
Print Assumptions insertion_typed.
Print Assumptions equality_realization.
Print Assumptions equality_square.
Print Assumptions lift_view.
Print Assumptions lift_shape.
Print Assumptions base_extension_typed.
Print Assumptions base_extension_realization.
End GlobalEqualityInsertion.
