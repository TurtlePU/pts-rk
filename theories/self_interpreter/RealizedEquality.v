From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting Congruence DefEq.
From PTSrk.NormalizationComplexity Require Import Greedy Morphisms.
From PTSrk.SelfInterpreter Require Import BrownPalsberg IndexedEquality OpenCanonical
  UniformTelescopeRecovery PHOASTelescope.
Import Context.

(** Equality-only extension of an already realized context. Endpoints must
    have independent ORIGINAL typing, and their actual realizations must
    already be convertible. Neither target quotation nor a semantic payload
    inhabitant is supplied by a new equality field. A uniform bounded
    enumeration of these extensions is a SEPARATE obligation. *)
Module RealizedEquality.
Module BP := BrownPalsberg.BrownPalsberg.
Module IE := IndexedEquality.IndexedEquality.
Module OC := OpenCanonical.OpenCanonical.
Module UR := UniformTelescopeRecovery.UniformTelescopeRecovery.
Module PT := PHOASTelescope.PHOASTelescope.

Lemma eq_type_reduces d n (C C' u u' v v' : Term nat n) :
  reduces_to nat n C C' -> reduces_to nat n u u' -> reduces_to nat n v v' ->
  reduces_to nat n (IE.eq_type d C u v) (IE.eq_type d C' u' v').
Proof.
  intros HC Hu Hv; unfold IE.eq_type, IE.motive_type.
  apply (@Π_cong_par nat (reduces_to nat) _ _ n).
  - apply BP.arr_reduces; [exact HC | reflexivity].
  - apply BP.arr_reduces; apply (@app_cong_r nat (reduces_to nat) _ (S n)), rename_rtc; assumption.
Qed.

Definition normal_reflexivity d {n} (G : Ctx nat n) (C u : Term nat n) :=
  IE.refl_case d (OC.nf G C) (OC.nf G u).

Theorem normal_reflexivity_typed c d n (G : Ctx nat n) C u v :
  @wf nat RankSorts n G -> @typ nat RankSorts n G C (𝓤 c) ->
  @typ nat RankSorts n G u C -> @typ nat RankSorts n G v C ->
  def_equiv nat n u v ->
  @typ nat RankSorts n G (normal_reflexivity d G C u) (IE.eq_type d C u v).
Proof.
  intros HG HC Hu Hv Heq.
  assert (HC' : typ G (OC.nf G C) (𝓤 c)) by (apply OC.nf_typed; assumption).
  assert (Hu' : typ G (OC.nf G u) (OC.nf G C)).
  { eapply typ_conv with (T := C) (ℓ := c).
    - apply OC.nf_typed; assumption.
    - exact HC'.
    - apply OC.nf_conversion. }
  unfold normal_reflexivity; eapply typ_conv with
    (T := IE.eq_type d (OC.nf G C) (OC.nf G u) (OC.nf G u))
    (ℓ := Nat.max (c+2) (d+1)).
  - apply IE.refl_case_typed with (a := c); assumption.
  - eapply IE.eq_type_sort; eassumption.
  - apply def_equiv_prop; eexists; split; [reflexivity |].
    assert (Hnf : OC.nf G u = OC.nf G v).
    { apply (proj2 (OC.nf_conversion_iff n G G u v C C HG HG Hu Hv)); exact Heq. }
    apply eq_type_reduces; try apply OC.nf_reduces.
    rewrite Hnf; apply OC.nf_reduces.
Qed.

Theorem normal_reflexivity_normal c d n (G : Ctx nat n) C u :
  @wf nat RankSorts n G -> @typ nat RankSorts n G C (𝓤 c) ->
  @typ nat RankSorts n G u C -> normalb (normal_reflexivity d G C u) = true.
Proof.
  intros HG HC Hu; apply IE.refl_case_normal; eapply OC.nf_normal; eassumption.
Qed.

(** Normalizing these annotations never normalizes the payload p. Every
    full application returns the LITERAL supplied p, typed or untyped. *)
Theorem normal_reflexivity_erases d n (G : Ctx nat n) C u P p :
  reduces_to nat n (IE.transport (normal_reflexivity d G C u) P p) p.
Proof. apply IE.transport_refl. Qed.

Definition extension d {n} (G : Ctx nat n) (C u v : Term nat n) :=
  G & IE.eq_type d C u v.
Definition extend_fill d {m n} (H : Ctx nat n) (sigma : Fin m -> Term nat n) C u :
    Fin (S m) -> Term nat n :=
  fin_match (normal_reflexivity d H (replace sigma C) (replace sigma u)) sigma.

Theorem extension_wf c d n (G : Ctx nat n) C u v :
  @wf nat RankSorts n G -> @typ nat RankSorts n G C (𝓤 c) ->
  @typ nat RankSorts n G u C -> @typ nat RankSorts n G v C ->
  @wf nat RankSorts (S n) (extension d G C u v).
Proof. intros HG HC Hu Hv; eapply wf_cons; [exact HG | eapply IE.eq_type_sort; eassumption]. Qed.

Theorem extension_normal d n (G : Ctx nat n) C u v :
  PT.normal_context G = true -> normalb C = true -> normalb u = true -> normalb v = true ->
  PT.normal_context (extension d G C u v) = true.
Proof.
  intros HG HC Hu Hv; unfold extension; cbn [PT.normal_context];
    rewrite HG, IE.eq_type_normal by assumption; reflexivity.
Qed.

Theorem extend_fill_typed c d m n (G : Ctx nat m) (H : Ctx nat n) sigma C u v :
  @wf nat RankSorts n H -> TypedSub G H sigma ->
  @typ nat RankSorts m G C (𝓤 c) -> @typ nat RankSorts m G u C -> @typ nat RankSorts m G v C ->
  def_equiv nat n (replace sigma u) (replace sigma v) ->
  TypedSub (extension d G C u v) H (extend_fill d H sigma C u).
Proof.
  intros HH HS HC Hu Hv Heq; apply UR.typed_sub_parameter; [exact HS |].
  rewrite IE.eq_type_replace; apply normal_reflexivity_typed with (c := c); try assumption.
  - change (typ H (replace sigma C) (replace sigma (𝓤 c))); eapply typing_replace; eassumption.
  - eapply typing_replace; eassumption.
  - eapply typing_replace; eassumption.
Qed.

Theorem extend_fill_erases d m n (H : Ctx nat n) sigma C u (P p : Term nat (S m)) :
  reduces_to nat n
    (replace (extend_fill d H sigma C u) (IE.transport (var fzero) P p))
    (replace (extend_fill d H sigma C u) p).
Proof.
  rewrite IE.transport_replace; cbn [replace extend_fill fin_match]; apply normal_reflexivity_erases.
Qed.

Theorem extend_fill_preserves_recovery d m n (H : Ctx nat n) sigma C u (P p : Term nat (S m)) t :
  reduces_to nat n (replace (extend_fill d H sigma C u) p) t ->
  reduces_to nat n (replace (extend_fill d H sigma C u) (IE.transport (var fzero) P p)) t.
Proof. intro Hred; eapply rtc_trans; [apply extend_fill_erases | exact Hred]. Qed.

Print Assumptions normal_reflexivity_typed.
Print Assumptions normal_reflexivity_normal.
Print Assumptions normal_reflexivity_erases.
Print Assumptions extension_wf.
Print Assumptions extension_normal.
Print Assumptions extend_fill_typed.
Print Assumptions extend_fill_erases.
Print Assumptions extend_fill_preserves_recovery.
End RealizedEquality.
