From Stdlib Require Import Arith.PeanoNat.
From PTSrk Require Import Syntax Context Typing Preservation Ranks DefEq
  Reduction AbstractRewriting.
From PTSrk.NormalizationComplexity Require Import Greedy Morphisms.
From PTSrk.SelfInterpreter Require Import OpenCanonical RankedNormalization.
Import Context.

Module CanonicalSubstitution.
Module OC := OpenCanonical.OpenCanonical.
Module RN := RankedNormalization.RankedNormalization.

(** Executable METALEVEL hereditary substitution for the full original PTS.
    The outer normalization is essential: substitution of normal terms can
    create beta redexes. These are syntax functions, not internal evaluators. *)
Definition normal_sub {m n} (D : Ctx nat n) (sigma : Fin m -> Term nat n) :=
  fun i => OC.nf D (sigma i).

Definition hsubst {m n} (D : Ctx nat n) (sigma : Fin m -> Term nat n)
    (t : Term nat m) := OC.nf D (replace sigma t).

Lemma normal_sub_reduces m n (D : Ctx nat n) (sigma : Fin m -> Term nat n) i :
  reduces_to nat n (sigma i) (normal_sub D sigma i).
Proof. apply OC.nf_reduces. Qed.

Lemma replaced_normal_sub_reduces m n (D : Ctx nat n)
    (sigma : Fin m -> Term nat n) (t : Term nat m) :
  reduces_to nat n (replace sigma t) (replace (normal_sub D sigma) t).
Proof. apply rtc_replace; intro i; apply normal_sub_reduces. Qed.

(** Normalizing entries preserves an ACTUAL original typed substitution.
    Its dependent lookup types must be converted too; keeping old lookup
    types silently would not establish TypedSub. *)
Theorem normal_sub_typed m n (G : Ctx nat m) (D : Ctx nat n) sigma :
  @wf nat RankSorts n D -> TypedSub G D sigma ->
  TypedSub G D (normal_sub D sigma).
Proof.
  intros HD Hsigma i.
  pose proof (Hsigma i) as Hi.
  destruct (type_is_correct _ _ Hi HD) as [r Hr].
  eapply typ_conv with (T := replace sigma (G !! i)) (ℓ := r).
  - apply OC.nf_typed with (T := replace sigma (G !! i)); assumption.
  - eapply subject_reduction'; [exact Hr | exact HD |].
    apply replaced_normal_sub_reduces.
  - apply RN.reduction_conversion, replaced_normal_sub_reduces.
Qed.

Lemma typed_sub_identity n (G : Ctx nat n) : TypedSub G G (fun i => var i).
Proof. intro i; rewrite replace_var; constructor. Qed.

Lemma typed_sub_compose l m n (G : Ctx nat l) (D : Ctx nat m) (E : Ctx nat n)
    sigma tau :
  TypedSub G D sigma -> TypedSub D E tau ->
  TypedSub G E (fun i => replace tau (sigma i)).
Proof.
  intros Hsigma Htau i.
  pose proof (typing_replace _ _ _ (Hsigma i) _ _ tau Htau) as H.
  rewrite replace_replace in H; exact H.
Qed.

Theorem hsubst_normal m n (G : Ctx nat m) (D : Ctx nat n) sigma t T :
  @wf nat RankSorts n D -> TypedSub G D sigma ->
  @typ nat RankSorts m G t T -> normalb (hsubst D sigma t) = true.
Proof.
  intros HD Hsigma Ht. unfold hsubst.
  apply OC.nf_normal with (T := replace sigma T); [exact HD |].
  eapply typing_replace; eassumption.
Qed.

Theorem hsubst_typed m n (G : Ctx nat m) (D : Ctx nat n) sigma t T :
  @wf nat RankSorts n D -> TypedSub G D sigma ->
  @typ nat RankSorts m G t T ->
  @typ nat RankSorts n D (hsubst D sigma t) (replace sigma T).
Proof.
  intros HD Hsigma Ht. unfold hsubst.
  apply OC.nf_typed; [exact HD |]. eapply typing_replace; eassumption.
Qed.

Theorem hsubst_source_nf m n (G : Ctx nat m) (D : Ctx nat n) sigma t T :
  @wf nat RankSorts m G -> @wf nat RankSorts n D ->
  TypedSub G D sigma -> @typ nat RankSorts m G t T ->
  hsubst D sigma t = hsubst D sigma (OC.nf G t).
Proof.
  intros HG HD Hsigma Ht. unfold hsubst.
  apply (proj2 (OC.nf_conversion_iff n D D _ _
    (replace sigma T) (replace sigma T) HD HD
    (typing_replace _ _ _ Ht _ _ sigma Hsigma)
    (typing_replace _ _ _ (OC.nf_typed m G t T HG Ht) _ _ sigma Hsigma))).
  apply RN.reduction_conversion, replace_rtc, OC.nf_reduces.
Qed.

(** Both term AND dependent type can be put in canonical form. Original
    validity supplies the type's exact sort; no cumulative rule is used. *)
Theorem hsubst_canonical_typed m n (G : Ctx nat m) (D : Ctx nat n) sigma t T :
  @wf nat RankSorts n D -> TypedSub G D sigma ->
  @typ nat RankSorts m G t T ->
  @typ nat RankSorts n D (hsubst D sigma t) (hsubst D sigma T).
Proof.
  intros HD Hsigma Ht.
  pose proof (typing_replace _ _ _ Ht _ _ sigma Hsigma) as Hst.
  destruct (type_is_correct _ _ Hst HD) as [r Hr].
  eapply typ_conv with (T := replace sigma T) (ℓ := r).
  - eapply hsubst_typed; eassumption.
  - apply OC.nf_typed; assumption.
  - apply OC.nf_conversion.
Qed.

Theorem hsubst_normal_sub m n (G : Ctx nat m) (D : Ctx nat n) sigma t T :
  @wf nat RankSorts n D -> TypedSub G D sigma ->
  @typ nat RankSorts m G t T ->
  hsubst D sigma t = hsubst D (normal_sub D sigma) t.
Proof.
  intros HD Hsigma Ht. unfold hsubst.
  apply (proj2 (OC.nf_conversion_iff n D D _ _
    (replace sigma T) (replace (normal_sub D sigma) T) HD HD
    (typing_replace _ _ _ Ht _ _ sigma Hsigma)
    (typing_replace _ _ _ Ht _ _ _ (normal_sub_typed m n G D sigma HD Hsigma)))).
  apply RN.reduction_conversion, replaced_normal_sub_reduces.
Qed.

Theorem hereditary_substitution m n (G : Ctx nat m) (D : Ctx nat n) sigma t T :
  @wf nat RankSorts m G -> @wf nat RankSorts n D ->
  TypedSub G D sigma -> @typ nat RankSorts m G t T ->
  hsubst D sigma t = hsubst D (normal_sub D sigma) (OC.nf G t).
Proof.
  intros HG HD Hsigma Ht.
  rewrite (hsubst_source_nf m n G D sigma t T HG HD Hsigma Ht).
  apply hsubst_normal_sub with (G := G) (T := T); try assumption.
  apply OC.nf_typed; assumption.
Qed.

Theorem hsubst_identity n (G : Ctx nat n) t :
  hsubst G (fun i => var i) t = OC.nf G t.
Proof. unfold hsubst; rewrite replace_var; reflexivity. Qed.

(** Composition normalizes every composite entry. This equation includes
    full dependent original types, not just the simply typed fragment. *)
Theorem hsubst_composition l m n
    (G : Ctx nat l) (D : Ctx nat m) (E : Ctx nat n) sigma tau t T :
  @wf nat RankSorts m D -> @wf nat RankSorts n E ->
  TypedSub G D sigma -> TypedSub D E tau -> @typ nat RankSorts l G t T ->
  hsubst E tau (hsubst D sigma t) =
  hsubst E (fun i => hsubst E tau (sigma i)) t.
Proof.
  intros HD HE Hsigma Htau Ht.
  pose proof (typing_replace _ _ _ Ht _ _ sigma Hsigma) as Hst.
  change (hsubst E tau (OC.nf D (replace sigma t)) =
    hsubst E (fun i => hsubst E tau (sigma i)) t).
  rewrite <- (hsubst_source_nf m n D E tau _ _ HD HE Htau Hst).
  unfold hsubst at 1. rewrite replace_replace.
  change (hsubst E (fun i => replace tau (sigma i)) t =
    hsubst E (normal_sub E (fun i => replace tau (sigma i))) t).
  apply hsubst_normal_sub with (G := G) (T := T); try assumption.
  apply typed_sub_compose with (D := D); assumption.
Qed.

Theorem hsubst_conversion m n (G : Ctx nat m) (D : Ctx nat n)
    sigma t u T U :
  @wf nat RankSorts n D -> TypedSub G D sigma ->
  @typ nat RankSorts m G t T -> @typ nat RankSorts m G u U ->
  def_equiv nat m t u -> hsubst D sigma t = hsubst D sigma u.
Proof.
  intros HD Hsigma Ht Hu Htu. unfold hsubst.
  apply (proj2 (OC.nf_conversion_iff n D D _ _
    (replace sigma T) (replace sigma U) HD HD
    (typing_replace _ _ _ Ht _ _ sigma Hsigma)
    (typing_replace _ _ _ Hu _ _ sigma Hsigma))).
  apply replace_equiv; exact Htu.
Qed.

Print Assumptions normal_sub_typed.
Print Assumptions hsubst_normal.
Print Assumptions hsubst_typed.
Print Assumptions hsubst_canonical_typed.
Print Assumptions hereditary_substitution.
Print Assumptions hsubst_identity.
Print Assumptions hsubst_composition.
Print Assumptions hsubst_conversion.
End CanonicalSubstitution.
