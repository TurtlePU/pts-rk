From Equations Require Import Equations.
From PTSrk Require Import Syntax Context Reduction Congruence AbstractRewriting.
From PTSrk.Combinatory Require Import Core ProductCatalogue IdentityCatalogue
  ConstantCatalogue SubstitutionCatalogue CatalogueHilbert ContextualHilbert.

(** Constructive assembly steps for Hilbert abstraction.  All premises are
    internal H+ derivations; these are not new inference constructors.  The
    family-abstraction premises in the product/application cases remain
    explicit, pending the general deduction theorem. *)
Module HilbertAbstraction.
Import ContextualHilbert.

Local Abbreviation v0 := (var fzero).
Local Abbreviation v1 := (var (fsucc fzero)).

Lemma replace_renaming {m n} (ρ : Fin m -> Fin n) (t : Term nat m) :
  replace (fun i => var (ρ i)) t = rename ρ t.
Proof.
  rewrite <- (replace_rename (fun i => var i) ρ t), replace_var.
  reflexivity.
Qed.

Local Ltac normalize_data d :=
  cbn in d; unfold subst, shift in d; cbn in d;
  autorewrite with syntax in d; cbn in d;
  repeat rewrite replace_renaming in d.

Local Ltac head_beta :=
  first [apply step_beta | apply step_app_left; head_beta].
Local Ltac compute_head :=
  eapply rtc_step; [head_beta | cbn; unfold shift, subst; cbn;
    autorewrite with syntax].

Definition product_atom {n} {Γ : Ctx nat n}
  (D : ContextDerivation Γ) a b :
  Derivation Γ (Core.product a b) (Core.product_type a b).
Proof. exact (context_scheme D (CatalogueHilbert.Product (ProductCatalogue.P1 a b))). Defined.

Definition identity_atom {n} {Γ : Ctx nat n}
  (D : ContextDerivation Γ) a :
  Derivation Γ (Core.identity a) (Core.identity_type a).
Proof. exact (context_scheme D (CatalogueHilbert.Identity (IdentityCatalogue.I1 a))). Defined.

Definition constant_atom {n} {Γ : Ctx nat n}
  (D : ContextDerivation Γ) a b :
  Derivation Γ (Core.constant_simple a b) (Core.constant_simple_type a b).
Proof. exact (context_scheme D (CatalogueHilbert.Constant (ConstantCatalogue.K1 a b))). Defined.

Definition substitution_atom {n} {Γ : Ctx nat n}
  (D : ContextDerivation Γ) a b c :
  Derivation Γ (Core.substitution a b c) (Core.substitution_type a b c).
Proof.
  exact (context_scheme D (CatalogueHilbert.Substitution
    (SubstitutionCatalogue.make SubstitutionCatalogue.S1 a b c 0))).
Defined.

Definition product_apply {n} {Γ : Ctx nat n} {A F a b}
  (dA : Derivation Γ A (𝓤 a)) (dF : Derivation Γ F (Π A (𝓤 b))) :
  Derivation Γ (Core.product a b $ A $ F) (𝓤 (Nat.max (S a) b)).
Proof.
  pose (d := h_apply (product_atom (derivation_context dA) a b) dA).
  normalize_data d. pose (e := h_apply d dF). normalize_data e. exact e.
Defined.

Definition product_family {n} {Γ : Ctx nat n} {A F a b}
  (dA : Derivation Γ A (𝓤 a)) (dF : Derivation Γ F (Π A (𝓤 b))) :
  Derivation Γ (Π A (shift F $ v0)) (𝓤 (Nat.max (S a) b)) :=
  h_subject_reduction (product_apply dA dF) (Core.product_beta a b A F).

(** Applying a weakened lambda to the newest variable restores its exact
    body, including every original annotation.  This is beta, not eta. *)
Lemma shifted_lambda_beta {n} (A : Term nat n) B :
  shift (lam A B) $ v0 ↠ᵝ B.
Proof.
  unfold shift. cbn. eapply rtc_step; [apply step_beta |].
  unfold subst. rewrite replace_rename.
  transitivity (replace (fun i => var i) B); [|rewrite replace_var; reflexivity].
  replace (replace _ B) with (replace (fun i => var i) B).
  - reflexivity.
  - apply replace_ext. intros i. dependent elimination i; reflexivity.
Qed.

Definition product_formation {n} {Γ : Ctx nat n} {A B a b}
  (dA : Derivation Γ A (𝓤 a))
  (dB : Derivation Γ (lam A B) (Π A (𝓤 b))) :
  Derivation Γ (Π A B) (𝓤 (Nat.max (S a) b)).
Proof.
  eapply h_subject_reduction; [exact (product_family dA dB) |].
  apply Π_cong_r, shifted_lambda_beta.
Defined.

Lemma identity_abstract_beta {n} a (A : Term nat n) :
  Core.identity a $ A ↠ᵝ lam A v0.
Proof. unfold Core.identity. compute_head. reflexivity. Qed.

Definition identity_abstract {n} {Γ : Ctx nat n} {A a}
  (dA : Derivation Γ A (𝓤 a)) :
  Derivation Γ (lam A v0) (Π A (shift A)).
Proof.
  pose (d := h_apply (identity_atom (derivation_context dA) a) dA).
  normalize_data d.
  eapply h_subject_reduction; [exact d | apply identity_abstract_beta].
Defined.

Lemma constant_abstract_beta {n} a b (A B M : Term nat n) :
  Core.constant_simple b a $ B $ A $ M ↠ᵝ lam A (shift M).
Proof. unfold Core.constant_simple. do 3 compute_head. reflexivity. Qed.

Definition constant_abstract {n} {Γ : Ctx nat n} {A B M a b}
  (dA : Derivation Γ A (𝓤 a)) (dB : Derivation Γ B (𝓤 b))
  (dM : Derivation Γ M B) :
  Derivation Γ (lam A (shift M)) (Π A (shift B)).
Proof.
  pose (d := h_apply (constant_atom (derivation_context dA) b a) dB).
  normalize_data d. pose (e := h_apply d dA). normalize_data e.
  pose (f := h_apply e dM). normalize_data f.
  eapply h_subject_reduction; [exact f | apply constant_abstract_beta].
Defined.

Definition binary_family_type {n} (A B : Term nat n) c : Term nat n :=
  Π A (Π (shift B $ v0) (𝓤 c)).

Definition application_function_type {n} (A B C : Term nat n) : Term nat n :=
  Π A (Π (shift B $ v0) (shift (shift C) $ v1 $ v0)).

Definition application_argument_type {n} (A B : Term nat n) : Term nat n :=
  Π A (shift B $ v0).

Definition application_result_type {n} (A C g : Term nat n) : Term nat n :=
  Π A (shift C $ v0 $ (shift g $ v0)).

(** The dependent S assembly, with the required type-family abstractions
    exposed as H+ premises rather than silently obtained from native typing. *)
Definition substitution_apply {n} {Γ : Ctx nat n} {A B C f g a b c}
  (dA : Derivation Γ A (𝓤 a)) (dB : Derivation Γ B (Π A (𝓤 b)))
  (dC : Derivation Γ C (binary_family_type A B c))
  (df : Derivation Γ f (application_function_type A B C))
  (dg : Derivation Γ g (application_argument_type A B)) :
  Derivation Γ (Core.substitution a b c $ A $ B $ C $ f $ g)
    (application_result_type A C g).
Proof.
  unfold application_function_type in df. normalize_data df.
  pose (d := h_apply (substitution_atom (derivation_context dA) a b c) dA).
  normalize_data d. pose (e := h_apply d dB). normalize_data e.
  pose (h := h_apply e dC). normalize_data h.
  pose (i := h_apply h df). normalize_data i.
  pose (j := h_apply i dg). normalize_data j. exact j.
Defined.

Lemma substitution_abstract_beta {n} a b c (A B C f g : Term nat n) :
  Core.substitution a b c $ A $ B $ C $ f $ g ↠ᵝ
    lam A (shift f $ v0 $ (shift g $ v0)).
Proof.
  unfold Core.substitution. do 5 compute_head.
  cbn. rewrite replace_renaming. reflexivity.
Qed.

Definition application_assembly {n} {Γ : Ctx nat n} {A B C f g a b c}
  (dA : Derivation Γ A (𝓤 a)) (dB : Derivation Γ B (Π A (𝓤 b)))
  (dC : Derivation Γ C (binary_family_type A B c))
  (df : Derivation Γ f (application_function_type A B C))
  (dg : Derivation Γ g (application_argument_type A B)) :
  Derivation Γ (lam A (shift f $ v0 $ (shift g $ v0)))
    (application_result_type A C g) :=
  h_subject_reduction (substitution_apply dA dB dC df dg)
    (substitution_abstract_beta a b c A B C f g).

(** This variant accepts family and function types that are reducts of
    the S domains.  Common-reduct application needs no type-expansion rule. *)
Definition substitution_apply_reduced {n} {Γ : Ctx nat n}
  {A B C f g a b c TC Tf Tg}
  (dA : Derivation Γ A (𝓤 a)) (dB : Derivation Γ B (Π A (𝓤 b)))
  (dC : Derivation Γ C TC) (df : Derivation Γ f Tf) (dg : Derivation Γ g Tg)
  (HC : binary_family_type A B c ↠ᵝ TC)
  (Hf : application_function_type A B C ↠ᵝ Tf)
  (Hg : application_argument_type A B ↠ᵝ Tg) :
  Derivation Γ (Core.substitution a b c $ A $ B $ C $ f $ g)
    (application_result_type A C g).
Proof.
  unfold application_function_type in Hf. normalize_data Hf.
  pose (d := h_apply (substitution_atom (derivation_context dA) a b c) dA).
  normalize_data d. pose (e := h_apply d dB). normalize_data e.
  pose (h := h_apply_common_reduct e dC HC (rtc_refl _ TC)).
  normalize_data h.
  pose (i := h_apply_common_reduct h df Hf (rtc_refl _ Tf)).
  normalize_data i.
  pose (j := h_apply_common_reduct i dg Hg (rtc_refl _ Tg)).
  normalize_data j. exact j.
Defined.

Lemma double_shifted_lambda_beta {n} (A : Term nat n) B C :
  shift (shift (lam A (lam B C))) $ v1 $ v0 ↠ᵝ C.
Proof.
  transitivity (shift (lam B C) $ v0).
  - apply app_cong_l.
    change (rename fsucc (shift (lam A (lam B C)) $ v0) ↠ᵝ
      rename fsucc (lam B C)).
    apply rename_rtc, shifted_lambda_beta.
  - apply shifted_lambda_beta.
Qed.

Definition application_abstract {n} {Γ : Ctx nat n} {A B C F G a b c}
  (dA : Derivation Γ A (𝓤 a))
  (dB : Derivation Γ (lam A B) (Π A (𝓤 b)))
  (dC : Derivation Γ (lam A (lam B C)) (Π A (Π B (𝓤 c))))
  (dF : Derivation Γ (lam A F) (Π A (Π B C)))
  (dG : Derivation Γ (lam A G) (Π A B)) :
  Derivation Γ (lam A (F $ G)) (Π A (subst C G)).
Proof.
  assert (HC : binary_family_type A (lam A B) c ↠ᵝ Π A (Π B (𝓤 c))).
  { apply Π_cong_r, Π_cong_l, shifted_lambda_beta. }
  assert (HF : application_function_type A (lam A B) (lam A (lam B C))
    ↠ᵝ Π A (Π B C)).
  { apply Π_cong_r. transitivity (Π B
      (shift (shift (lam A (lam B C))) $ v1 $ v0)).
    - apply Π_cong_l, shifted_lambda_beta.
    - apply Π_cong_r, double_shifted_lambda_beta. }
  assert (HG : application_argument_type A (lam A B) ↠ᵝ Π A B).
  { apply Π_cong_r, shifted_lambda_beta. }
  pose (d := substitution_apply_reduced dA dB dC dF dG HC HF HG).
  pose (e := h_subject_reduction d
    (substitution_abstract_beta a b c A (lam A B) (lam A (lam B C))
      (lam A F) (lam A G))).
  eapply h_type_reduction.
  - eapply h_subject_reduction; [exact e |].
    apply λ_cong_r. transitivity (F $ (shift (lam A G) $ v0)).
    + apply app_cong_l, shifted_lambda_beta.
    + apply app_cong_r, shifted_lambda_beta.
  - unfold application_result_type. apply Π_cong_r.
    transitivity (lam B C $ G).
    + transitivity (lam B C $ (shift (lam A G) $ v0)).
      * apply app_cong_l, shifted_lambda_beta.
      * apply app_cong_r, shifted_lambda_beta.
    + eapply rtc_step; [apply step_beta | reflexivity].
Defined.

Print Assumptions product_atom.
Print Assumptions identity_atom.
Print Assumptions constant_atom.
Print Assumptions substitution_atom.
Print Assumptions product_apply.
Print Assumptions product_family.
Print Assumptions shifted_lambda_beta.
Print Assumptions product_formation.
Print Assumptions identity_abstract_beta.
Print Assumptions identity_abstract.
Print Assumptions constant_abstract_beta.
Print Assumptions constant_abstract.
Print Assumptions substitution_apply.
Print Assumptions substitution_abstract_beta.
Print Assumptions application_assembly.
Print Assumptions substitution_apply_reduced.
Print Assumptions double_shifted_lambda_beta.
Print Assumptions application_abstract.

End HilbertAbstraction.
