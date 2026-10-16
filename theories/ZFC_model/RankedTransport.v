(** Structural transport for the joint semantic certificates. These lemmas
    retain the original annotated syntax and both semantic indices. They
    supply the binder-lifting and type-alignment operations for hereditary
    substitution; they do not assume or establish certificate totality. *)
From Equations Require Import Equations.
From ZFC Require Import Sets Axioms.
From PTSrk Require Import Syntax Context Typing Ranks DefEq Inversions AbstractRewriting.
From PTSrkModel Require Import CodeUniverses CardinalHierarchy Denotation
  SyntaxRenaming ContextTransport CanonicalTypeWitnesses CanonicalDenotation
  CanonicalRenaming CanonicalContext RankedDenotation.
Import CodeUniverses.CodeUniverses.

Module RankedTransport.
Module RD := RankedDenotation.RankedDenotation.
Module CD := CanonicalDenotation.CanonicalDenotation.
Module CC := CanonicalContext.CanonicalContext.
Section Transport.
Variables H s : Ens.

Theorem certificate_rename n G rho t T v a : RD.certificate H s n G rho t T v a ->
  forall m (D : Ctx nat m) (r : Fin n -> Fin m) rho',
    context_renaming G D r -> valuation_renaming rho rho' r ->
    RD.certificate H s m D rho' (rename r t) (rename r T) v a.
Proof.
  intro HD; induction HD; intros q D r rho' EC EV; cbn [rename].
  - apply RD.certificate_sort.
  - eapply RD.certificate_equal; [eapply RD.certificate_variable | | apply EQ_refl].
    + apply IHHD; eassumption.
    + rewrite <- EC. apply rename_equiv; assumption.
    + eapply IN_sound_left; [apply EV | eassumption].
    + apply EQ_sym, EV.
  - eapply RD.certificate_product.
    + change (@typ nat RankSorts (S q) (D & rename r A)
        (rename (weak r) B) (rename (weak r) (𝓤 k))).
      eapply rank_typing_rename; [eassumption | apply context_renaming_extend; exact EC].
    + apply beta_normal_rename; assumption.
    + eauto.
    + eauto using context_renaming_extend, valuation_renaming_extend.
    + assumption.
  - eapply RD.certificate_lambda with (m := m) (k := k).
    + change (@typ nat RankSorts (S q) (D & rename r A)
        (rename (weak r) B) (rename (weak r) (𝓤 k))).
      eapply rank_typing_rename; [eassumption | apply context_renaming_extend; exact EC].
    + eapply rank_typing_rename; [eassumption | apply context_renaming_extend; exact EC].
    + apply beta_normal_rename; assumption.
    + apply beta_normal_rename; assumption.
    + eauto.
    + eauto using context_renaming_extend, valuation_renaming_extend.
    + eauto using context_renaming_extend, valuation_renaming_extend.
    + assumption.
    + assumption.
  - eapply RD.certificate_application with (A := rename r A) (B := rename (weak r) B)
      (m := m) (k := k).
    + change (@typ nat RankSorts (S q) (D & rename r A)
        (rename (weak r) B) (rename (weak r) (𝓤 k))).
      eapply rank_typing_rename; [eassumption | apply context_renaming_extend; exact EC].
    + apply beta_normal_rename; assumption.
    + eauto.
    + eauto using context_renaming_extend, valuation_renaming_extend.
    + eauto.
    + eauto.
    + eauto.
    + rewrite <- rename_subst. apply rename_equiv; assumption.
    + apply not_lambda_rename; assumption.
    + assumption.
  - eapply RD.certificate_equal; eauto.
Qed.

Corollary certificate_shift n G rho t T v a A x :
  RD.certificate H s n G rho t T v a ->
  RD.certificate H s (S n) (G & A) (fin_match x rho) (shift t) (shift T) v a.
Proof.
  intro HD; unfold shift; eapply certificate_rename; [exact HD | |].
  - intro i; reflexivity.
  - intro i; apply EQ_refl.
Qed.

Theorem certificate_context_transport n G rho t T v a :
  RD.certificate H s n G rho t T v a ->
  forall D : Ctx nat n, context_typing_morphism G D ->
    RD.certificate H s n D rho t T v a.
Proof.
  intro HD; induction HD; intros D HM.
  - apply RD.certificate_sort.
  - eapply RD.certificate_variable; [apply IHHD; exact HM | | assumption].
    transitivity (G !! i); [symmetry; eapply var_inversion; apply HM | assumption].
  - eapply RD.certificate_product.
    + eapply typing_context_transport; [apply CC.context_typing_morphism_extend; exact HM | eassumption].
    + assumption.
    + eauto.
    + eauto using CC.context_typing_morphism_extend.
    + assumption.
  - eapply RD.certificate_lambda.
    + eapply typing_context_transport; [apply CC.context_typing_morphism_extend; exact HM | eassumption].
    + eapply typing_context_transport; [apply CC.context_typing_morphism_extend; exact HM | eassumption].
    + assumption.
    + assumption.
    + eauto.
    + eauto using CC.context_typing_morphism_extend.
    + eauto using CC.context_typing_morphism_extend.
    + assumption.
    + assumption.
  - eapply RD.certificate_application.
    + eapply typing_context_transport; [apply CC.context_typing_morphism_extend; exact HM | eassumption].
    + assumption.
    + eauto.
    + eauto using CC.context_typing_morphism_extend.
    + eauto.
    + eauto.
    + eauto.
    + assumption.
    + assumption.
    + assumption.
  - eapply RD.certificate_equal; eauto.
Qed.

(** An existing term certificate and an actual canonical type value suffice
    to align both the normal assigned type and its code. No conversion
    property of semantic evaluation is assumed. *)
Theorem certificate_type_alignment n G rho t T C v a b :
  RD.certificate H s n G rho t T v a ->
  @typ nat RankSorts n G t C -> beta_normal C -> CD.denotes H s n G rho C b ->
  RD.certificate H s n G rho t C v b.
Proof.
  intros HD TC NC DC.
  assert (E : T = C).
  { eapply normal_types_unique; [eapply RD.original_typing; exact HD | exact TC |
      exact (proj2 (RD.normality H s n G rho t T v a HD)) |exact NC]. }
  subst C. eapply RD.certificate_equal; [exact HD |apply EQ_refl |].
  eapply CD.coherent; [|exact DC].
  exact (proj2 (RD.canonical_denotations H s n G rho t T v a HD)).
Qed.
End Transport.
End RankedTransport.

Print Assumptions RankedTransport.certificate_rename.
Print Assumptions RankedTransport.certificate_shift.
Print Assumptions RankedTransport.certificate_context_transport.
Print Assumptions RankedTransport.certificate_type_alignment.
