From Stdlib Require Import Lists.List.
From Equations Require Import Equations.
From PTSrk Require Import Syntax Reduction Congruence AbstractRewriting.
From PTSrk.Combinatory Require Import ProductCatalogue CatalogueHilbert.

(** The syntactic part of product exposure along a major-premise chain.
    Changing its distinguished product to a lambda commutes with every
    ORIGINAL beta step, including reduction in annotations and arguments.
    This is a forward simulation, NOT eta conversion or subject expansion.
    Selecting and typing an exposed head for an arbitrary Hilbert proof is
    a separate obligation; it is not assumed by these lemmas. *)
Module ProductExposure.

Inductive Exposure : forall {n}, Term nat n -> Term nat n -> Prop :=
| expose_pi {n} (A : Term nat n) B : Exposure (Π A B) (lam A B)
| expose_lam {n} (A : Term nat n) M N :
    Exposure M N -> Exposure (lam A M) (lam A N)
| expose_app {n} (M N x : Term nat n) :
    Exposure M N -> Exposure (app M x) (app N x).

Theorem exposure_replace {m n} (σ : Fin m -> Term nat n) M N :
  Exposure M N -> Exposure (replace σ M) (replace σ N).
Proof.
  intro H. revert n σ. induction H; intros; cbn; constructor; auto.
Qed.

Corollary exposure_subst {n} (M N : Term nat (S n)) x :
  Exposure M N -> Exposure (subst M x) (subst N x).
Proof. apply exposure_replace. Qed.

(** One source beta step has exactly one matching target beta step. *)
Theorem exposure_step {n} (M M' : Term nat n) :
  M →ᵝ M' -> forall N, Exposure M N ->
  exists N', N →ᵝ N' /\ Exposure M' N'.
Proof.
  intro H. induction H; intros N HE; dependent elimination HE.
  - eexists. split; [apply step_lam_left; exact H | constructor].
  - eexists. split; [apply step_lam_right; exact H | constructor].
  - eexists. split; [apply step_lam_left; exact H | constructor; assumption].
  - match goal with E : Exposure _ _ |- _ =>
      destruct (IHstep _ E) as [N' [HN' HE']] end.
    eexists. split; [apply step_lam_right; exact HN' | constructor; exact HE'].
  - match goal with E : Exposure _ _ |- _ =>
      destruct (IHstep _ E) as [N' [HN' HE']] end.
    eexists. split; [apply step_app_left; exact HN' | constructor; exact HE'].
  - eexists. split; [apply step_app_right; exact H | constructor; assumption].
  - match goal with E : Exposure _ _ |- _ => dependent elimination E end.
    eexists. split; [apply step_beta | apply exposure_subst; assumption].
Qed.

Theorem exposure_reduction {n} (M M' : Term nat n) :
  M ↠ᵝ M' -> forall N, Exposure M N ->
  exists N', N ↠ᵝ N' /\ Exposure M' N'.
Proof.
  intro H. induction H; intros N HE.
  - exists N. split; [reflexivity | exact HE].
  - destruct (exposure_step _ _ H _ HE) as [N1 [Hstep HE1]].
    destruct (IHRTC _ HE1) as [N' [Hpath HE']].
    exists N'. split; [eapply rtc_step; eassumption | exact HE'].
Qed.

Theorem exposure_product {n} (A : Term nat n) B N :
  Exposure (Π A B) N -> N = lam A B.
Proof. intro H. dependent elimination H. reflexivity. Qed.

Theorem exposure_product_reduct {n} (M N A : Term nat n) B :
  Exposure M N -> M ↠ᵝ Π A B -> N ↠ᵝ lam A B.
Proof.
  intros HE HM. destruct (exposure_reduction _ _ HM _ HE) as [N' [HN HE']].
  rewrite (exposure_product _ _ _ HE') in HN. exact HN.
Qed.

Fixpoint apps {n} (M : Term nat n) (xs : list (Term nat n)) : Term nat n :=
  match xs with nil => M | cons x rest => apps (app M x) rest end.

Theorem exposure_apps {n} (xs : list (Term nat n)) M N :
  Exposure M N -> Exposure (apps M xs) (apps N xs).
Proof.
  revert M N. induction xs; intros M N HE; cbn; [exact HE |].
  apply IHxs, expose_app, HE.
Qed.

Theorem expose_product_sound {n} (M N : Term nat n) :
  ProductCatalogue.expose_product M = Some N -> Exposure M N.
Proof.
  revert N. induction M; intros N HE; cbn in HE; try discriminate.
  - inversion HE; subst. constructor.
  - destruct (ProductCatalogue.expose_product M2) eqn:HB; cbn in HE;
      try discriminate.
    inversion HE; subst. constructor. apply IHM2. reflexivity.
Qed.

Theorem catalogue_exposure l l' :
  CatalogueHilbert.exposure l = Some l' ->
  Exposure (CatalogueHilbert.subject l) (CatalogueHilbert.subject l').
Proof.
  intro H. apply expose_product_sound.
  rewrite CatalogueHilbert.exposure_exact, H. reflexivity.
Qed.

(** Exact annotations at the end of any beta-reducing application spine. *)
Theorem catalogue_spine_product l l' xs A B :
  CatalogueHilbert.exposure l = Some l' ->
  apps (CatalogueHilbert.subject l) xs ↠ᵝ Π A B ->
  apps (CatalogueHilbert.subject l') xs ↠ᵝ lam A B.
Proof.
  intros Hl HM. eapply exposure_product_reduct; [| exact HM].
  apply exposure_apps, catalogue_exposure, Hl.
Qed.

(** The catalogue map preserves not only the subject's prefix but its
    corresponding TYPE prefix.  This is the literal axiom-level premise
    used in Bunder--Dekkers 7.5(ii); arbitrary derivation replay is separate. *)
Inductive SchemaExposure : forall {n},
  Term nat n -> Term nat n -> Term nat n -> Term nat n -> Prop :=
| schema_product {n} (A : Term nat n) B a b :
    SchemaExposure (Π A B) (𝓤 a) (lam A B) (Π A (𝓤 b))
| schema_lambda {n} (A : Term nat n) M T N U :
    SchemaExposure M T N U ->
    SchemaExposure (lam A M) (Π A T) (lam A N) (Π A U).

Theorem schema_term_exposure {n} (M T N U : Term nat n) :
  SchemaExposure M T N U -> Exposure M N.
Proof. intro H. induction H; constructor; assumption || idtac. Qed.

Theorem schema_replace {m n} (σ : Fin m -> Term nat n) M T N U :
  SchemaExposure M T N U ->
  SchemaExposure (replace σ M) (replace σ T) (replace σ N) (replace σ U).
Proof. intro H. revert n σ. induction H; intros; cbn; constructor; auto. Qed.

Theorem catalogue_schema_exposure l l' :
  CatalogueHilbert.exposure l = Some l' ->
  SchemaExposure (CatalogueHilbert.subject l) (CatalogueHilbert.declared_type l)
    (CatalogueHilbert.subject l') (CatalogueHilbert.declared_type l').
Proof.
  destruct l as [s|s|s|s];
    [destruct s | destruct s | destruct s | destruct s as [p a b c d]; destruct p];
    intro H; cbn in H; try discriminate; inversion H; subst;
    repeat constructor.
Qed.

Print Assumptions exposure_replace.
Print Assumptions exposure_subst.
Print Assumptions exposure_step.
Print Assumptions exposure_reduction.
Print Assumptions exposure_product_reduct.
Print Assumptions exposure_apps.
Print Assumptions expose_product_sound.
Print Assumptions catalogue_spine_product.
Print Assumptions schema_term_exposure.
Print Assumptions schema_replace.
Print Assumptions catalogue_schema_exposure.

End ProductExposure.
