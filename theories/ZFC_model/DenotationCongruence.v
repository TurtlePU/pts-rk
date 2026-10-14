(** The six compatible cases of original reduction, given preservation for
    the reduced immediate subterm. Root beta is deliberately not assumed here. *)
From ZFC Require Import Sets Axioms.
From PTSrk Require Import Syntax Context Typing Ranks Reduction Preservation.
From PTSrkModel Require Import CardinalHierarchy Denotation DenotationInversion ContextTransport.

Section Congruence.
Variables H s : Ens.

Theorem denotes_product_domain_step n (G : Ctx nat n) rho A A' B l :
  @wf nat RankSorts n G -> @typ nat RankSorts n G A (𝓤 l) -> A →ᵝ A' ->
  (forall v, denotes H s n G rho A v -> denotes H s n G rho A' v) ->
  forall v, denotes H s n G rho (Π A B) v -> denotes H s n G rho (Π A' B) v.
Proof.
  intros HG HA R IH v D.
  destruct (denotes_product_inversion H s n G rho A B v D) as [a [b [DA [DB [EB E]]]]].
  eapply denotes_equal; [eapply denotes_product with (a := a) (b := b) | apply EQ_sym; exact E].
  - apply IH; exact DA.
  - intros x Hx. eapply denotes_context_reduction.
    + eapply wf_cons; eauto.
    + apply beta_here; exact R.
    + apply DB; exact Hx.
  - exact EB.
Qed.

Theorem denotes_product_codomain n (G : Ctx nat n) rho A B B' :
  (forall a x, denotes H s n G rho A a -> IN x (decode a) -> forall v,
    denotes H s (S n) (G & A) (fin_match x rho) B v ->
    denotes H s (S n) (G & A) (fin_match x rho) B' v) ->
  forall v, denotes H s n G rho (Π A B) v -> denotes H s n G rho (Π A B') v.
Proof.
  intros IH v D.
  destruct (denotes_product_inversion H s n G rho A B v D) as [a [b [DA [DB [EB E]]]]].
  eapply denotes_equal; [eapply denotes_product with (a := a) (b := b) | apply EQ_sym; exact E].
  - exact DA.
  - intros x Hx; eapply IH; [exact DA | exact Hx | apply DB; exact Hx].
  - exact EB.
Qed.

Theorem denotes_lambda_domain_step n (G : Ctx nat n) rho A A' t l :
  @wf nat RankSorts n G -> @typ nat RankSorts n G A (𝓤 l) -> A →ᵝ A' ->
  (forall v, denotes H s n G rho A v -> denotes H s n G rho A' v) ->
  forall v, denotes H s n G rho (lam A t) v -> denotes H s n G rho (lam A' t) v.
Proof.
  intros HG HA R IH v D.
  destruct (denotes_lambda_inversion H s n G rho A t v D)
    as [B [a [b [body [Tt [DA [DB [Dt [EB [Et E]]]]]]]]]].
  assert (HW : @wf nat RankSorts (S n) (G & A)) by (eapply wf_cons; eauto).
  eapply denotes_equal; [eapply denotes_lambda with (B := B) (a := a) (b := b) (body := body) | apply EQ_sym; exact E].
  - eapply context_reduction_strong; [exact Tt | exact HW | apply beta_here; exact R].
  - apply IH; exact DA.
  - intros x Hx. eapply denotes_context_reduction; [exact HW | apply beta_here; exact R | apply DB; exact Hx].
  - intros x Hx. eapply denotes_context_reduction; [exact HW | apply beta_here; exact R | apply Dt; exact Hx].
  - exact EB.
  - exact Et.
Qed.

Theorem denotes_lambda_body_step n (G : Ctx nat n) rho A t t' :
  @wf nat RankSorts (S n) (G & A) -> t →ᵝ t' ->
  (forall a x, denotes H s n G rho A a -> IN x (decode a) -> forall v,
    denotes H s (S n) (G & A) (fin_match x rho) t v ->
    denotes H s (S n) (G & A) (fin_match x rho) t' v) ->
  forall v, denotes H s n G rho (lam A t) v -> denotes H s n G rho (lam A t') v.
Proof.
  intros HG R IH v D.
  destruct (denotes_lambda_inversion H s n G rho A t v D)
    as [B [a [b [body [Tt [DA [DB [Dt [EB [Et E]]]]]]]]]].
  eapply denotes_equal; [eapply denotes_lambda with (B := B) (a := a) (b := b) (body := body) | apply EQ_sym; exact E].
  - eapply subject_reduction; [exact Tt | exact HG | exact R].
  - exact DA.
  - exact DB.
  - intros x Hx; eapply IH; [exact DA | exact Hx | apply Dt; exact Hx].
  - exact EB.
  - exact Et.
Qed.

Theorem denotes_application_function_step n (G : Ctx nat n) rho t t' u :
  @wf nat RankSorts n G -> t →ᵝ t' ->
  (forall v, denotes H s n G rho t v -> denotes H s n G rho t' v) ->
  forall v, denotes H s n G rho (app t u) v -> denotes H s n G rho (app t' u) v.
Proof.
  intros HG R IH v D.
  destruct (denotes_application_inversion H s n G rho t u v D)
    as [A [B [a [b [f [x [Tt [DA [DB [EB [Dt [Du E]]]]]]]]]]]].
  eapply denotes_equal; [eapply denotes_application with (A := A) (B := B) (a := a) (b := b) (f := f) (x := x) | apply EQ_sym; exact E].
  - eapply subject_reduction; [exact Tt | exact HG | exact R].
  - exact DA.
  - exact DB.
  - exact EB.
  - apply IH; exact Dt.
  - exact Du.
Qed.

Theorem denotes_application_argument n (G : Ctx nat n) rho t u u' :
  (forall v, denotes H s n G rho u v -> denotes H s n G rho u' v) ->
  forall v, denotes H s n G rho (app t u) v -> denotes H s n G rho (app t u') v.
Proof.
  intros IH v D.
  destruct (denotes_application_inversion H s n G rho t u v D)
    as [A [B [a [b [f [x [Tt [DA [DB [EB [Dt [Du E]]]]]]]]]]]].
  eapply denotes_equal; [eapply denotes_application with (A := A) (B := B) (a := a) (b := b) (f := f) (x := x) | apply EQ_sym; exact E].
  - exact Tt.
  - exact DA.
  - exact DB.
  - exact EB.
  - exact Dt.
  - apply IH; exact Du.
Qed.
End Congruence.
Print Assumptions denotes_product_domain_step.
Print Assumptions denotes_product_codomain.
Print Assumptions denotes_lambda_domain_step.
Print Assumptions denotes_lambda_body_step.
Print Assumptions denotes_application_function_step.
Print Assumptions denotes_application_argument.
