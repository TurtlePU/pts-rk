From Stdlib Require Import Arith.PeanoNat Bool.Bool.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting.
From PTSrk.NormalizationComplexity Require Import Greedy Morphisms.
From PTSrk.SelfInterpreter Require Import QuotationTree QuotationCache
  TarskiContext UniformTelescope.
Import Context.

(** Recursive constructor views survive simultaneous source/target
    renaming. The new environment is arbitrary, with actual inherited
    carrier/decoder compatibility; equality of proof records is not used. *)
Module QuotationViewRenaming.
Module QT := QuotationTree.QuotationTree.
Module QC := QuotationCache.QuotationCache.
Module CX := TarskiContext.TarskiContext.
Module UT := UniformTelescope.UniformTelescope.

Record compatible {k m p G H} (E : CX.environment k m G)
    (F : CX.environment k p H) (theta : Fin m -> Fin p) : Prop := {
  carriers : forall r, rename theta (CX.carrier E r) = CX.carrier F r;
  decoders : forall r, rename theta (CX.decoder E r) = CX.decoder F r
}.

Definition square {n m p l} (fill : Fin m -> Term nat n)
    (newfill : Fin l -> Term nat p) (rho : Fin n -> Fin p) (theta : Fin m -> Fin l) :=
  forall i, newfill (theta i) = rename rho (fill i).

Lemma square_lift n m p l fill newfill rho theta :
  @square n m p l fill newfill rho theta ->
  square (transpose fill) (transpose newfill) (weak rho) (weak theta).
Proof.
  intros HS i; dependent elimination i as [fzero | fsucc i]; [reflexivity |].
  change (shift (newfill (theta i)) = rename (weak rho) (shift (fill i))).
  rewrite HS; syntax_simp.
Qed.

Lemma square_replace n m p l fill newfill rho theta t :
  @square n m p l fill newfill rho theta ->
  replace newfill (rename theta t) = rename rho (replace fill t).
Proof. intro HS; rewrite replace_rename, rename_replace; apply replace_ext; exact HS. Qed.

Lemma compatible_weaken k m p G H (E : CX.environment k m G)
    (F : CX.environment k p H) theta A :
  compatible E F theta ->
  compatible (CX.weaken_environment E A)
    (CX.weaken_environment F (rename theta A)) (weak theta).
Proof.
  intros [HC HE]; constructor; intro r.
  - change (rename (weak theta) (shift (CX.carrier E r)) = shift (CX.carrier F r)).
    rewrite <- HC; syntax_simp.
  - change (rename (weak theta) (shift (CX.decoder E r)) = shift (CX.decoder F r)).
    rewrite <- HE; syntax_simp.
Qed.

Lemma product_head_rename n (t : Term nat n) p (rho : Fin n -> Fin p) :
  QC.product_head (rename rho t) = QC.product_head t.
Proof. destruct t; reflexivity. Qed.

Theorem rename_certificate k n m G E fill t r code p l H F newfill rho theta :
  QC.code_certificate E fill t r code -> TypedRen G H theta ->
  @compatible k m l G H E F theta -> @square n m p l fill newfill rho theta ->
  QC.code_certificate F newfill (rename rho t) r (rename theta code).
Proof.
  intros [Hr HC HN HL HR] HT HE HS; constructor; [exact Hr | | | |].
  - rewrite <- (carriers _ _ _ HE r); apply typing_rename with (G := G); assumption.
  - rewrite UT.normalb_rename; exact HN.
  - rewrite UT.isLambda_rename; exact HL.
  - rewrite (square_replace _ _ _ _ _ _ _ _ _ HS); apply rename_rtc; exact HR.
Qed.

Fixpoint rename_view {k n m G E fill t r code}
    (v : QC.code_view k n m G E fill t r code) {p l} (H : Ctx nat l)
    (F : CX.environment k l H) (newfill : Fin l -> Term nat p)
    (rho : Fin n -> Fin p) (theta : Fin m -> Fin l)
    (HT : TypedRen G H theta) (HE : compatible E F theta)
    (HS : square fill newfill rho theta) {struct v} :
    QC.code_view k p l H F newfill (rename rho t) r (rename theta code).
Proof.
  destruct v as [n m G E fill t r q Hnon HC |
    n m G E fill A B a b root Ac Bc Ha Hb va vb HC].
  - pose (q' := QT.rename_indexed n m t q p l rho theta).
    assert (HV : QT.value q' = rename theta (QT.value q)) by apply QT.cache_rename.
    rewrite <- HV; apply QC.cv_atomic.
    + rewrite product_head_rename; exact Hnon.
    + rewrite HV; eapply rename_certificate; eassumption.
  - cbn [rename]; eapply QC.cv_product; [exact Ha | exact Hb | | |].
    + exact (@rename_view k n m G E fill A a Ac va p l H F newfill rho theta HT HE HS).
    + assert (HD : rename theta (app (CX.decoder E a) Ac) =
        app (CX.decoder F a) (rename theta Ac)).
      { cbn [rename]; now rewrite (decoders _ _ _ HE a). }
      pose (v' := @rename_view k (S n) (S m) _ _ _ B b Bc vb (S p) (S l)
        (H & rename theta (app (CX.decoder E a) Ac))
        (CX.weaken_environment F (rename theta (app (CX.decoder E a) Ac)))
        (transpose newfill) (weak rho) (weak theta)
        (typed_ren_lift G H theta (app (CX.decoder E a) Ac) HT)
        (compatible_weaken k m l G H E F theta (app (CX.decoder E a) Ac) HE)
        (square_lift n m p l fill newfill rho theta HS)).
      rewrite HD in v'; exact v'.
    + exact (rename_certificate k n m G E fill (Π A B) (Nat.max (S a) b)
        root p l H F newfill rho theta HC HT HE HS).
Defined.

Definition rename_shape {k n m G E fill t}
    (v : QC.shape_view k n m G E fill t) {p l} (H : Ctx nat l)
    (F : CX.environment k l H) (newfill : Fin l -> Term nat p)
    (rho : Fin n -> Fin p) (theta : Fin m -> Fin l)
    (HT : TypedRen G H theta) (HE : compatible E F theta)
    (HS : square fill newfill rho theta) :
    QC.shape_view k p l H F newfill (rename rho t).
Proof.
  destruct v as [n m G E fill t q Hnon |
    n m G E fill A B a b Ac Bc Ha Hb va vb].
  - apply QC.sv_atomic with (q := QT.rename_indexed n m t q p l rho theta).
    rewrite product_head_rename; exact Hnon.
  - cbn [rename]; eapply QC.sv_product; [exact Ha | exact Hb | |].
    + exact (rename_view va H F newfill rho theta HT HE HS).
    + assert (HD : rename theta (app (CX.decoder E a) Ac) =
        app (CX.decoder F a) (rename theta Ac)).
      { cbn [rename]; now rewrite (decoders _ _ _ HE a). }
      pose (v' := rename_view vb (H & rename theta (app (CX.decoder E a) Ac))
        (CX.weaken_environment F (rename theta (app (CX.decoder E a) Ac)))
        (transpose newfill) (weak rho) (weak theta)
        (typed_ren_lift G H theta (app (CX.decoder E a) Ac) HT)
        (compatible_weaken k m l G H E F theta (app (CX.decoder E a) Ac) HE)
        (square_lift n m p l fill newfill rho theta HS)).
      rewrite HD in v'; exact v'.
Defined.

Lemma compatible_shift k m G (E : CX.environment k m G) A :
  compatible E (CX.weaken_environment E A) fsucc.
Proof.
  constructor; intro r; unfold CX.carrier, CX.decoder, CX.weaken_environment,
    CX.rename_environment; cbn [CX.ren]; rewrite rename_comp; reflexivity.
Qed.

Lemma compatible_renaming k m p G H (E : CX.environment k m G) theta HT :
  compatible E (CX.rename_environment k m p G H E theta HT) theta.
Proof.
  constructor; intro r; unfold CX.carrier, CX.decoder, CX.rename_environment;
    cbn [CX.ren]; rewrite rename_comp; reflexivity.
Qed.

Definition weaken_view {k n m G E fill t r code}
    (v : QC.code_view k n m G E fill t r code) (A : Term nat m) :
    QC.code_view k (S n) (S m) (G & A) (CX.weaken_environment E A)
      (transpose fill) (shift t) r (shift code) :=
  rename_view v (G & A) (CX.weaken_environment E A) (transpose fill) fsucc fsucc
    (typed_ren_shift G A) (compatible_shift k m G E A) (fun i => eq_refl).

Definition weaken_shape {k n m G E fill t}
    (v : QC.shape_view k n m G E fill t) (A : Term nat m) :
    QC.shape_view k (S n) (S m) (G & A) (CX.weaken_environment E A)
      (transpose fill) (shift t) :=
  rename_shape v (G & A) (CX.weaken_environment E A) (transpose fill) fsucc fsucc
    (typed_ren_shift G A) (compatible_shift k m G E A) (fun i => eq_refl).

Print Assumptions square_lift.
Print Assumptions square_replace.
Print Assumptions compatible_weaken.
Print Assumptions compatible_renaming.
Print Assumptions rename_certificate.
Print Assumptions rename_view.
Print Assumptions rename_shape.
Print Assumptions weaken_view.
Print Assumptions weaken_shape.
End QuotationViewRenaming.
