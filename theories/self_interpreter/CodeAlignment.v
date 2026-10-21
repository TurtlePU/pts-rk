From Stdlib Require Import Bool.Bool Lists.List Arith.PeanoNat Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting Congruence DefEq.
From PTSrk.NormalizationComplexity Require Import Greedy Morphisms.
From PTSrk.SelfInterpreter Require Import BrownPalsberg IndexedEquality
  ContextualTelescope UniformTelescope ContextualEqualityExtension
  TarskiContext TarskiProducts ScopedTarski.
Import Context ListNotations.

(** Actual use of a globally allocated equality-only field. A code's cache
    and its structural view may differ; independently realized equality
    aligns their decoded types without providing a semantic payload. *)
Module CodeAlignment.
Module BP := BrownPalsberg.BrownPalsberg.
Module IE := IndexedEquality.IndexedEquality.
Module CT := ContextualTelescope.ContextualTelescope.
Module UT := UniformTelescope.UniformTelescope.
Module EX := ContextualEqualityExtension.ContextualEqualityExtension.
Module CX := TarskiContext.TarskiContext.
Module TP := TarskiProducts.TarskiProducts.
Module ST := ScopedTarski.ScopedTarski.

Definition align {n rs} (D : CT.telescope n rs) E q :=
  IE.transport (EX.field_apply D) (EX.lifted E) (EX.lifted q).

Lemma lifted_typed d n rs (G : Ctx nat n) (D : CT.telescope n rs) C a b t T :
  @typ nat RankSorts _ (CT.context D G) t T ->
  @typ nat RankSorts _ (CT.context (EX.shifted_domains D) (EX.extension d G D C a b))
    (EX.lifted t) (EX.lifted T).
Proof.
  intro Ht; apply typing_rename with (G := CT.context D G); [| exact Ht].
  apply CT.context_ren, typed_ren_shift.
Qed.

Lemma lift_sub_square rs : forall m n p (rho : Fin m -> Fin n)
    (sigma : Fin m -> Term nat p) (tau : Fin n -> Term nat p),
  (forall i, tau (rho i) = sigma i) ->
  forall i, CT.lift_sub rs tau (CT.lift_ren rs rho i) = CT.lift_sub rs sigma i.
Proof.
  induction rs; intros m n p rho sigma tau H i; cbn [CT.lift_sub CT.lift_ren].
  - apply H.
  - apply IHrs; intro j; dependent elimination j as [fzero | fsucc j].
    + reflexivity.
    + change (shift (tau (rho j)) = shift (sigma j)); now rewrite H.
Qed.

Theorem fill_lifted d n rs (D : CT.telescope n rs) sigma C a t :
  replace (CT.lift_sub rs (EX.fill d D sigma C a)) (EX.lifted t) = EX.filled sigma t.
Proof.
  unfold EX.lifted, EX.filled; rewrite replace_rename; apply replace_ext.
  apply lift_sub_square; intro i; reflexivity.
Qed.

Theorem align_typed r n rs (G : Ctx nat n) (D : CT.telescope n rs) C a b E q :
  @typ nat RankSorts _ (CT.context D G) E (BP.arr C (𝓤 r)) ->
  @typ nat RankSorts _ (CT.context D G) q (app E a) ->
  @typ nat RankSorts _ (CT.context (EX.shifted_domains D) (EX.extension r G D C a b))
    (align D E q) (app (EX.lifted E) (EX.lifted b)).
Proof.
  intros HE Hq; apply EX.field_transport_typed.
  - unfold IE.motive_type; change (typ
      (CT.context (EX.shifted_domains D) (EX.extension r G D C a b))
      (EX.lifted E) (EX.lifted (BP.arr C (𝓤 r)))).
    apply lifted_typed; exact HE.
  - change (typ (CT.context (EX.shifted_domains D) (EX.extension r G D C a b))
      (EX.lifted q) (EX.lifted (app E a))); apply lifted_typed; exact Hq.
Qed.

Theorem align_normal n rs (D : CT.telescope n rs) E q :
  normalb E = true -> normalb q = true -> normalb (align D E q) = true.
Proof.
  intros HE Hq; apply EX.field_transport_normal; unfold EX.lifted;
    rewrite UT.normalb_rename; assumption.
Qed.

Theorem align_neutral n rs (D : CT.telescope n rs) E q : isLambda (align D E q) = false.
Proof. reflexivity. Qed.

Theorem align_filled_erases r n rs (D : CT.telescope n rs) sigma C a E q :
  reduces_to nat _ (replace (CT.lift_sub rs (EX.fill r D sigma C a)) (align D E q))
    (EX.filled sigma q).
Proof.
  unfold align; rewrite <- (fill_lifted r n rs D sigma C a q).
  apply EX.filled_transport_erases.
Qed.

Theorem align_preserves_recovery r n rs (D : CT.telescope n rs) sigma C a E q t :
  reduces_to nat _ (EX.filled sigma q) t ->
  reduces_to nat _ (replace (CT.lift_sub rs (EX.fill r D sigma C a)) (align D E q)) t.
Proof. intro H; eapply rtc_trans; [apply align_filled_erases | exact H]. Qed.

Theorem align_filled_typed c r n rs (G : Ctx nat n) (D : CT.telescope n rs)
    sigma C a b E q :
  TypedSub G ε sigma -> CT.formed G D ->
  @typ nat RankSorts _ (CT.context D G) C (𝓤 c) ->
  @typ nat RankSorts _ (CT.context D G) a C -> @typ nat RankSorts _ (CT.context D G) b C ->
  def_equiv nat _ (EX.filled sigma a) (EX.filled sigma b) ->
  @typ nat RankSorts _ (CT.context D G) E (BP.arr C (𝓤 r)) ->
  @typ nat RankSorts _ (CT.context D G) q (app E a) ->
  @typ nat RankSorts _ (CT.context (EX.filled_domains D sigma) ε)
    (replace (CT.lift_sub rs (EX.fill r D sigma C a)) (align D E q))
    (app (EX.filled sigma E) (EX.filled sigma b)).
Proof.
  intros HS HD HC Ha Hb Hab HE Hq.
  pose proof (EX.filled_transport_typed c r n rs G D sigma C a b (EX.lifted E) (EX.lifted q)
    HS HD HC Ha Hb Hab) as H.
  cbn [replace] in H; rewrite !fill_lifted in H; apply H.
  - unfold IE.motive_type; change (typ
      (CT.context (EX.shifted_domains D) (EX.extension r G D C a b))
      (EX.lifted E) (EX.lifted (BP.arr C (𝓤 r)))); apply lifted_typed; exact HE.
  - change (typ (CT.context (EX.shifted_domains D) (EX.extension r G D C a b))
      (EX.lifted q) (EX.lifted (app E a))); apply lifted_typed; exact Hq.
Qed.

(** The inherited Tarski interface remains a typed variable environment
    after adding the global field, including under all local binders. *)
Definition aligned_environment k r n rs (G : Ctx nat n) (D : CT.telescope n rs)
    C a b (E : CX.environment k _ (CT.context D G)) :=
  CX.rename_environment k _ _ (CT.context D G)
    (CT.context (EX.shifted_domains D) (EX.extension r G D C a b)) E
    (CT.lift_ren rs fsucc)
    (CT.context_ren n rs D G (S n) (EX.extension r G D C a b) fsucc
      (typed_ren_shift G (EX.declaration r D C a b))).

Lemma lifted_carrier k r n rs G (D : CT.telescope n rs) C a b E j :
  EX.lifted (CX.carrier E j) =
    CX.carrier (aligned_environment k r n rs G D C a b E) j.
Proof. unfold EX.lifted, CX.carrier; apply ST.inherited_rename. Qed.

Lemma lifted_decoder k r n rs G (D : CT.telescope n rs) C a b E j :
  EX.lifted (CX.decoder E j) =
    CX.decoder (aligned_environment k r n rs G D C a b E) j.
Proof. unfold EX.lifted; apply ST.decoder_rename. Qed.

Lemma lifted_product_code k r n rs G (D : CT.telescope n rs) C a b E i j A B :
  EX.lifted (CX.product_code E i j A B) =
    CX.product_code (aligned_environment k r n rs G D C a b E) i j
      (EX.lifted A) (EX.lifted B).
Proof.
  unfold EX.lifted, CX.product_code; cbn [rename]; f_equal; f_equal.
Qed.

Definition application {k n rs G} (D : CT.telescope n rs)
    (E : CX.environment k _ (CT.context D G)) a b R A B f u :=
  ST.application_term
    (aligned_environment k (Nat.max (S a) b) n rs G D
      (CX.carrier E (Nat.max (S a) b)) R (CX.product_code E a b A B) E)
    a b (EX.lifted A) (EX.lifted B)
    (align D (CX.decoder E (Nat.max (S a) b)) f) (EX.lifted u).

Theorem application_typed k n rs G (D : CT.telescope n rs) E a b R A B f u :
  @wf nat RankSorts n G -> CT.formed G D -> a <= k -> b <= k ->
  @typ nat RankSorts _ (CT.context D G) R (CX.carrier E (Nat.max (S a) b)) ->
  @typ nat RankSorts _ (CT.context D G) A (CX.carrier E a) ->
  @typ nat RankSorts _ (CT.context D G) B
    (TP.code_family (CX.carrier E b) (CX.decoder E a) A) ->
  @typ nat RankSorts _ (CT.context D G) f (app (CX.decoder E (Nat.max (S a) b)) R) ->
  @typ nat RankSorts _ (CT.context D G) u (app (CX.decoder E a) A) ->
  @typ nat RankSorts _
    (CT.context (EX.shifted_domains D)
      (EX.extension (Nat.max (S a) b) G D (CX.carrier E (Nat.max (S a) b))
        R (CX.product_code E a b A B)))
    (@application k n rs G D E a b R A B f u)
    (EX.lifted (app (CX.decoder E b) (app B u))).
Proof.
  intros HG HD Ha Hb HR HA HB Hf Hu; unfold application.
  change (EX.lifted (app (CX.decoder E b) (app B u))) with
    (app (EX.lifted (CX.decoder E b)) (app (EX.lifted B) (EX.lifted u))).
  rewrite (lifted_decoder k (Nat.max (S a) b) n rs G D
    (CX.carrier E (Nat.max (S a) b)) R (CX.product_code E a b A B) E b).
  apply ST.application_term_typed; try assumption.
  - eapply EX.local_context_wf; [exact HG | exact HD | | exact HR |].
    + apply CX.carrier_typed; lia.
    + apply CX.product_code_typed; assumption.
  - rewrite <- lifted_carrier; apply lifted_typed; exact HA.
  - rewrite <- lifted_carrier, <- lifted_decoder.
    change (TP.code_family (EX.lifted (CX.carrier E b))
      (EX.lifted (CX.decoder E a)) (EX.lifted A)) with
      (EX.lifted (TP.code_family (CX.carrier E b) (CX.decoder E a) A)).
    apply lifted_typed; exact HB.
  - unfold CX.encoded; rewrite <- lifted_decoder, <- lifted_product_code.
    apply align_typed; [apply CX.decoder_typed; lia | exact Hf].
  - rewrite <- lifted_decoder.
    change (app (EX.lifted (CX.decoder E a)) (EX.lifted A)) with
      (EX.lifted (app (CX.decoder E a) A)).
    apply lifted_typed; exact Hu.
Qed.

Theorem application_normal k n rs G (D : CT.telescope n rs) E a b R A B f u :
  normalb A = true -> normalb B = true -> normalb f = true -> normalb u = true ->
  normalb (@application k n rs G D E a b R A B f u) = true.
Proof.
  intros HA HB Hf Hu; unfold application; apply ST.application_term_normal.
  - unfold EX.lifted; now rewrite UT.normalb_rename.
  - unfold EX.lifted; now rewrite UT.normalb_rename.
  - apply align_normal; [reflexivity | exact Hf].
  - unfold EX.lifted; now rewrite UT.normalb_rename.
Qed.

(** Alignment disappears inside the ORIGINAL smart application. Its
    subsequent semantic recovery can therefore be reused without assuming
    recovery as an input to field allocation. *)
Theorem application_filled_erases k n rs G (D : CT.telescope n rs) E a b R A B f u sigma :
  reduces_to nat _
    (replace (CT.lift_sub rs (EX.fill (Nat.max (S a) b) D sigma
      (CX.carrier E (Nat.max (S a) b)) R))
      (@application k n rs G D E a b R A B f u))
    (EX.filled sigma (ST.application_term E a b A B f u)).
Proof.
  rewrite <- (fill_lifted (Nat.max (S a) b) n rs D sigma
    (CX.carrier E (Nat.max (S a) b)) R (ST.application_term E a b A B f u)).
  unfold application, EX.lifted.
  rewrite (ST.application_term_rename k _ _ (CT.context D G)
    (CT.context (EX.shifted_domains D)
      (EX.extension (Nat.max (S a) b) G D (CX.carrier E (Nat.max (S a) b))
        R (CX.product_code E a b A B))) E (CT.lift_ren rs fsucc)
    (CT.context_ren n rs D G (S n) _ fsucc
      (typed_ren_shift G (EX.declaration (Nat.max (S a) b) D
        (CX.carrier E (Nat.max (S a) b)) R (CX.product_code E a b A B))))).
  unfold ST.application_term; cbn [replace].
  apply (@app_cong_l nat (reduces_to nat) _ _), (@app_cong_r nat (reduces_to nat) _ _).
  unfold align; apply EX.filled_transport_erases.
Qed.

Print Assumptions lifted_typed.
Print Assumptions fill_lifted.
Print Assumptions align_typed.
Print Assumptions align_normal.
Print Assumptions align_neutral.
Print Assumptions align_filled_erases.
Print Assumptions align_preserves_recovery.
Print Assumptions align_filled_typed.
Print Assumptions application_typed.
Print Assumptions application_normal.
Print Assumptions application_filled_erases.
End CodeAlignment.
