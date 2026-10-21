From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation
  Ranks DefEq Reduction AbstractRewriting Congruence.
From PTSrk.NormalizationComplexity Require Import Greedy Morphisms.
From PTSrk.SelfInterpreter Require Import BrownPalsberg DependentPHOAS
  IndexedEquality TypedHOASFaithful TarskiProducts TarskiCasts TarskiIdentity
  TarskiSignature TarskiOperations.
Import Context.

Module TarskiBinders.
Module BP := BrownPalsberg.BrownPalsberg.
Module DP := DependentPHOAS.DependentPHOAS.
Module IE := IndexedEquality.IndexedEquality.
Module TF := TypedHOASFaithful.TypedHOASFaithful.
Module TP := TarskiProducts.TarskiProducts.
Module TC := TarskiCasts.TarskiCasts.
Module TI := TarskiIdentity.TarskiIdentity.
Module TS := TarskiSignature.TarskiSignature.
Module TO := TarskiOperations.TarskiOperations.

(** Apply a family to the freshly bound variable, contracting just the
    administrative redex when the family is a lambda. Unlike arbitrary
    substitution, this cannot introduce a redex into a normal lambda body. *)
Definition bound_apply {n} (B : Term nat n) : Term nat (S n) :=
  match B with
  | lam _ body => body
  | _ => app (shift B) (var fzero)
  end.

Theorem bound_apply_reduces n (B : Term nat n) :
  reduces_to nat (S n) (app (shift B) (var fzero)) (bound_apply B).
Proof.
  destruct B; try reflexivity.
  cbn [bound_apply shift rename].
  replace B2 with (subst (rename (weak fsucc) B2) (var fzero)) at 2.
  - apply rtc_in, step_beta.
  - syntax_simp. rewrite <- (replace_var B2) at 2.
    apply replace_ext. intro i; dependent elimination i; reflexivity.
Qed.

Theorem bound_apply_normal n (B : Term nat n) :
  normalb B = true -> normalb (bound_apply B) = true.
Proof.
  intro HB; destruct B; cbn [bound_apply].
  all: try (cbn [normalb] in HB; apply andb_true_iff in HB; exact (proj2 HB)).
  all: unfold shift; cbn [normalb isLambda rename];
    rewrite ?TF.normalb_rename, ?TF.isLambda_rename; repeat rewrite andb_true_r;
    cbn [normalb isLambda] in HB; try exact HB; reflexivity.
Qed.

Theorem bound_apply_rename m n (rho : Fin m -> Fin n) B :
  rename (weak rho) (bound_apply B) = bound_apply (rename rho B).
Proof.
  destruct B; cbn [bound_apply rename]; try reflexivity; syntax_simp.
  f_equal. f_equal. apply rename_ext. intro i; dependent elimination i; reflexivity.
Qed.

Theorem bound_apply_replace m n (sigma : Fin m -> Term nat n) B :
  reduces_to nat (S n) (replace (transpose sigma) (bound_apply B))
    (bound_apply (replace sigma B)).
Proof.
  destruct B; cbn [bound_apply replace]; try reflexivity.
  all: rewrite ?replace_lift_shift; try reflexivity.
  apply bound_apply_reduces.
Qed.

Definition decoded {n} (Ea Eb A B : Term nat n) :=
  Π (app Ea A) (app (shift Eb) (bound_apply B)).

Theorem decoded_reduces n (Ea Eb A B : Term nat n) :
  reduces_to nat n (TP.decoded_product Ea Eb A B) (decoded Ea Eb A B).
Proof.
  unfold TP.decoded_product, DP.product, decoded.
  apply (@Π_cong_r nat (reduces_to nat) _ n).
  apply (@app_cong_r nat (reduces_to nat) _ (S n)), bound_apply_reduces.
Qed.

Theorem decoded_normal k a b A B :
  normalb A = true -> normalb B = true ->
  normalb (decoded (TS.decoder k a) (TS.decoder k b) A B) = true.
Proof.
  intros HA HB. destruct (TS.decoder_variable k a) as [i Ei].
  destruct (TS.decoder_variable k b) as [j Ej].
  unfold decoded; rewrite Ei, Ej.
  cbn [normalb isLambda shift rename].
  rewrite HA, (bound_apply_normal _ B HB); reflexivity.
Qed.

Lemma type_law_reduces c n (S S' T : Term nat n) :
  reduces_to nat n S S' ->
  reduces_to nat n (TC.type_law c S T) (TC.type_law c S' T).
Proof.
  intro H; unfold TC.type_law, IE.eq_type, BP.arr.
  apply (@Π_cong_r nat (reduces_to nat) _ n).
  apply (@Π_cong_l nat (reduces_to nat) _ (Datatypes.S n)).
  apply (@app_cong_r nat (reduces_to nat) _ (Datatypes.S n)).
  apply rename_rtc; exact H.
Qed.

Theorem decoded_typed k a b A B : a <= k -> b <= k ->
  @typ nat RankSorts _ (TS.context k) A (TS.carrier k a) ->
  @typ nat RankSorts _ (TS.context k) B
    (TP.code_family (TS.carrier k b) (TS.decoder k a) A) ->
  @typ nat RankSorts _ (TS.context k)
    (decoded (TS.decoder k a) (TS.decoder k b) A B) (𝓤 (Nat.max (S a) b)).
Proof.
  intros Ha Hb HA HB. eapply subject_reduction'.
  - exact (proj1 (TO.product_sorts k a b A B Ha Hb HA HB)).
  - apply TS.context_wf.
  - apply decoded_reduces.
Qed.

Theorem evidence_typed k a b A B : a <= k -> b <= k ->
  @typ nat RankSorts _ (TS.context k) A (TS.carrier k a) ->
  @typ nat RankSorts _ (TS.context k) B
    (TP.code_family (TS.carrier k b) (TS.decoder k a) A) ->
  @typ nat RankSorts _ (TS.context k) (TO.product_evidence k a b A B)
    (TC.type_law (Nat.max (S a) b)
      (decoded (TS.decoder k a) (TS.decoder k b) A B) (TO.encoded k a b A B)).
Proof.
  intros Ha Hb HA HB. eapply typ_conv.
  - apply TO.product_evidence_typed; assumption.
  - apply TC.type_law_sort.
    + apply decoded_typed; assumption.
    + exact (proj2 (TO.product_sorts k a b A B Ha Hb HA HB)).
  - apply def_equiv_prop; eexists; split; [| reflexivity].
    apply type_law_reduces, decoded_reduces.
Qed.

Definition abstract_term k a b (A B f : Term nat (TS.width k)) :=
  app (TC.forward (Nat.max (S a) b)
    (decoded (TS.decoder k a) (TS.decoder k b) A B)
    (TO.product_evidence k a b A B)) f.
Definition application_term k a b (A B f u : Term nat (TS.width k)) :=
  app (app (TC.backward (Nat.max (S a) b)
    (decoded (TS.decoder k a) (TS.decoder k b) A B)
    (TO.product_evidence k a b A B)) f) u.

Theorem abstract_term_typed k a b A B f : a <= k -> b <= k ->
  @typ nat RankSorts _ (TS.context k) A (TS.carrier k a) ->
  @typ nat RankSorts _ (TS.context k) B
    (TP.code_family (TS.carrier k b) (TS.decoder k a) A) ->
  @typ nat RankSorts _ (TS.context k) f
    (decoded (TS.decoder k a) (TS.decoder k b) A B) ->
  @typ nat RankSorts _ (TS.context k) (abstract_term k a b A B f)
    (TO.encoded k a b A B).
Proof.
  intros Ha Hb HA HB Hf; unfold abstract_term. eapply BP.arr_apply; [| exact Hf].
  apply (proj1 (TC.casts_typed _ _ _ _ _ _
    (decoded_typed k a b A B Ha Hb HA HB)
    (proj2 (TO.product_sorts k a b A B Ha Hb HA HB))
    (evidence_typed k a b A B Ha Hb HA HB))).
Qed.

Theorem application_term_typed k a b A B f u : a <= k -> b <= k ->
  @typ nat RankSorts _ (TS.context k) A (TS.carrier k a) ->
  @typ nat RankSorts _ (TS.context k) B
    (TP.code_family (TS.carrier k b) (TS.decoder k a) A) ->
  @typ nat RankSorts _ (TS.context k) f (TO.encoded k a b A B) ->
  @typ nat RankSorts _ (TS.context k) u (app (TS.decoder k a) A) ->
  @typ nat RankSorts _ (TS.context k) (application_term k a b A B f u)
    (app (TS.decoder k b) (app B u)).
Proof.
  intros Ha Hb HA HB Hf Hu.
  pose proof (proj2 (TC.casts_typed _ _ _ _ _ _
    (decoded_typed k a b A B Ha Hb HA HB)
    (proj2 (TO.product_sorts k a b A B Ha Hb HA HB))
    (evidence_typed k a b A B Ha Hb HA HB))) as Hcast.
  pose proof (BP.arr_apply _ _ _ _ _ Hcast Hf) as Hbody.
  assert (Horiginal : @typ nat RankSorts _ (TS.context k)
    (app (TC.backward (Nat.max (S a) b)
      (decoded (TS.decoder k a) (TS.decoder k b) A B)
      (TO.product_evidence k a b A B)) f) (TO.decoded k a b A B)).
  { eapply typ_conv; [exact Hbody | |].
    - exact (proj1 (TO.product_sorts k a b A B Ha Hb HA HB)).
    - apply def_equiv_prop; eexists; split; [reflexivity | apply decoded_reduces]. }
  unfold application_term, TO.decoded, TP.decoded_product, DP.product in *.
  replace (app (TS.decoder k b) (app B u)) with
    (subst (app (shift (TS.decoder k b)) (app (shift B) (var fzero))) u)
    by syntax_simp.
  eapply typ_app; eassumption.
Qed.

(** No normal-decoded-annotation premise: it follows from the normal inputs. *)
Theorem abstract_term_normal k a b A B f :
  normalb A = true -> normalb B = true -> normalb f = true ->
  normalb (abstract_term k a b A B f) = true.
Proof.
  intros HA HB Hf; unfold abstract_term.
  apply (proj1 (TC.neutral_casts_normal _ _ _ _ f
    (decoded_normal k a b A B HA HB)
    (TO.product_evidence_normal k a b A B HA HB) eq_refl Hf)).
Qed.

Theorem application_term_normal k a b A B f u :
  normalb A = true -> normalb B = true -> normalb f = true -> normalb u = true ->
  normalb (application_term k a b A B f u) = true.
Proof.
  intros HA HB Hf Hu.
  pose proof (proj2 (TC.neutral_casts_normal (Nat.max (S a) b) _ _ _ f
    (decoded_normal k a b A B HA HB)
    (TO.product_evidence_normal k a b A B HA HB) eq_refl Hf)) as H.
  change (normalb (app (TC.backward (Nat.max (S a) b)
    (decoded (TS.decoder k a) (TS.decoder k b) A B)
    (TO.product_evidence k a b A B)) f) && normalb u && negb false = true).
  now rewrite H, Hu.
Qed.

(** Substitution does not commute literally with the smart constructor when
    a neutral family becomes a lambda. Recovery needs no such false law:
    reflexivity eliminates the whole cast, including its annotation. *)
Theorem abstract_term_recovers k a b n (A B f : Term nat (TS.width k)) :
  a <= k -> b <= k ->
  reduces_to nat n (replace (@TS.fill k n) (abstract_term k a b A B f))
    (replace (TS.fill k) f).
Proof.
  intros Ha Hb; unfold abstract_term; cbn [replace].
  rewrite (proj1 (TC.casts_replace _ _ _ _ _ _)).
  eapply rtc_trans.
  - do 3 apply (@app_cong_l nat (reduces_to nat) _ n).
    apply TO.product_evidence_recovers; assumption.
  - apply (proj1 (TC.cast_application_reflexivity _ _ _ _ _)).
Qed.

Theorem application_term_recovers k a b n (A B f u : Term nat (TS.width k)) :
  a <= k -> b <= k ->
  reduces_to nat n (replace (@TS.fill k n) (application_term k a b A B f u))
    (app (replace (TS.fill k) f) (replace (TS.fill k) u)).
Proof.
  intros Ha Hb; unfold application_term; cbn [replace].
  rewrite (proj2 (TC.casts_replace _ _ _ _ _ _)).
  apply (@app_cong_l nat (reduces_to nat) _ n).
  eapply rtc_trans.
  - do 3 apply (@app_cong_l nat (reduces_to nat) _ n).
    apply TO.product_evidence_recovers; assumption.
  - apply (proj2 (TC.cast_application_reflexivity _ _ _ _ _)).
Qed.

(** A genuine dependent binder: the family body and term body may use the
    fresh variable. These are local introduction rules, not a source quoter. *)
Definition family k a (A : Term nat (TS.width k))
    (body : Term nat (S (TS.width k))) := lam (app (TS.decoder k a) A) body.
Definition binder k a b (A : Term nat (TS.width k))
    (Bbody body : Term nat (S (TS.width k))) :=
  abstract_term k a b A (family k a A Bbody) (family k a A body).

Theorem family_typed k a b A Bbody : a <= k -> b <= k ->
  @typ nat RankSorts _ (TS.context k) A (TS.carrier k a) ->
  @typ nat RankSorts _ (TS.context k & app (TS.decoder k a) A)
    Bbody (shift (TS.carrier k b)) ->
  @typ nat RankSorts _ (TS.context k) (family k a A Bbody)
    (TP.code_family (TS.carrier k b) (TS.decoder k a) A).
Proof.
  intros Ha Hb HA HB. unfold family, TP.code_family, BP.arr.
  eapply typ_λ with (ℓ := a); [| exact HB].
  eapply BP.arr_apply; [apply TS.decoder_typed; lia | exact HA].
Qed.

Theorem binder_typed k a b A Bbody body : a <= k -> b <= k ->
  @typ nat RankSorts _ (TS.context k) A (TS.carrier k a) ->
  @typ nat RankSorts _ (TS.context k & app (TS.decoder k a) A)
    Bbody (shift (TS.carrier k b)) ->
  @typ nat RankSorts _ (TS.context k & app (TS.decoder k a) A)
    body (app (shift (TS.decoder k b)) Bbody) ->
  @typ nat RankSorts _ (TS.context k) (binder k a b A Bbody body)
    (TO.encoded k a b A (family k a A Bbody)).
Proof.
  intros Ha Hb HA HB Hbody. apply abstract_term_typed; try assumption.
  - apply family_typed; assumption.
  - unfold family, decoded; cbn [bound_apply].
    eapply typ_λ with (ℓ := a); [| exact Hbody].
    eapply BP.arr_apply; [apply TS.decoder_typed; lia | exact HA].
Qed.

Lemma family_normal k a A body : normalb A = true -> normalb body = true ->
  normalb (family k a A body) = true.
Proof.
  intros HA Hb. destruct (TS.decoder_variable k a) as [i Hi].
  unfold family; rewrite Hi; cbn [normalb isLambda]; now rewrite HA, Hb.
Qed.

Theorem binder_normal k a b A Bbody body :
  normalb A = true -> normalb Bbody = true -> normalb body = true ->
  normalb (binder k a b A Bbody body) = true.
Proof.
  intros HA HB Ht. apply abstract_term_normal; try assumption;
    apply family_normal; assumption.
Qed.

Theorem binder_recovers k a b n A Bbody body : a <= k -> b <= k ->
  reduces_to nat n (replace (@TS.fill k n) (binder k a b A Bbody body))
    (lam (replace (TS.fill k) (app (TS.decoder k a) A))
      (replace (transpose (TS.fill k)) body)).
Proof. intros Ha Hb; apply abstract_term_recovers; assumption. Qed.

(** The smart annotation does not erase the supplied family: it also
    occurs unchanged in the neutral law application. This is LOCAL input
    injectivity, not yet injectivity of a full source-derivation translation. *)
Theorem binder_inputs_injective k a b A Bbody body A' Bbody' body' :
  binder k a b A Bbody body = binder k a b A' Bbody' body' ->
  A = A' /\ Bbody = Bbody' /\ body = body'.
Proof.
  unfold binder, abstract_term, TC.forward, TO.product_evidence, family.
  intro H. repeat match goal with
  | H : app _ _ = app _ _ |- _ => injection H; clear H; intros
  | H : lam _ _ = lam _ _ |- _ => injection H; clear H; intros
  end. auto.
Qed.

Theorem binder_conversion_injective k a b A Bbody body A' Bbody' body' :
  normalb A = true -> normalb Bbody = true -> normalb body = true ->
  normalb A' = true -> normalb Bbody' = true -> normalb body' = true ->
  def_equiv nat _ (binder k a b A Bbody body) (binder k a b A' Bbody' body') ->
  A = A' /\ Bbody = Bbody' /\ body = body'.
Proof.
  intros HA HB Ht HA' HB' Ht' HE. apply binder_inputs_injective with (k := k) (a := a) (b := b).
  apply ChurchSyntaxFaithful.normal_conversion_identity;
    [apply binder_normal | apply binder_normal |]; assumption.
Qed.

Print Assumptions bound_apply_reduces.
Print Assumptions bound_apply_normal.
Print Assumptions bound_apply_rename.
Print Assumptions bound_apply_replace.
Print Assumptions decoded_normal.
Print Assumptions decoded_typed.
Print Assumptions evidence_typed.
Print Assumptions abstract_term_typed.
Print Assumptions application_term_typed.
Print Assumptions abstract_term_normal.
Print Assumptions application_term_normal.
Print Assumptions abstract_term_recovers.
Print Assumptions application_term_recovers.
Print Assumptions family_typed.
Print Assumptions binder_typed.
Print Assumptions binder_normal.
Print Assumptions binder_recovers.
Print Assumptions binder_inputs_injective.
Print Assumptions binder_conversion_injective.
End TarskiBinders.
