From Stdlib Require Import Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation
  Ranks DefEq Reduction AbstractRewriting Congruence.
From PTSrk.SelfInterpreter Require Import BrownPalsberg.
Import Context.

Module DependentPHOAS.
Module BP := BrownPalsberg.BrownPalsberg.

(** Local genuinely dependent, externally rank-indexed PHOAS operations.
    These are original PTS terms and judgments.  They are not a recursive
    interpretation of all dependent source derivations: in particular no
    conversion coherence for arbitrary abstract handlers is assumed. *)

Definition family_domain {n} (Fa A : Term nat n) b :=
  BP.arr (app Fa A) (𝓤 b).

Definition product {n} (Fa Fb A B : Term nat n) :=
  Π (app Fa A) (app (shift Fb) (app (shift B) (var fzero))).

Definition abs_case_type {n} (Fa Fb Fc A B : Term nat n) :=
  BP.arr (product Fa Fb A B) (app Fc (product Fa Fb A B)).
Definition app_case_type {n} (Fa Fb Fc A B : Term nat n) :=
  BP.arr (app Fc (product Fa Fb A B)) (product Fa Fb A B).

Lemma product_sort n (G : Ctx nat n) Fa Fb A B a b :
  @typ nat RankSorts n G Fa (BP.family_type a a) ->
  @typ nat RankSorts n G Fb (BP.family_type b b) ->
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G B (family_domain Fa A b) ->
  @typ nat RankSorts n G (product Fa Fb A B) (𝓤 (Nat.max (S a) b)).
Proof.
  intros HF HG HA HB. unfold product.
  eapply typ_Π with (ℓₜ := a) (ℓᵤ := b).
  - eapply BP.family_apply; eassumption.
  - eapply BP.family_apply with (a := b).
    + change (typ (G & app Fa A) (shift Fb) (shift (BP.family_type b b))).
      apply weakening; exact HG.
    + eapply BP.arr_apply with (A := shift (app Fa A)).
      * change (typ (G & app Fa A) (shift B)
          (BP.arr (shift (app Fa A)) (shift (𝓤 b)))).
        rewrite <- BP.arr_shift. apply weakening; exact HB.
      * change (typ (G & app Fa A) (var fzero) ((G & app Fa A) !! fzero)).
        constructor.
  - reflexivity.
Qed.

Theorem dependent_abs_operation_typing n (G : Ctx nat n) Fa Fb Fc A B op body a :
  @typ nat RankSorts n G Fa (BP.family_type a a) ->
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G op (abs_case_type Fa Fb Fc A B) ->
  @typ nat RankSorts (S n) (G & app Fa A) body
    (app (shift Fb) (app (shift B) (var fzero))) ->
  @typ nat RankSorts n G (app op (lam (app Fa A) body))
    (app Fc (product Fa Fb A B)).
Proof.
  intros HF HA Hop Hbody. eapply BP.arr_apply; [exact Hop |].
  unfold product. eapply typ_λ with (ℓ := a).
  - eapply BP.family_apply; eassumption.
  - exact Hbody.
Qed.

Theorem dependent_app_operation_typing n (G : Ctx nat n) Fa Fb Fc A B op f u :
  @typ nat RankSorts n G op (app_case_type Fa Fb Fc A B) ->
  @typ nat RankSorts n G f (app Fc (product Fa Fb A B)) ->
  @typ nat RankSorts n G u (app Fa A) ->
  @typ nat RankSorts n G (app (app op f) u) (app Fb (app B u)).
Proof.
  intros Hop Hf Hu.
  pose proof (BP.arr_apply G op f _ _ Hop Hf) as HD.
  unfold product in HD. pose proof (typ_app (app Fa A) HD Hu) as H.
  replace (app Fb (app B u)) with
    (subst (app (shift Fb) (app (shift B) (var fzero))) u) by syntax_simp.
  exact H.
Qed.

Theorem dependent_case_type_sorts n (G : Ctx nat n) Fa Fb Fc A B a b :
  @typ nat RankSorts n G Fa (BP.family_type a a) ->
  @typ nat RankSorts n G Fb (BP.family_type b b) ->
  @typ nat RankSorts n G Fc
    (BP.family_type (Nat.max (S a) b) (Nat.max (S a) b)) ->
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G B (family_domain Fa A b) ->
  @typ nat RankSorts n G (abs_case_type Fa Fb Fc A B)
    (𝓤 (S (Nat.max (S a) b))) /\
  @typ nat RankSorts n G (app_case_type Fa Fb Fc A B)
    (𝓤 (S (Nat.max (S a) b))).
Proof.
  intros HF HG HH HA HB.
  pose proof (product_sort n G Fa Fb A B a b HF HG HA HB) as HD.
  pose proof (BP.family_apply G Fc (product Fa Fb A B) _ _ HH HD) as HI.
  unfold abs_case_type, app_case_type.
  replace (S (Nat.max (S a) b)) with
    (Nat.max (S (Nat.max (S a) b)) (Nat.max (S a) b)) by lia.
  split; apply BP.arr_sort; assumption.
Qed.

Definition indexed_abs_type a b {n} (Fa Fb Fc : Term nat n) :=
  Π (𝓤 a) (Π (family_domain (shift Fa) (var fzero) b)
    (abs_case_type (shift (shift Fa)) (shift (shift Fb)) (shift (shift Fc))
      (var (fsucc fzero)) (var fzero))).
Definition indexed_app_type a b {n} (Fa Fb Fc : Term nat n) :=
  Π (𝓤 a) (Π (family_domain (shift Fa) (var fzero) b)
    (app_case_type (shift (shift Fa)) (shift (shift Fb)) (shift (shift Fc))
      (var (fsucc fzero)) (var fzero))).

Lemma family_domain_shift n (Fa A : Term nat n) b :
  shift (family_domain Fa A b) = family_domain (shift Fa) (shift A) b.
Proof. unfold family_domain. rewrite BP.arr_shift. reflexivity. Qed.

Theorem dependent_handler_type_sorts a b n (G : Ctx nat n) Fa Fb Fc :
  @typ nat RankSorts n G Fa (BP.family_type a a) ->
  @typ nat RankSorts n G Fb (BP.family_type b b) ->
  @typ nat RankSorts n G Fc
    (BP.family_type (Nat.max (S a) b) (Nat.max (S a) b)) ->
  @typ nat RankSorts n G (indexed_abs_type a b Fa Fb Fc)
    (𝓤 (S (Nat.max (S a) b))) /\
  @typ nat RankSorts n G (indexed_app_type a b Fa Fb Fc)
    (𝓤 (S (Nat.max (S a) b))).
Proof.
  intros HF HG HH.
  set (GA := G & 𝓤 a).
  set (BA := @family_domain (S n) (shift Fa) (var fzero) b).
  assert (HFa : typ GA (shift Fa) (BP.family_type a a)).
  { change (typ (G & 𝓤 a) (shift Fa) (shift (BP.family_type a a))).
    apply weakening; exact HF. }
  assert (HA : typ GA (var fzero) (𝓤 a)).
  { change (typ GA (var fzero) (GA !! fzero)). constructor. }
  assert (HBA : typ GA BA (𝓤 (S a))).
  { unfold BA, family_domain. replace (S a) with (Nat.max (S a) 0) by lia.
    apply BP.arr_sort; [eapply BP.family_apply; eassumption | constructor; reflexivity]. }
  assert (Hshift : forall F r, typ G F (BP.family_type r r) ->
    typ (GA & BA) (shift (shift F)) (BP.family_type r r)).
  { intros F r H. change (typ (GA & BA)
      (shift (shift F)) (shift (shift (BP.family_type r r)))).
    apply weakening, weakening; exact H. }
  assert (HA' : typ (GA & BA) (var (fsucc fzero)) (𝓤 a)).
  { change (typ (GA & BA) (shift (var fzero)) (shift (𝓤 a))).
    apply weakening; exact HA. }
  assert (HB : typ (GA & BA) (var fzero)
    (family_domain (shift (shift Fa)) (var (fsucc fzero)) b)).
  { change (typ (GA & BA) (var fzero) (family_domain (shift (shift Fa)) (shift (var fzero)) b)).
    rewrite <- family_domain_shift.
    change (typ (GA & BA) (var fzero) ((GA & BA) !! fzero)). constructor. }
  destruct (dependent_case_type_sorts _ (GA & BA) _ _ _ _ _ a b
    (Hshift Fa a HF) (Hshift Fb b HG) (Hshift Fc _ HH) HA' HB) as [Habs Happ].
  unfold indexed_abs_type, indexed_app_type. split.
  - eapply typ_Π with (ℓₜ := 0) (ℓᵤ := S (Nat.max (S a) b)).
    + apply typ_𝓤; reflexivity.
    + eapply typ_Π with (ℓₜ := S a) (ℓᵤ := S (Nat.max (S a) b)).
      * exact HBA.
      * exact Habs.
      * change (S (Nat.max (S a) b) = Nat.max (S (S a)) (S (Nat.max (S a) b))); lia.
    + change (S (Nat.max (S a) b) = Nat.max 1 (S (Nat.max (S a) b))); lia.
  - eapply typ_Π with (ℓₜ := 0) (ℓᵤ := S (Nat.max (S a) b)).
    + apply typ_𝓤; reflexivity.
    + eapply typ_Π with (ℓₜ := S a) (ℓᵤ := S (Nat.max (S a) b)).
      * exact HBA.
      * exact Happ.
      * change (S (Nat.max (S a) b) = Nat.max (S (S a)) (S (Nat.max (S a) b))); lia.
    + change (S (Nat.max (S a) b) = Nat.max 1 (S (Nat.max (S a) b))); lia.
Qed.

(** At identity specialization the body family remains genuinely dependent.
    B is an arbitrary original term of type A -> U_b, not a constant type. *)
Definition plain_product {n} (A B : Term nat n) :=
  Π A (app (shift B) (var fzero)).
Definition abs_identity_case {n} (A B : Term nat n) :=
  lam (plain_product A B) (var fzero).
Definition app_identity_case {n} (A B : Term nat n) :=
  lam (plain_product A B)
    (lam (shift A) (app (var (fsucc fzero)) (var fzero))).

Lemma plain_product_sort n (G : Ctx nat n) A B a b :
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G B (BP.arr A (𝓤 b)) ->
  @typ nat RankSorts n G (plain_product A B) (𝓤 (Nat.max (S a) b)).
Proof.
  intros HA HB. unfold plain_product.
  eapply typ_Π with (ℓₜ := a) (ℓᵤ := b); [exact HA | | reflexivity].
  eapply BP.arr_apply with (A := shift A).
  - change (typ (G & A) (shift B) (BP.arr (shift A) (shift (𝓤 b)))).
    rewrite <- BP.arr_shift; apply weakening; exact HB.
  - change (typ (G & A) (var fzero) ((G & A) !! fzero)). constructor.
Qed.

Lemma plain_product_rename m n (rho : Fin m -> Fin n) (A B : Term nat m) :
  rename rho (plain_product A B) = plain_product (rename rho A) (rename rho B).
Proof. unfold plain_product. syntax_simp. Qed.

Lemma plain_product_shift n (A B : Term nat n) :
  shift (plain_product A B) = plain_product (shift A) (shift B).
Proof. apply plain_product_rename. Qed.

Lemma plain_product_apply n (G : Ctx nat n) f u A B :
  @typ nat RankSorts n G f (plain_product A B) ->
  @typ nat RankSorts n G u A ->
  @typ nat RankSorts n G (app f u) (app B u).
Proof.
  intros Hf Hu. replace (app B u) with (subst (app (shift B) (var fzero)) u) by syntax_simp.
  eapply typ_app; eassumption.
Qed.

Theorem plain_identity_cases_typing a b n (G : Ctx nat n) A B :
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G B (BP.arr A (𝓤 b)) ->
  @typ nat RankSorts n G (abs_identity_case A B)
    (BP.arr (plain_product A B) (plain_product A B)) /\
  @typ nat RankSorts n G (app_identity_case A B)
    (BP.arr (plain_product A B) (plain_product A B)).
Proof.
  intros HA HB. pose proof (plain_product_sort n G A B a b HA HB) as HD.
  split.
  - unfold abs_identity_case, BP.arr. eapply typ_λ with (ℓ := Nat.max (S a) b).
    + exact HD.
    + change (typ (G & plain_product A B) (var fzero)
        ((G & plain_product A B) !! fzero)). constructor.
  - unfold app_identity_case, BP.arr. eapply typ_λ with (ℓ := Nat.max (S a) b).
    + exact HD.
    + change (typ (G & plain_product A B)
        (lam (shift A) (app (var (fsucc fzero)) (var fzero))) (shift (plain_product A B))).
      rewrite plain_product_shift. unfold plain_product.
      eapply typ_λ with (ℓ := a).
      * change (typ (G & plain_product A B) (shift A) (shift (𝓤 a))).
        apply weakening; exact HA.
      * eapply plain_product_apply with (A := shift (shift A)).
        -- rewrite <- !plain_product_shift.
           change (typ ((G & plain_product A B) & shift A) (var (fsucc fzero))
             (((G & plain_product A B) & shift A) !! fsucc fzero)). constructor.
        -- change (typ ((G & plain_product A B) & shift A) (var fzero)
             (((G & plain_product A B) & shift A) !! fzero)). constructor.
Qed.

(** Conversion at identity specialization is proved from actual beta
    reductions, not supplied as an algebra law. *)
Lemma product_identity_recovers a b n (A B : Term nat n) :
  reduces_to nat n (product (BP.type_identity a) (BP.type_identity b) A B)
    (plain_product A B).
Proof.
  unfold product, plain_product.
  apply (@Π_cong_par nat (reduces_to nat) _ _ n).
  - apply rtc_in, BP.type_identity_beta.
  - change (reduces_to nat (S n)
      (app (BP.type_identity b) (app (shift B) (var fzero)))
      (app (shift B) (var fzero))).
    apply rtc_in, BP.type_identity_beta.
Qed.

Lemma identity_case_types_recover a b n (A B : Term nat n) :
  reduces_to nat n
    (abs_case_type (BP.type_identity a) (BP.type_identity b)
      (BP.type_identity (Nat.max (S a) b)) A B)
    (BP.arr (plain_product A B) (plain_product A B)) /\
  reduces_to nat n
    (app_case_type (BP.type_identity a) (BP.type_identity b)
      (BP.type_identity (Nat.max (S a) b)) A B)
    (BP.arr (plain_product A B) (plain_product A B)).
Proof.
  pose proof (product_identity_recovers a b n A B) as HD.
  assert (HI : reduces_to nat n
    (app (BP.type_identity (Nat.max (S a) b))
      (product (BP.type_identity a) (BP.type_identity b) A B)) (plain_product A B)).
  { eapply rtc_step; [apply BP.type_identity_beta | exact HD]. }
  unfold abs_case_type, app_case_type. split; apply BP.arr_reduces; assumption.
Qed.

Lemma identity_family_domain_typed a b n (G : Ctx nat n) A B :
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G B (BP.arr A (𝓤 b)) ->
  @typ nat RankSorts n G B (family_domain (BP.type_identity a) A b).
Proof.
  intros HA HB. eapply typ_conv with (T := BP.arr A (𝓤 b)) (ℓ := S a).
  - exact HB.
  - unfold family_domain. replace (S a) with (Nat.max (S a) 0) by lia.
    apply BP.arr_sort.
    + eapply BP.family_apply; [apply BP.type_identity_typing | exact HA].
    + constructor; reflexivity.
  - apply def_equiv_prop. exists (BP.arr A (𝓤 b)). split; [reflexivity |].
    apply BP.arr_reduces; [apply rtc_in, BP.type_identity_beta | reflexivity].
Qed.

Theorem dependent_identity_case_typing a b n (G : Ctx nat n) A B :
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G B (BP.arr A (𝓤 b)) ->
  @typ nat RankSorts n G (abs_identity_case A B)
    (abs_case_type (BP.type_identity a) (BP.type_identity b)
      (BP.type_identity (Nat.max (S a) b)) A B) /\
  @typ nat RankSorts n G (app_identity_case A B)
    (app_case_type (BP.type_identity a) (BP.type_identity b)
      (BP.type_identity (Nat.max (S a) b)) A B).
Proof.
  intros HA HB.
  destruct (dependent_case_type_sorts n G _ _ _ A B a b
    (BP.type_identity_typing a n G) (BP.type_identity_typing b n G)
    (BP.type_identity_typing _ n G) HA
    (identity_family_domain_typed a b n G A B HA HB)) as [HSabs HSapp].
  destruct (plain_identity_cases_typing a b n G A B HA HB) as [Habs Happ].
  destruct (identity_case_types_recover a b n A B) as [HRabs HRapp].
  split; eapply typ_conv with (T := BP.arr (plain_product A B) (plain_product A B))
    (ℓ := S (Nat.max (S a) b)); try eassumption;
    apply def_equiv_prop; exists (BP.arr (plain_product A B) (plain_product A B));
    split; try reflexivity; assumption.
Qed.

Definition plain_indexed_type a b {n} : Term nat n :=
  Π (𝓤 a) (Π (BP.arr (var fzero) (𝓤 b))
    (BP.arr (plain_product (var (fsucc fzero)) (var fzero))
      (plain_product (var (fsucc fzero)) (var fzero)))).
Definition abs_identity a b {n} : Term nat n :=
  lam (𝓤 a) (lam (BP.arr (var fzero) (𝓤 b))
    (abs_identity_case (var (fsucc fzero)) (var fzero))).
Definition app_identity a b {n} : Term nat n :=
  lam (𝓤 a) (lam (BP.arr (var fzero) (𝓤 b))
    (app_identity_case (var (fsucc fzero)) (var fzero))).

Lemma plain_indexed_identity_typing a b n (G : Ctx nat n) :
  @typ nat RankSorts n G (abs_identity a b) (plain_indexed_type a b) /\
  @typ nat RankSorts n G (app_identity a b) (plain_indexed_type a b).
Proof.
  set (GA := G & 𝓤 a).
  set (BA := @BP.arr (S n) (var fzero) (𝓤 b)).
  assert (HA : typ GA (var fzero) (𝓤 a)).
  { change (typ GA (var fzero) (GA !! fzero)); constructor. }
  assert (HBA : typ GA BA (𝓤 (S a))).
  { unfold BA. replace (S a) with (Nat.max (S a) 0) by lia.
    apply BP.arr_sort; [exact HA | constructor; reflexivity]. }
  assert (HA' : typ (GA & BA) (var (fsucc fzero)) (𝓤 a)).
  { change (typ (GA & BA) (shift (var fzero)) (shift (𝓤 a))). apply weakening; exact HA. }
  assert (HB : typ (GA & BA) (var fzero) (BP.arr (var (fsucc fzero)) (𝓤 b))).
  { change (typ (GA & BA) (var fzero) (BP.arr (shift (var fzero)) (shift (𝓤 b)))).
    rewrite <- BP.arr_shift. change (typ (GA & BA) (var fzero) ((GA & BA) !! fzero)).
    constructor. }
  destruct (plain_identity_cases_typing a b _ (GA & BA) _ _ HA' HB) as [Hab Hap].
  unfold abs_identity, app_identity, plain_indexed_type. split.
  - eapply typ_λ with (ℓ := 0); [constructor; reflexivity |].
    eapply typ_λ with (ℓ := S a); [exact HBA | exact Hab].
  - eapply typ_λ with (ℓ := 0); [constructor; reflexivity |].
    eapply typ_λ with (ℓ := S a); [exact HBA | exact Hap].
Qed.

Lemma specialize_plain_handler a b n (G : Ctx nat n) h A B :
  @typ nat RankSorts n G h (plain_indexed_type a b) ->
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G B (BP.arr A (𝓤 b)) ->
  @typ nat RankSorts n G (app (app h A) B)
    (BP.arr (plain_product A B) (plain_product A B)).
Proof.
  intros Hh HA HB. unfold plain_indexed_type in Hh.
  pose proof (typ_app (𝓤 a) Hh HA) as Hfirst.
  assert (Heq : subst (Π (BP.arr (var fzero) (𝓤 b))
      (BP.arr (plain_product (var (fsucc fzero)) (var fzero))
        (plain_product (var (fsucc fzero)) (var fzero)))) A =
    Π (BP.arr A (𝓤 b))
      (BP.arr (plain_product (shift A) (var fzero))
        (plain_product (shift A) (var fzero)))).
  { unfold plain_product, BP.arr. syntax_simp. unfold shift. syntax_simp. }
  rewrite Heq in Hfirst. pose proof (typ_app (BP.arr A (𝓤 b)) Hfirst HB) as Hsecond.
  replace (BP.arr (plain_product A B) (plain_product A B)) with
    (subst (BP.arr (plain_product (shift A) (var fzero))
      (plain_product (shift A) (var fzero))) B).
  - exact Hsecond.
  - unfold plain_product, BP.arr. syntax_simp. unfold shift. syntax_simp.
    rewrite BP.replace_fsucc. reflexivity.
Qed.

(** Direct application typing precedes and is independent of recovery;
    no subject expansion from the beta reduct is used. *)
Theorem dependent_identity_application_typed a b n (G : Ctx nat n) A B f u :
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G B (BP.arr A (𝓤 b)) ->
  @typ nat RankSorts n G f (plain_product A B) ->
  @typ nat RankSorts n G u A ->
  @typ nat RankSorts n G
    (app (app (app (app (app_identity a b) A) B) f) u) (app B u).
Proof.
  intros HA HB Hf Hu. eapply plain_product_apply; [| exact Hu].
  eapply BP.arr_apply; [| exact Hf].
  eapply specialize_plain_handler; [apply (proj2 (plain_indexed_identity_typing a b n G)) | exact HA | exact HB].
Qed.

Lemma identity_indexed_types_recover a b n :
  reduces_to nat n
    (indexed_abs_type a b (BP.type_identity a) (BP.type_identity b)
      (BP.type_identity (Nat.max (S a) b))) (plain_indexed_type a b) /\
  reduces_to nat n
    (indexed_app_type a b (BP.type_identity a) (BP.type_identity b)
      (BP.type_identity (Nat.max (S a) b))) (plain_indexed_type a b).
Proof.
  unfold indexed_abs_type, indexed_app_type, plain_indexed_type.
  split; apply (@Π_cong_par nat (reduces_to nat) _ _ n); try reflexivity;
    apply (@Π_cong_par nat (reduces_to nat) _ _ (S n)).
  - unfold family_domain. apply BP.arr_reduces; [apply rtc_in, BP.type_identity_beta | reflexivity].
  - apply (proj1 (identity_case_types_recover a b _ _ _)).
  - unfold family_domain. apply BP.arr_reduces; [apply rtc_in, BP.type_identity_beta | reflexivity].
  - apply (proj2 (identity_case_types_recover a b _ _ _)).
Qed.

Theorem dependent_indexed_identity_handlers_typing a b n (G : Ctx nat n) :
  @typ nat RankSorts n G (abs_identity a b)
    (indexed_abs_type a b (BP.type_identity a) (BP.type_identity b)
      (BP.type_identity (Nat.max (S a) b))) /\
  @typ nat RankSorts n G (app_identity a b)
    (indexed_app_type a b (BP.type_identity a) (BP.type_identity b)
      (BP.type_identity (Nat.max (S a) b))).
Proof.
  destruct (dependent_handler_type_sorts a b n G _ _ _
    (BP.type_identity_typing a n G) (BP.type_identity_typing b n G)
    (BP.type_identity_typing _ n G)) as [HSabs HSapp].
  destruct (plain_indexed_identity_typing a b n G) as [Habs Happ].
  destruct (identity_indexed_types_recover a b n) as [HRabs HRapp].
  split; eapply typ_conv with (T := plain_indexed_type a b)
    (ℓ := S (Nat.max (S a) b)); try eassumption;
    apply def_equiv_prop; exists (plain_indexed_type a b);
    split; try reflexivity; assumption.
Qed.

Lemma abs_identity_specializes a b n (A B : Term nat n) :
  reduces_to nat n (app (app (abs_identity a b) A) B) (abs_identity_case A B).
Proof.
  unfold abs_identity, abs_identity_case, plain_product, BP.arr.
  eapply rtc_step; [apply step_app_left, step_beta |].
  eapply rtc_step; [apply step_beta |]. syntax_simp. reflexivity.
Qed.

Lemma app_identity_specializes a b n (A B : Term nat n) :
  reduces_to nat n (app (app (app_identity a b) A) B) (app_identity_case A B).
Proof.
  unfold app_identity, app_identity_case, plain_product, BP.arr.
  eapply rtc_step; [apply step_app_left, step_beta |].
  eapply rtc_step; [apply step_beta |]. syntax_simp.
  rewrite BP.replace_fsucc. reflexivity.
Qed.

Theorem dependent_abs_recovers a b n (A B f : Term nat n) :
  reduces_to nat n (app (app (app (abs_identity a b) A) B) f) f.
Proof.
  eapply rtc_trans.
  - apply (@app_cong_l nat (reduces_to nat) _ n), abs_identity_specializes.
  - unfold abs_identity_case. apply rtc_in, step_beta.
Qed.

Theorem dependent_app_recovers a b n (A B f u : Term nat n) :
  reduces_to nat n (app (app (app (app (app_identity a b) A) B) f) u) (app f u).
Proof.
  eapply rtc_trans.
  - apply (@app_cong_l nat (reduces_to nat) _ n), (@app_cong_l nat (reduces_to nat) _ n),
      app_identity_specializes.
  - unfold app_identity_case. eapply rtc_step; [apply step_app_left, step_beta |].
    cbn [subst replace transpose fin_match].
    replace (subst (shift A) f) with A by syntax_simp.
    replace (app f u) with (subst (app (shift f) (var fzero)) u) by syntax_simp.
    apply rtc_in, step_beta.
Qed.

(** In the candidate convention interpreting sort literals by themselves,
    a represented type B:U_b has term carrier F_0(U_b), since U_b:U_0.
    Using that carrier as an annotation needs a universe decoder El_b.
    Its type is well-sorted; no generic beta law for El/Abs/App is asserted. *)
Definition universe_decode_type {n} (F0 : Term nat n) b :=
  BP.arr (app F0 (𝓤 b)) (𝓤 b).

Theorem universe_decode_type_sort b n (G : Ctx nat n) F0 :
  @typ nat RankSorts n G F0 (BP.family_type 0 0) ->
  @typ nat RankSorts n G (universe_decode_type F0 b) (𝓤 1).
Proof.
  intro HF. unfold universe_decode_type.
  change (typ G (BP.arr (app F0 (𝓤 b)) (𝓤 b)) (𝓤 (Nat.max (S 0) 0))).
  apply BP.arr_sort.
  - eapply BP.family_apply; [exact HF | constructor; reflexivity].
  - constructor; reflexivity.
Qed.

Theorem universe_decode_identity_typed b n (G : Ctx nat n) :
  @typ nat RankSorts n G (BP.type_identity b)
    (universe_decode_type (BP.type_identity 0) b).
Proof.
  eapply typ_conv with (T := BP.family_type b b) (ℓ := 1).
  - apply BP.type_identity_typing.
  - apply universe_decode_type_sort, BP.type_identity_typing.
  - apply def_equiv_prop. exists (BP.family_type b b). split; [reflexivity |].
    unfold universe_decode_type. change (reduces_to nat n
      (BP.arr (app (BP.type_identity 0) (𝓤 b)) (𝓤 b)) (BP.arr (𝓤 b) (𝓤 b))).
    apply BP.arr_reduces; [apply rtc_in, BP.type_identity_beta | reflexivity].
Qed.

Theorem universe_decode_identity_recovers b n (B : Term nat n) :
  step nat n (app (BP.type_identity b) B) B.
Proof. apply BP.type_identity_beta. Qed.

Print Assumptions product_sort.
Print Assumptions dependent_abs_operation_typing.
Print Assumptions dependent_app_operation_typing.
Print Assumptions dependent_case_type_sorts.
Print Assumptions dependent_handler_type_sorts.
Print Assumptions plain_identity_cases_typing.
Print Assumptions dependent_identity_case_typing.
Print Assumptions dependent_indexed_identity_handlers_typing.
Print Assumptions dependent_identity_application_typed.
Print Assumptions dependent_abs_recovers.
Print Assumptions dependent_app_recovers.
Print Assumptions universe_decode_type_sort.
Print Assumptions universe_decode_identity_typed.
Print Assumptions universe_decode_identity_recovers.

End DependentPHOAS.
