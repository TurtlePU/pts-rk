From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia.
From PTSrk Require Import Syntax Context Typing Preservation Ranks Reduction
  AbstractRewriting Congruence DefEq.
From PTSrk.NormalizationComplexity Require Import Greedy Morphisms.
From PTSrk.SelfInterpreter Require Import BrownPalsberg TypedHOASFaithful.
Import Context.

(** Rank-indexed Leibniz transport, expressed entirely by ORIGINAL annotated
    PTS products, lambdas and applications. A witness is an object term, not
    an assumed definitional equality or a new primitive. The motive rank is
    explicit; no same-level predicative symmetry or cumulativity is assumed. *)
Module IndexedEquality.
Module BP := BrownPalsberg.BrownPalsberg.
Module TF := TypedHOASFaithful.TypedHOASFaithful.

Definition motive_type b {n} (A : Term nat n) := BP.arr A (𝓤 b).
Definition eq_type b {n} (A u v : Term nat n) : Term nat n :=
  Π (motive_type b A)
    (BP.arr (app (var fzero) (shift u)) (app (var fzero) (shift v))).
Definition refl_case b {n} (A u : Term nat n) : Term nat n :=
  lam (motive_type b A) (lam (app (var fzero) (shift u)) (var fzero)).
Definition transport {n} (e P p : Term nat n) := app (app e P) p.

Lemma motive_type_rename b m n (rho : Fin m -> Fin n) A :
  rename rho (motive_type b A) = motive_type b (rename rho A).
Proof. unfold motive_type, BP.arr; syntax_simp. Qed.

Lemma motive_type_replace b m n (sigma : Fin m -> Term nat n) A :
  replace sigma (motive_type b A) = motive_type b (replace sigma A).
Proof. unfold motive_type, BP.arr; syntax_simp. Qed.

Lemma eq_type_rename b m n (rho : Fin m -> Fin n) A u v :
  rename rho (eq_type b A u v) =
  eq_type b (rename rho A) (rename rho u) (rename rho v).
Proof. unfold eq_type, motive_type, BP.arr; syntax_simp. Qed.

Lemma eq_type_replace b m n (sigma : Fin m -> Term nat n) A u v :
  replace sigma (eq_type b A u v) =
  eq_type b (replace sigma A) (replace sigma u) (replace sigma v).
Proof. unfold eq_type, motive_type, BP.arr; syntax_simp. Qed.

Lemma refl_case_rename b m n (rho : Fin m -> Fin n) A u :
  rename rho (refl_case b A u) = refl_case b (rename rho A) (rename rho u).
Proof. unfold refl_case, motive_type, BP.arr; syntax_simp. Qed.

Lemma refl_case_replace b m n (sigma : Fin m -> Term nat n) A u :
  replace sigma (refl_case b A u) = refl_case b (replace sigma A) (replace sigma u).
Proof. unfold refl_case, motive_type, BP.arr; syntax_simp. Qed.

Lemma transport_rename m n (rho : Fin m -> Fin n) e P p :
  rename rho (transport e P p) = transport (rename rho e) (rename rho P) (rename rho p).
Proof. reflexivity. Qed.

Lemma transport_replace m n (sigma : Fin m -> Term nat n) e P p :
  replace sigma (transport e P p) =
  transport (replace sigma e) (replace sigma P) (replace sigma p).
Proof. reflexivity. Qed.

Lemma motive_type_sort a b n (G : Ctx nat n) A :
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G (motive_type b A) (𝓤 (S a)).
Proof.
  intro HA; unfold motive_type. replace (S a) with (Nat.max (S a) 0) by lia.
  apply BP.arr_sort; [exact HA | constructor; reflexivity].
Qed.

Lemma bound_motive_application b n (G : Ctx nat n) A u :
  @typ nat RankSorts n G u A ->
  @typ nat RankSorts (S n) (G & motive_type b A)
    (app (var fzero) (shift u)) (𝓤 b).
Proof.
  intro Hu. eapply BP.arr_apply with (A := shift A).
  - change (typ (G & motive_type b A) (var fzero) ((G & motive_type b A) !! fzero)).
    constructor.
  - apply weakening; exact Hu.
Qed.

Theorem eq_type_sort a b n (G : Ctx nat n) A u v :
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G u A -> @typ nat RankSorts n G v A ->
  @typ nat RankSorts n G (eq_type b A u v) (𝓤 (Nat.max (a+2) (b+1))).
Proof.
  intros HA Hu Hv; unfold eq_type.
  eapply typ_Π with (ℓₜ := S a) (ℓᵤ := S b).
  - apply motive_type_sort; exact HA.
  - replace (S b) with (Nat.max (S b) b) by lia.
    apply BP.arr_sort; apply bound_motive_application; assumption.
  - change (Nat.max (a+2) (b+1) = Nat.max (S (S a)) (S b)); f_equal; lia.
Qed.

Theorem refl_case_typed a b n (G : Ctx nat n) A u :
  @typ nat RankSorts n G A (𝓤 a) -> @typ nat RankSorts n G u A ->
  @typ nat RankSorts n G (refl_case b A u) (eq_type b A u u).
Proof.
  intros HA Hu; unfold refl_case, eq_type, BP.arr.
  eapply typ_λ with (ℓ := S a); [apply motive_type_sort; exact HA |].
  eapply typ_λ with (ℓ := b); [apply bound_motive_application; exact Hu |].
  change (typ ((G & motive_type b A) & app (var fzero) (shift u))
    (var fzero) (((G & motive_type b A) & app (var fzero) (shift u)) !! fzero)).
  constructor.
Qed.

Lemma eq_specialize b n (G : Ctx nat n) A u v e P :
  @typ nat RankSorts n G e (eq_type b A u v) ->
  @typ nat RankSorts n G P (motive_type b A) ->
  @typ nat RankSorts n G (app e P) (BP.arr (app P u) (app P v)).
Proof.
  intros He HP; unfold eq_type in He.
  pose proof (typ_app (motive_type b A) He HP) as H.
  replace (BP.arr (app P u) (app P v)) with
    (subst (BP.arr (app (var fzero) (shift u)) (app (var fzero) (shift v))) P).
  - exact H.
  - unfold subst; rewrite TypedHOAS.TypedHOAS.arr_replace; syntax_simp.
Qed.

(** Direct original application typing, not subject expansion from recovery.
    An equality witness is an ordinary input with its explicit original type. *)
Theorem transport_typed b n (G : Ctx nat n) A u v e P p :
  @typ nat RankSorts n G e (eq_type b A u v) ->
  @typ nat RankSorts n G P (motive_type b A) ->
  @typ nat RankSorts n G p (app P u) ->
  @typ nat RankSorts n G (transport e P p) (app P v).
Proof.
  intros He HP Hp; unfold transport. eapply BP.arr_apply;
    [eapply eq_specialize; eassumption | exact Hp].
Qed.

Theorem transport_refl b n (A u P p : Term nat n) :
  reduces_to nat n (transport (refl_case b A u) P p) p.
Proof.
  unfold transport, refl_case. eapply rtc_step; [apply step_app_left, step_beta |].
  unfold motive_type, BP.arr. syntax_simp.
  apply rtc_in, step_beta.
Qed.

Definition refl_type a b {n} : Term nat n :=
  Π (𝓤 a) (Π (var fzero) (eq_type b (var (fsucc fzero)) (var fzero) (var fzero))).
Definition refl a b {n} : Term nat n :=
  lam (𝓤 a) (lam (var fzero) (refl_case b (var (fsucc fzero)) (var fzero))).

(** These builders are closed object terms, usable in every target scope. *)
Theorem refl_typed a b n (G : Ctx nat n) :
  @typ nat RankSorts n G (refl a b) (refl_type a b).
Proof.
  unfold refl, refl_type. eapply typ_λ with (ℓ := 0); [constructor; reflexivity |].
  eapply typ_λ with (ℓ := a).
  - change (typ (G & 𝓤 a) (var fzero) ((G & 𝓤 a) !! fzero)); constructor.
  - apply refl_case_typed with (a := a).
    + change (typ ((G & 𝓤 a) & var fzero) (shift (var fzero)) (shift (𝓤 a))).
      apply weakening. change (typ (G & 𝓤 a) (var fzero) ((G & 𝓤 a) !! fzero)); constructor.
    + change (typ ((G & 𝓤 a) & var fzero) (var fzero)
        (((G & 𝓤 a) & var fzero) !! fzero)); constructor.
Qed.

Theorem refl_type_sort a b n (G : Ctx nat n) :
  @typ nat RankSorts n G (refl_type a b) (𝓤 (Nat.max (a+2) (b+1))).
Proof.
  unfold refl_type.
  eapply typ_Π with (ℓₜ := 0) (ℓᵤ := Nat.max (a+2) (b+1)).
  - constructor; reflexivity.
  - eapply typ_Π with (ℓₜ := a) (ℓᵤ := Nat.max (a+2) (b+1)).
    + change (typ (G & 𝓤 a) (var fzero) ((G & 𝓤 a) !! fzero)); constructor.
    + apply eq_type_sort with (a := a).
      * change (typ ((G & 𝓤 a) & var fzero) (shift (var fzero)) (shift (𝓤 a))).
        apply weakening. change (typ (G & 𝓤 a) (var fzero) ((G & 𝓤 a) !! fzero)); constructor.
      * change (typ ((G & 𝓤 a) & var fzero) (var fzero)
          (((G & 𝓤 a) & var fzero) !! fzero)); constructor.
      * change (typ ((G & 𝓤 a) & var fzero) (var fzero)
          (((G & 𝓤 a) & var fzero) !! fzero)); constructor.
    + change (Nat.max (a+2) (b+1) = Nat.max (S a) (Nat.max (a+2) (b+1))); lia.
  - change (Nat.max (a+2) (b+1) = Nat.max 1 (Nat.max (a+2) (b+1))); lia.
Qed.

Theorem refl_specializes a b n (A u : Term nat n) :
  reduces_to nat n (app (app (refl a b) A) u) (refl_case b A u).
Proof.
  unfold refl, refl_case, motive_type, BP.arr.
  eapply rtc_step; [apply step_app_left, step_beta |].
  eapply rtc_step; [apply step_beta |]. syntax_simp. reflexivity.
Qed.

Lemma eq_type_normal b n (A u v : Term nat n) :
  normalb A = true -> normalb u = true -> normalb v = true ->
  normalb (eq_type b A u v) = true.
Proof.
  intros HA Hu Hv; unfold eq_type, motive_type, BP.arr, shift.
  repeat progress (cbn [normalb isLambda]; rewrite ?TF.normalb_rename).
  rewrite HA, Hu, Hv; reflexivity.
Qed.

Lemma refl_case_normal b n (A u : Term nat n) :
  normalb A = true -> normalb u = true -> normalb (refl_case b A u) = true.
Proof.
  intros HA Hu; unfold refl_case, motive_type, BP.arr, shift.
  repeat progress (cbn [normalb isLambda]; rewrite ?TF.normalb_rename).
  rewrite HA, Hu; reflexivity.
Qed.

Lemma refl_normal a b n : normalb (@refl a b n) = true.
Proof. reflexivity. Qed.

Print Assumptions eq_type_sort.
Print Assumptions refl_case_typed.
Print Assumptions transport_typed.
Print Assumptions transport_refl.
Print Assumptions refl_typed.
Print Assumptions refl_type_sort.
Print Assumptions refl_specializes.
Print Assumptions eq_type_replace.
Print Assumptions refl_case_replace.
Print Assumptions eq_type_normal.
Print Assumptions refl_case_normal.
End IndexedEquality.
