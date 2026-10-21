From PTSrk Require Import -(notations) Syntax Context Typing Preservation
  Ranks DefEq Reduction AbstractRewriting.
From PTSrk.NormalizationComplexity Require Import Greedy.
From PTSrk.SelfInterpreter Require Import BrownPalsberg ChurchSyntaxFaithful.
Import Context.

Module EtaBoundary.
Module BP := BrownPalsberg.BrownPalsberg.

(** A limited beta-only boundary, not an impossibility theorem for PHOAS.
    The two closed functions agree after application to both arguments,
    but they are distinct normal terms. An arbitrary dependent type family
    can distinguish a function variable from its eta expansion by original
    beta conversion. No eta or object-language extensionality is assumed. *)

Definition function_type {n} : Term nat n := BP.arr (𝓤 0) (𝓤 0).
Definition direct {n} : Term nat n := lam function_type (var fzero).
Definition eta_expand {n} (f : Term nat n) : Term nat n :=
  lam (𝓤 0) (app (shift f) (var fzero)).
Definition expanded {n} : Term nat n :=
  lam function_type (eta_expand (var fzero)).

Lemma function_type_sort n (G : Ctx nat n) :
  @typ nat RankSorts n G function_type (𝓤 1).
Proof.
  unfold function_type. apply BP.arr_sort with (a := 0) (b := 0);
    constructor; reflexivity.
Qed.

Lemma direct_typing n (G : Ctx nat n) :
  @typ nat RankSorts n G direct (BP.arr function_type function_type).
Proof.
  unfold direct, BP.arr. apply typ_λ with (ℓ := 1).
  - apply function_type_sort.
  - change (typ (G & function_type) (var fzero)
      ((G & function_type) !! fzero)). constructor.
Qed.

Lemma eta_expand_typing n (G : Ctx nat n) f :
  @typ nat RankSorts n G f function_type ->
  @typ nat RankSorts n G (eta_expand f) function_type.
Proof.
  intro Hf. unfold eta_expand, function_type, BP.arr.
  apply typ_λ with (ℓ := 0); [constructor; reflexivity |].
  eapply BP.arr_apply with (A := 𝓤 0).
  - change (typ (G & 𝓤 0) (shift f) (shift function_type)).
    apply weakening; exact Hf.
  - change (typ (G & 𝓤 0) (var fzero) ((G & 𝓤 0) !! fzero)).
    constructor.
Qed.

Lemma expanded_typing n (G : Ctx nat n) :
  @typ nat RankSorts n G expanded (BP.arr function_type function_type).
Proof.
  unfold expanded, BP.arr. apply typ_λ with (ℓ := 1).
  - apply function_type_sort.
  - change (typ (G & function_type) (eta_expand (var fzero)) function_type).
    apply eta_expand_typing.
    change (typ (G & function_type) (var fzero)
      ((G & function_type) !! fzero)); constructor.
Qed.

Theorem closed_functions_typing :
  @typ nat RankSorts 0 ε direct (BP.arr function_type function_type) /\
  @typ nat RankSorts 0 ε expanded (BP.arr function_type function_type) /\
  @typ nat RankSorts 0 ε (BP.arr function_type function_type) (𝓤 2).
Proof.
  split; [apply direct_typing |]. split; [apply expanded_typing |].
  apply BP.arr_sort with (a := 1) (b := 1); apply function_type_sort.
Qed.

Theorem closed_functions_normal_distinct :
  normalb (@direct 0) = true /\ normalb (@expanded 0) = true /\
  @direct 0 <> @expanded 0.
Proof. split; [reflexivity |]. split; [reflexivity | discriminate]. Qed.

Theorem closed_functions_not_convertible :
  ~ def_equiv nat 0 direct expanded.
Proof.
  intro H. pose proof (normal_conversion_identity 0 direct expanded
    eq_refl eq_refl H) as E. discriminate E.
Qed.

Lemma direct_apply n (f : Term nat n) : step nat n (app direct f) f.
Proof. unfold direct. apply step_beta. Qed.

Lemma expanded_apply n (f : Term nat n) :
  step nat n (app expanded f) (eta_expand f).
Proof.
  unfold expanded.
  replace (eta_expand f) with (subst (eta_expand (var fzero)) f) by
    (unfold eta_expand; syntax_simp).
  apply step_beta.
Qed.

Lemma eta_apply n (f x : Term nat n) :
  step nat n (app (eta_expand f) x) (app f x).
Proof.
  unfold eta_expand.
  replace (app f x) with (subst (app (shift f) (var fzero)) x) by syntax_simp.
  apply step_beta.
Qed.

(** The reduction statement is uniform over raw arguments. Typing of those
    arguments is imposed separately below, not hidden in the domain. *)
Theorem pointwise_recovery n (f x : Term nat n) :
  reduces_to nat n (app (app direct f) x) (app f x) /\
  reduces_to nat n (app (app expanded f) x) (app f x).
Proof.
  split.
  - apply rtc_in, step_app_left, direct_apply.
  - eapply rtc_step with (y := app (eta_expand f) x).
    + apply step_app_left, expanded_apply.
    + apply rtc_in, eta_apply.
Qed.

Theorem pointwise_typed n (G : Ctx nat n) f x :
  @typ nat RankSorts n G f function_type ->
  @typ nat RankSorts n G x (𝓤 0) ->
  @typ nat RankSorts n G (app (app direct f) x) (𝓤 0) /\
  @typ nat RankSorts n G (app (app expanded f) x) (𝓤 0) /\
  def_equiv nat n (app (app direct f) x) (app (app expanded f) x).
Proof.
  intros Hf Hx. split.
  - eapply BP.arr_apply with (A := 𝓤 0); [| exact Hx].
    eapply BP.arr_apply; [apply direct_typing | exact Hf].
  - split.
    + eapply BP.arr_apply with (A := 𝓤 0); [| exact Hx].
      eapply BP.arr_apply; [apply expanded_typing | exact Hf].
    + apply def_equiv_prop; exists (app f x). apply pointwise_recovery.
Qed.

(** In the valid original context f:D, K:D->U0, K f and K(eta f)
    are actual source TYPES. Pointwise agreement of f and eta f therefore
    cannot be silently substituted for beta equality in dependent indices. *)
Definition dependent_context : Ctx nat 2 :=
  (ε & function_type) & BP.arr function_type (𝓤 0).
Definition direct_index : Term nat 2 :=
  app (var fzero) (var (fsucc fzero)).
Definition expanded_index : Term nat 2 :=
  app (var fzero) (eta_expand (var (fsucc fzero))).

Theorem dependent_context_wf : @wf nat RankSorts 2 dependent_context.
Proof.
  unfold dependent_context. apply wf_cons with (ℓ := 2).
  - apply wf_cons with (ℓ := 1); [constructor | apply function_type_sort].
  - apply BP.arr_sort with (a := 1) (b := 0).
    + apply function_type_sort.
    + constructor; reflexivity.
Qed.

Theorem dependent_indices_typed :
  @typ nat RankSorts 2 dependent_context direct_index (𝓤 0) /\
  @typ nat RankSorts 2 dependent_context expanded_index (𝓤 0).
Proof.
  assert (Hf : @typ nat RankSorts 2 dependent_context
    (var (fsucc fzero)) function_type).
  { change (typ dependent_context (var (fsucc fzero))
      (dependent_context !! fsucc fzero)); constructor. }
  assert (HK : @typ nat RankSorts 2 dependent_context
    (var fzero) (BP.arr function_type (𝓤 0))).
  { change (typ dependent_context (var fzero)
      (dependent_context !! fzero)); constructor. }
  split; unfold direct_index, expanded_index;
    eapply BP.arr_apply; [exact HK | exact Hf | exact HK |].
  apply eta_expand_typing; exact Hf.
Qed.

Theorem dependent_indices_normal_distinct :
  normalb direct_index = true /\ normalb expanded_index = true /\
  direct_index <> expanded_index.
Proof. split; [reflexivity |]. split; [reflexivity | discriminate]. Qed.

Theorem dependent_indices_not_convertible :
  ~ def_equiv nat 2 direct_index expanded_index.
Proof.
  intro H. pose proof (normal_conversion_identity 2 direct_index expanded_index
    eq_refl eq_refl H) as E. discriminate E.
Qed.

Print Assumptions closed_functions_typing.
Print Assumptions closed_functions_normal_distinct.
Print Assumptions closed_functions_not_convertible.
Print Assumptions pointwise_recovery.
Print Assumptions pointwise_typed.
Print Assumptions dependent_context_wf.
Print Assumptions dependent_indices_typed.
Print Assumptions dependent_indices_normal_distinct.
Print Assumptions dependent_indices_not_convertible.

End EtaBoundary.
