From Stdlib Require Import Bool.Bool.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks.
From PTSrk.NormalizationComplexity Require Import Greedy Morphisms.
From PTSrk.SelfInterpreter Require Import UniformTelescope.
Import Context.

(** Substitution by normal, non-lambda terms creates NO beta redex.
    This is an exact structural fact about the ORIGINAL annotated syntax,
    not hereditary substitution or external normalization. *)
Module NormalNeutralSubstitution.
Module UT := UniformTelescope.UniformTelescope.

Definition neutral_sub {m n} (sigma : Fin m -> Term nat n) : Prop :=
  forall i, isLambda (sigma i) = false.
Definition normal_sub {m n} (sigma : Fin m -> Term nat n) : Prop :=
  forall i, normalb (sigma i) = true.

Lemma transpose_neutral m n (sigma : Fin m -> Term nat n) :
  neutral_sub sigma -> neutral_sub (transpose sigma).
Proof.
  intros H i; dependent elimination i as [fzero | fsucc i];
    cbn [transpose fin_match]; [reflexivity |].
  unfold shift; rewrite UT.isLambda_rename; exact (H i).
Qed.

Lemma transpose_normal m n (sigma : Fin m -> Term nat n) :
  normal_sub sigma -> normal_sub (transpose sigma).
Proof.
  intros H i; dependent elimination i as [fzero | fsucc i];
    cbn [transpose fin_match]; [reflexivity |].
  unfold shift; rewrite UT.normalb_rename; exact (H i).
Qed.

Theorem isLambda_replace m (t : Term nat m) n (sigma : Fin m -> Term nat n) :
  neutral_sub sigma -> isLambda (replace sigma t) = isLambda t.
Proof. intro H; destruct t; cbn [replace isLambda]; try reflexivity; apply H. Qed.

Theorem normalb_replace m (t : Term nat m) : forall n (sigma : Fin m -> Term nat n),
  normal_sub sigma -> neutral_sub sigma ->
  normalb (replace sigma t) = normalb t.
Proof.
  induction t; intros k sigma HN HL; cbn [replace normalb].
  - reflexivity.
  - rewrite IHt1, IHt2; try assumption;
      [reflexivity | apply transpose_normal | apply transpose_neutral]; assumption.
  - apply HN.
  - rewrite IHt1, IHt2; try assumption;
      [reflexivity | apply transpose_normal | apply transpose_neutral]; assumption.
  - rewrite IHt1, IHt2, isLambda_replace; try assumption; reflexivity.
Qed.

Theorem replacement_normal m n (sigma : Fin m -> Term nat n) t :
  normal_sub sigma -> neutral_sub sigma -> normalb t = true ->
  normalb (replace sigma t) = true.
Proof. intros HN HL HT; rewrite normalb_replace; assumption. Qed.

Theorem replacement_neutral m n (sigma : Fin m -> Term nat n) t :
  neutral_sub sigma -> isLambda t = false -> isLambda (replace sigma t) = false.
Proof. intros HS HT; rewrite isLambda_replace; assumption. Qed.

Theorem composition_normal m n p (sigma : Fin m -> Term nat n)
    (tau : Fin n -> Term nat p) :
  normal_sub sigma -> normal_sub tau -> neutral_sub tau ->
  normal_sub (fun i => replace tau (sigma i)).
Proof. intros HS HT HN i; apply replacement_normal; auto. Qed.

Theorem composition_neutral m n p (sigma : Fin m -> Term nat n)
    (tau : Fin n -> Term nat p) :
  neutral_sub sigma -> neutral_sub tau ->
  neutral_sub (fun i => replace tau (sigma i)).
Proof. intros HS HT i; apply replacement_neutral; auto. Qed.

(** Original typing is independently transported by TypedSub. Normality is
    a consequence of normal inputs and neutral replacement, never a premise
    on the desired substituted output. No well-formedness restriction is
    introduced beyond the ORIGINAL typing/substitution judgments. *)
Theorem typed_normal_replacement m n (G : Ctx nat m) (H : Ctx nat n)
    (sigma : Fin m -> Term nat n) t T :
  TypedSub G H sigma -> @typ nat RankSorts m G t T ->
  normal_sub sigma -> neutral_sub sigma -> normalb t = true ->
  @typ nat RankSorts n H (replace sigma t) (replace sigma T) /\
    normalb (replace sigma t) = true.
Proof.
  intros HS Ht HN HL HtN; split.
  - exact (typing_replace _ _ _ Ht _ _ _ HS).
  - apply replacement_normal; assumption.
Qed.

Theorem substitution_normal n (t : Term nat (S n)) (u : Term nat n) :
  normalb u = true -> isLambda u = false ->
  normalb (subst t u) = normalb t.
Proof.
  intros HN HL; unfold subst; apply normalb_replace;
    intro i; dependent elimination i as [fzero | fsucc i]; cbn [fin_match];
    assumption || reflexivity.
Qed.

Print Assumptions transpose_neutral.
Print Assumptions transpose_normal.
Print Assumptions isLambda_replace.
Print Assumptions normalb_replace.
Print Assumptions replacement_normal.
Print Assumptions replacement_neutral.
Print Assumptions composition_normal.
Print Assumptions composition_neutral.
Print Assumptions typed_normal_replacement.
Print Assumptions substitution_normal.
End NormalNeutralSubstitution.
