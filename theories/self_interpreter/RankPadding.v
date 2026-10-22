From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting Congruence.
From PTSrk.NormalizationComplexity Require Import Morphisms Greedy.
From PTSrk.SelfInterpreter Require Import RankObstruction BrownPalsberg
  NormalNeutralSubstitution UniformTelescope.
Import Context.

(** Exact-rank padding in the ORIGINAL non-cumulative PTS.  A common upper
    bound on formation ranks is converted to one actual formation rank by
    adding a harmless argument of an independently inhabited type.  Neither
    the supplied program nor its result is normalized. *)
Module RankPadding.

Lemma rank_type_rename j : forall m n (rho : Fin m -> Fin n),
  rename rho (@rank_type j m) = @rank_type j n.
Proof. induction j; intros; cbn [rank_type rename]; f_equal; auto. Qed.
Lemma rank_value_rename j m n (rho : Fin m -> Fin n) :
  rename rho (@rank_value j m) = @rank_value j n.
Proof. destruct j; cbn [rank_value rename]; f_equal; apply rank_type_rename. Qed.
Lemma rank_type_replace j : forall m n (sigma : Fin m -> Term nat n),
  replace sigma (@rank_type j m) = @rank_type j n.
Proof. induction j; intros; cbn [rank_type replace]; f_equal; auto. Qed.
Lemma rank_value_replace j m n (sigma : Fin m -> Term nat n) :
  replace sigma (@rank_value j m) = @rank_value j n.
Proof. destruct j; cbn [rank_value replace]; f_equal; apply rank_type_replace. Qed.
Lemma rank_type_normal j n : normalb (@rank_type j n) = true.
Proof.
  revert n; induction j; intro n; cbn [rank_type normalb];
    [reflexivity | rewrite IHj; reflexivity].
Qed.
Lemma rank_value_normal j n : normalb (@rank_value j n) = true.
Proof.
  destruct j; cbn [rank_value normalb];
    [reflexivity | rewrite rank_type_normal; reflexivity].
Qed.

Definition padded_type j {n} (A : Term nat n) :=
  BrownPalsberg.BrownPalsberg.arr (rank_type j) A.
Definition embed j {n} (q : Term nat n) := lam (rank_type j) (shift q).
Definition force j {n} (q : Term nat n) := app q (rank_value j).

Lemma embed_replace j m n (sigma : Fin m -> Term nat n) q :
  replace sigma (embed j q) = embed j (replace sigma q).
Proof.
  unfold embed; cbn [replace]; rewrite rank_type_replace, replace_lift_shift;
    reflexivity.
Qed.
Lemma force_replace j m n (sigma : Fin m -> Term nat n) q :
  replace sigma (force j q) = force j (replace sigma q).
Proof. unfold force; cbn [replace]; rewrite rank_value_replace; reflexivity. Qed.

Theorem padded_type_sort j n (G : Ctx nat n) A a :
  @typ nat RankSorts n G A (𝓤 a) -> a <= S j ->
  @typ nat RankSorts n G (padded_type j A) (𝓤 (S j)).
Proof.
  intros HA Ha; unfold padded_type.
  replace (S j) with (Nat.max (S j) a) by lia.
  apply BrownPalsberg.BrownPalsberg.arr_sort; [apply rank_type_sort | exact HA].
Qed.
Theorem embed_typed j n (G : Ctx nat n) q A :
  @typ nat RankSorts n G q A ->
  @typ nat RankSorts n G (embed j q) (padded_type j A).
Proof.
  intro Hq; unfold embed, padded_type, BrownPalsberg.BrownPalsberg.arr.
  eapply typ_λ with (ℓ := j); [apply rank_type_sort | apply weakening; exact Hq].
Qed.
Theorem force_typed j n (G : Ctx nat n) q A :
  @typ nat RankSorts n G q (padded_type j A) ->
  @typ nat RankSorts n G (force j q) A.
Proof.
  intro Hq; unfold force; eapply BrownPalsberg.BrownPalsberg.arr_apply;
    [exact Hq | apply rank_value_typing].
Qed.
Theorem force_embed j n (q : Term nat n) :
  reduces_to nat n (force j (embed j q)) q.
Proof.
  unfold force, embed; replace q with (subst (shift q) (rank_value j)) at 2
    by syntax_simp; apply rtc_in, step_beta.
Qed.
Theorem padded_type_normal j n (A : Term nat n) :
  normalb A = true -> normalb (padded_type j A) = true.
Proof.
  intro HA; unfold padded_type, BrownPalsberg.BrownPalsberg.arr, shift;
    cbn [normalb]; rewrite rank_type_normal,
      UniformTelescope.UniformTelescope.normalb_rename, HA; reflexivity.
Qed.
Theorem embed_normal j n (q : Term nat n) :
  normalb q = true -> normalb (embed j q) = true.
Proof.
  intro Hq; unfold embed, shift; cbn [normalb]; rewrite rank_type_normal,
    UniformTelescope.UniformTelescope.normalb_rename, Hq; reflexivity.
Qed.
Theorem embed_injective j n (q u : Term nat n) :
  embed j q = embed j u -> q = u.
Proof.
  intro H; unfold embed in H; injection H as H.
  apply (f_equal (fun t => subst t (𝓤 0))) in H.
  unfold subst, shift in H; autorewrite with syntax in H; exact H.
Qed.

Definition runner_sub j {n} : Fin (S n) -> Term nat (S n) :=
  fin_match (force j (var fzero)) (fun i => var (fsucc i)).
Definition runner j {n} (A : Term nat n) (b : Term nat (S n)) :=
  lam (padded_type j A) (replace (runner_sub j) b).

Lemma runner_sub_shift j n (t : Term nat n) :
  replace (runner_sub j) (shift t) = shift t.
Proof.
  unfold shift; rewrite replace_rename; change
    (replace (fun i => var (fsucc i)) t = rename fsucc t).
  apply replace_as_rename.
Qed.
Lemma padded_type_rename j m n (rho : Fin m -> Fin n) A :
  rename rho (padded_type j A) = padded_type j (rename rho A).
Proof.
  unfold padded_type, BrownPalsberg.BrownPalsberg.arr;
    cbn [rename]; rewrite rank_type_rename; f_equal; syntax_simp.
Qed.
Lemma runner_sub_typed j n (G : Ctx nat n) A :
  TypedSub (G & A) (G & padded_type j A) (runner_sub j).
Proof.
  intro i; dependent elimination i as [fzero | fsucc i];
    cbn [index ctx_top ctx_pred]; rewrite runner_sub_shift.
  - change (typ (G & padded_type j A) (force j (var fzero)) (shift A)).
    apply force_typed.
    unfold shift; rewrite <- padded_type_rename.
    change (typ (G & padded_type j A) (var fzero)
      ((G & padded_type j A) !! fzero)); constructor.
  - change (typ (G & padded_type j A) (var (fsucc i)) (shift (G !! i))).
    constructor.
Qed.
Theorem runner_typed j n (G : Ctx nat n) A T b a :
  @typ nat RankSorts n G A (𝓤 a) -> a <= S j ->
  @typ nat RankSorts (S n) (G & A) b (shift T) ->
  @typ nat RankSorts n G (runner j A b)
    (BrownPalsberg.BrownPalsberg.arr (padded_type j A) T).
Proof.
  intros HA Ha Hb; unfold runner, BrownPalsberg.BrownPalsberg.arr.
  eapply typ_λ with (ℓ := S j); [eapply padded_type_sort; eassumption |].
  rewrite <- (runner_sub_shift j n T).
  apply typing_replace with (G := G & A); [exact Hb | apply runner_sub_typed].
Qed.
Lemma runner_sub_normal j n :
  NormalNeutralSubstitution.NormalNeutralSubstitution.normal_sub (@runner_sub j n).
Proof.
  intro i; dependent elimination i as [fzero | fsucc i];
    cbn [runner_sub fin_match force normalb isLambda];
    [rewrite rank_value_normal |]; reflexivity.
Qed.
Lemma runner_sub_neutral j n :
  NormalNeutralSubstitution.NormalNeutralSubstitution.neutral_sub (@runner_sub j n).
Proof.
  intro i; dependent elimination i as [fzero | fsucc i]; reflexivity.
Qed.
Theorem runner_normal j n (A : Term nat n) b :
  normalb A = true -> normalb b = true -> normalb (runner j A b) = true.
Proof.
  intros HA Hb; unfold runner; cbn [normalb].
  rewrite padded_type_normal by exact HA.
  rewrite NormalNeutralSubstitution.NormalNeutralSubstitution.normalb_replace;
    [exact Hb | apply runner_sub_normal | apply runner_sub_neutral].
Qed.
Theorem runner_embed j n (A q : Term nat n) b :
  reduces_to nat n (app (runner j A b) (embed j q)) (subst b q).
Proof.
  unfold runner; eapply rtc_step; [apply step_beta |].
  unfold subst; rewrite replace_replace; apply rtc_replace; intro i.
  dependent elimination i as [fzero | fsucc i];
    cbn [runner_sub fin_match force replace].
  - rewrite rank_value_replace; apply force_embed.
  - reflexivity.
Qed.
Theorem runner_recovers j n (A q t : Term nat n) b :
  reduces_to nat n (subst b q) t ->
  reduces_to nat n (app (runner j A b) (embed j q)) t.
Proof. intro H; eapply rtc_trans; [apply runner_embed | exact H]. Qed.

Print Assumptions padded_type_sort.
Print Assumptions embed_typed.
Print Assumptions force_typed.
Print Assumptions force_embed.
Print Assumptions padded_type_normal.
Print Assumptions embed_normal.
Print Assumptions embed_injective.
Print Assumptions runner_sub_typed.
Print Assumptions runner_typed.
Print Assumptions runner_normal.
Print Assumptions runner_embed.
Print Assumptions runner_recovers.
End RankPadding.
