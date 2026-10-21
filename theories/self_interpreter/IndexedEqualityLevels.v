From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation
  Ranks Reduction AbstractRewriting DefEq Congruence.
From PTSrk.NormalizationComplexity Require Import Greedy.
From PTSrk.SelfInterpreter Require Import BrownPalsberg IndexedEquality
  IndexedCoherence TypedHOASFaithful.
Import Context.

(** Predicative change of equality level, using actual ORIGINAL PTS terms.
    No cumulativity or same-level symmetry is assumed. These programs act
    on supplied internal evidence, not on metalevel source conversions. *)
Module IndexedEqualityLevels.
Module BP := BrownPalsberg.BrownPalsberg.
Module IE := IndexedEquality.IndexedEquality.
Module IC := IndexedCoherence.IndexedCoherence.
Module TF := TypedHOASFaithful.TypedHOASFaithful.

Definition high a d := Nat.max (a+2) (d+1).
Definition lower_motive d {n} (A u : Term nat n) :=
  lam A (IE.eq_type d (shift A) (shift u) (var fzero)).
Definition reverse_motive d {n} (A u : Term nat n) :=
  lam A (IE.eq_type d (shift A) (var fzero) (shift u)).
Definition lower d {n} (A u e : Term nat n) :=
  IE.transport e (lower_motive d A u) (IE.refl_case d A u).
Definition reverse d {n} (A u e : Term nat n) :=
  IE.transport e (reverse_motive d A u) (IE.refl_case d A u).

Lemma motives_typed a d n (G : Ctx nat n) A u :
  @typ nat RankSorts n G A (𝓤 a) -> @typ nat RankSorts n G u A ->
  @typ nat RankSorts n G (lower_motive d A u) (IE.motive_type (high a d) A) /\
  @typ nat RankSorts n G (reverse_motive d A u) (IE.motive_type (high a d) A).
Proof.
  intros HA Hu.
  assert (HS : typ (G & A) (shift A) (𝓤 a)).
  { change (typ (G & A) (shift A) (shift (𝓤 a))); apply weakening; exact HA. }
  assert (HU : typ (G & A) (shift u) (shift A)) by (apply weakening; exact Hu).
  assert (HX : typ (G & A) (var fzero) (shift A)).
  { change (typ (G & A) (var fzero) ((G & A) !! fzero)); constructor. }
  unfold lower_motive, reverse_motive, IE.motive_type, BP.arr, high.
  split; eapply typ_λ with (ℓ := a); [exact HA | | exact HA |];
    apply IE.eq_type_sort with (a := a); assumption.
Qed.

Lemma lower_motive_beta d n (A u v : Term nat n) :
  step nat n (app (lower_motive d A u) v) (IE.eq_type d A u v).
Proof.
  unfold lower_motive; replace (IE.eq_type d A u v) with
    (subst (IE.eq_type d (shift A) (shift u) (var fzero)) v).
  - apply step_beta.
  - unfold subst; rewrite IE.eq_type_replace; syntax_simp.
Qed.

Lemma reverse_motive_beta d n (A u v : Term nat n) :
  step nat n (app (reverse_motive d A u) v) (IE.eq_type d A v u).
Proof.
  unfold reverse_motive; replace (IE.eq_type d A v u) with
    (subst (IE.eq_type d (shift A) (var fzero) (shift u)) v).
  - apply step_beta.
  - unfold subst; rewrite IE.eq_type_replace; syntax_simp.
Qed.

Theorem lower_typed a d n (G : Ctx nat n) A u v e :
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G u A -> @typ nat RankSorts n G v A ->
  @typ nat RankSorts n G e (IE.eq_type (high a d) A u v) ->
  @typ nat RankSorts n G (lower d A u e) (IE.eq_type d A u v).
Proof.
  intros HA Hu Hv He; destruct (motives_typed a d n G A u HA Hu) as [HM _].
  eapply typ_conv with (T := app (lower_motive d A u) v) (ℓ := high a d).
  - unfold lower; eapply IE.transport_typed; [exact He | exact HM |].
    eapply typ_conv with (T := IE.eq_type d A u u) (ℓ := high a d).
    + apply IE.refl_case_typed with (a := a); assumption.
    + eapply BP.arr_apply; [exact HM | exact Hu].
    + apply def_equiv_prop; exists (IE.eq_type d A u u); split;
        [reflexivity | apply rtc_in, lower_motive_beta].
  - apply IE.eq_type_sort with (a := a); assumption.
  - apply def_equiv_prop; exists (IE.eq_type d A u v); split;
      [apply rtc_in, lower_motive_beta | reflexivity].
Qed.

Theorem reverse_typed a d n (G : Ctx nat n) A u v e :
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G u A -> @typ nat RankSorts n G v A ->
  @typ nat RankSorts n G e (IE.eq_type (high a d) A u v) ->
  @typ nat RankSorts n G (reverse d A u e) (IE.eq_type d A v u).
Proof.
  intros HA Hu Hv He; destruct (motives_typed a d n G A u HA Hu) as [_ HM].
  eapply typ_conv with (T := app (reverse_motive d A u) v) (ℓ := high a d).
  - unfold reverse; eapply IE.transport_typed; [exact He | exact HM |].
    eapply typ_conv with (T := IE.eq_type d A u u) (ℓ := high a d).
    + apply IE.refl_case_typed with (a := a); assumption.
    + eapply BP.arr_apply; [exact HM | exact Hu].
    + apply def_equiv_prop; exists (IE.eq_type d A u u); split;
        [reflexivity | apply rtc_in, reverse_motive_beta].
  - apply IE.eq_type_sort with (a := a); assumption.
  - apply def_equiv_prop; exists (IE.eq_type d A v u); split;
      [apply rtc_in, reverse_motive_beta | reflexivity].
Qed.

Definition join d {n} (A u v e f : Term nat n) :=
  IC.compose d A u (lower d A u e) (reverse d A v f).

Theorem join_typed a d n (G : Ctx nat n) A u v w e f :
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G u A -> @typ nat RankSorts n G v A ->
  @typ nat RankSorts n G w A ->
  @typ nat RankSorts n G e (IE.eq_type (high a d) A u w) ->
  @typ nat RankSorts n G f (IE.eq_type (high a d) A v w) ->
  @typ nat RankSorts n G (join d A u v e f) (IE.eq_type d A u v).
Proof.
  intros HA Hu Hv Hw He Hf; unfold join.
  eapply IC.compose_typed with (a := a) (v := w); try eassumption.
  - eapply lower_typed; eassumption.
  - eapply reverse_typed; eassumption.
Qed.

Theorem lower_replace d m n (sigma : Fin m -> Term nat n) A u e :
  replace sigma (lower d A u e) =
  lower d (replace sigma A) (replace sigma u) (replace sigma e).
Proof.
  unfold lower, lower_motive, IE.transport, IE.refl_case, IE.eq_type, IE.motive_type, BP.arr;
    syntax_simp.
Qed.

Theorem reverse_replace d m n (sigma : Fin m -> Term nat n) A u e :
  replace sigma (reverse d A u e) =
  reverse d (replace sigma A) (replace sigma u) (replace sigma e).
Proof.
  unfold reverse, reverse_motive, IE.transport, IE.refl_case, IE.eq_type, IE.motive_type, BP.arr;
    syntax_simp.
Qed.

Theorem join_replace d m n (sigma : Fin m -> Term nat n) A u v e f :
  replace sigma (join d A u v e f) =
  join d (replace sigma A) (replace sigma u) (replace sigma v)
    (replace sigma e) (replace sigma f).
Proof. unfold join; rewrite IC.compose_replace, lower_replace, reverse_replace; reflexivity. Qed.

Theorem lower_reflexivity h d n (A u : Term nat n) :
  reduces_to nat n (lower d A u (IE.refl_case h A u)) (IE.refl_case d A u).
Proof. apply IE.transport_refl. Qed.

Theorem reverse_reflexivity h d n (A u : Term nat n) :
  reduces_to nat n (reverse d A u (IE.refl_case h A u)) (IE.refl_case d A u).
Proof. apply IE.transport_refl. Qed.

Lemma compose_reduces d n (A u e e' f f' : Term nat n) :
  reduces_to nat n e e' -> reduces_to nat n f f' ->
  reduces_to nat n (IC.compose d A u e f) (IC.compose d A u e' f').
Proof.
  intros He Hf; unfold IC.compose, IE.transport.
  apply (@λ_cong_par nat (reduces_to nat) _ _ n); [reflexivity |].
  apply (@λ_cong_par nat (reduces_to nat) _ _ (S n)); [reflexivity |].
  apply (@app_cong_par nat (reduces_to nat) _ _ (S (S n))).
  - apply (@app_cong_par nat (reduces_to nat) _ _ (S (S n))); [| reflexivity].
    apply rename_rtc, rename_rtc; exact Hf.
  - apply (@app_cong_par nat (reduces_to nat) _ _ (S (S n))); [| reflexivity].
    apply (@app_cong_par nat (reduces_to nat) _ _ (S (S n))); [| reflexivity].
    apply rename_rtc, rename_rtc; exact He.
Qed.

Theorem join_reflexivity h d n (A u : Term nat n) :
  reduces_to nat n
    (join d A u u (IE.refl_case h A u) (IE.refl_case h A u)) (IE.refl_case d A u).
Proof.
  unfold join; eapply rtc_trans; [apply compose_reduces;
    [apply lower_reflexivity | apply reverse_reflexivity] | apply IC.compose_reflexivity].
Qed.

Lemma high_strict a d : d < high a d.
Proof. unfold high; lia. Qed.

(** A law between TYPES at U_c needs predicate c+2 as input to return
    reversed evidence at predicate c+1, the level used by the actual casts. *)
Theorem reverse_type_law_typed c n (G : Ctx nat n) X Y e :
  @typ nat RankSorts n G X (𝓤 c) -> @typ nat RankSorts n G Y (𝓤 c) ->
  @typ nat RankSorts n G e (IE.eq_type (c+2) (𝓤 c) X Y) ->
  @typ nat RankSorts n G (reverse (S c) (𝓤 c) X e)
    (IE.eq_type (S c) (𝓤 c) Y X).
Proof.
  intros HX HY He; apply reverse_typed with (a := 0); try assumption.
  - constructor; reflexivity.
  - replace (high 0 (S c)) with (c+2) by (unfold high; lia); exact He.
Qed.

Lemma motives_normal d n (A u : Term nat n) :
  normalb A = true -> normalb u = true ->
  normalb (lower_motive d A u) = true /\ normalb (reverse_motive d A u) = true.
Proof.
  intros HA Hu; unfold lower_motive, reverse_motive, IE.eq_type, IE.motive_type, BP.arr, shift.
  repeat progress (cbn [normalb isLambda]; rewrite ?TF.normalb_rename).
  rewrite HA, Hu; split; reflexivity.
Qed.

Theorem lower_normal d n (A u e : Term nat n) :
  normalb A = true -> normalb u = true -> normalb e = true -> isLambda e = false ->
  normalb (lower d A u e) = true.
Proof.
  intros HA Hu He HN; destruct (motives_normal d n A u HA Hu) as [HM _].
  pose proof (IE.refl_case_normal d n A u HA Hu) as HR.
  unfold lower, IE.transport; cbn [normalb isLambda]; rewrite He, HN, HM, HR; reflexivity.
Qed.

Theorem reverse_normal d n (A u e : Term nat n) :
  normalb A = true -> normalb u = true -> normalb e = true -> isLambda e = false ->
  normalb (reverse d A u e) = true.
Proof.
  intros HA Hu He HN; destruct (motives_normal d n A u HA Hu) as [_ HM].
  pose proof (IE.refl_case_normal d n A u HA Hu) as HR.
  unfold reverse, IE.transport; cbn [normalb isLambda]; rewrite He, HN, HM, HR; reflexivity.
Qed.

Lemma compose_normal d n (A u e f : Term nat n) :
  normalb A = true -> normalb u = true -> normalb e = true -> normalb f = true ->
  isLambda e = false -> isLambda f = false -> normalb (IC.compose d A u e f) = true.
Proof.
  intros HA Hu He Hf NE NF; unfold IC.compose, IE.motive_type, BP.arr, IE.transport, shift.
  repeat progress (cbn [normalb isLambda]; rewrite ?TF.normalb_rename, ?TF.isLambda_rename).
  rewrite HA, Hu, He, Hf, NE, NF; reflexivity.
Qed.

Theorem join_normal d n (A u v e f : Term nat n) :
  normalb A = true -> normalb u = true -> normalb v = true ->
  normalb e = true -> normalb f = true -> isLambda e = false -> isLambda f = false ->
  normalb (join d A u v e f) = true.
Proof.
  intros HA Hu Hv He Hf NE NF; unfold join; apply compose_normal; try assumption;
    try reflexivity; [apply lower_normal | apply reverse_normal]; assumption.
Qed.

Print Assumptions motives_typed.
Print Assumptions lower_typed.
Print Assumptions reverse_typed.
Print Assumptions join_typed.
Print Assumptions lower_replace.
Print Assumptions reverse_replace.
Print Assumptions join_replace.
Print Assumptions lower_reflexivity.
Print Assumptions reverse_reflexivity.
Print Assumptions join_reflexivity.
Print Assumptions reverse_type_law_typed.
Print Assumptions high_strict.
Print Assumptions lower_normal.
Print Assumptions reverse_normal.
Print Assumptions join_normal.
End IndexedEqualityLevels.
