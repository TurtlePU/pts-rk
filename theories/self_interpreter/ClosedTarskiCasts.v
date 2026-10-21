From Stdlib Require Import Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation
  Ranks DefEq Reduction AbstractRewriting Congruence.
From PTSrk.NormalizationComplexity Require Import Greedy.
From PTSrk.SelfInterpreter Require Import BrownPalsberg IndexedEquality TarskiCasts.
Import Context.

Module ClosedTarskiCasts.
Module BP := BrownPalsberg.BrownPalsberg.
Module IE := IndexedEquality.IndexedEquality.
Module TC := TarskiCasts.TarskiCasts.

(** Close the already proved local type casts over their three actual
    object parameters. The boolean only selects a direction externally;
    the resulting programs are ORIGINAL closed annotated PTS terms.
    This constructs local transport programs, not a dependent interpreter. *)
Definition result_type (reverse : bool) {n} (S T : Term nat n) :=
  if reverse then BP.arr T S else BP.arr S T.
Definition cast_body (reverse : bool) c {n} (S e : Term nat n) :=
  if reverse then TC.backward c S e else TC.forward c S e.

Definition program_type reverse c {n} : Term nat n :=
  Π (𝓤 c) (Π (𝓤 c)
    (BP.arr (TC.type_law c (var (fsucc fzero)) (var fzero))
      (result_type reverse (var (fsucc fzero)) (var fzero)))).
Definition program reverse c {n} : Term nat n :=
  lam (𝓤 c) (lam (𝓤 c)
    (lam (TC.type_law c (var (fsucc fzero)) (var fzero))
      (cast_body reverse c (var (fsucc (fsucc fzero))) (var fzero)))).

Definition forward c {n} : Term nat n := program false c.
Definition backward c {n} : Term nat n := program true c.
Definition forward_type c {n} : Term nat n := program_type false c.
Definition backward_type c {n} : Term nat n := program_type true c.

Lemma result_type_sort reverse c n (G : Ctx nat n) S T :
  @typ nat RankSorts n G S (𝓤 c) ->
  @typ nat RankSorts n G T (𝓤 c) ->
  @typ nat RankSorts n G (result_type reverse S T) (𝓤 (Datatypes.S c)).
Proof.
  intros HS HT. replace (Datatypes.S c) with (Nat.max (Datatypes.S c) c) by lia.
  destruct reverse; unfold result_type; apply BP.arr_sort; assumption.
Qed.

Lemma program_type_sort reverse c n (G : Ctx nat n) :
  @typ nat RankSorts n G (program_type reverse c) (𝓤 (c+3)).
Proof.
  assert (HS : @typ nat RankSorts (S (S n)) ((G & 𝓤 c) & 𝓤 c)
      (var (fsucc fzero)) (𝓤 c)).
  { change (typ ((G & 𝓤 c) & 𝓤 c) (var (fsucc fzero))
      (((G & 𝓤 c) & 𝓤 c) !! fsucc fzero)); constructor. }
  assert (HT : @typ nat RankSorts (S (S n)) ((G & 𝓤 c) & 𝓤 c)
      (var fzero) (𝓤 c)).
  { change (typ ((G & 𝓤 c) & 𝓤 c) (var fzero)
      (((G & 𝓤 c) & 𝓤 c) !! fzero)); constructor. }
  unfold program_type.
  eapply typ_Π with (ℓₜ := 0) (ℓᵤ := c+3).
  - apply typ_𝓤; reflexivity.
  - eapply typ_Π with (ℓₜ := 0) (ℓᵤ := c+3).
    + apply typ_𝓤; reflexivity.
    + replace (c+3) with (Nat.max (S (c+2)) (S c)) by lia.
      apply BP.arr_sort.
      * apply TC.type_law_sort; assumption.
      * apply result_type_sort; assumption.
    + change (c+3 = Nat.max 1 (c+3)); lia.
  - change (c+3 = Nat.max 1 (c+3)); lia.
Qed.

Lemma program_typing reverse c n (G : Ctx nat n) :
  @typ nat RankSorts n G (program reverse c) (program_type reverse c).
Proof.
  set (GT := (G & 𝓤 c) & 𝓤 c).
  set (law := @TC.type_law c (S (S n)) (var (fsucc fzero)) (var fzero)).
  assert (Hlaw : @typ nat RankSorts (S (S n)) GT law (𝓤 (c+2))).
  { apply TC.type_law_sort;
      [change (typ GT (var (fsucc fzero)) (GT !! fsucc fzero)) |
       change (typ GT (var fzero) (GT !! fzero))]; constructor. }
  assert (HS : @typ nat RankSorts (S (S (S n))) (GT & law)
      (var (fsucc (fsucc fzero))) (𝓤 c)).
  { change (typ (GT & law) (var (fsucc (fsucc fzero)))
      ((GT & law) !! fsucc (fsucc fzero))); constructor. }
  assert (HT : @typ nat RankSorts (S (S (S n))) (GT & law)
      (var (fsucc fzero)) (𝓤 c)).
  { change (typ (GT & law) (var (fsucc fzero))
      ((GT & law) !! fsucc fzero)); constructor. }
  assert (He : @typ nat RankSorts (S (S (S n))) (GT & law) (var fzero)
      (TC.type_law c (var (fsucc (fsucc fzero))) (var (fsucc fzero)))).
  { change (typ (GT & law) (var fzero) ((GT & law) !! fzero)); constructor. }
  unfold program, program_type, BP.arr at 1.
  eapply typ_λ with (ℓ := 0); [constructor; reflexivity |].
  eapply typ_λ with (ℓ := 0); [constructor; reflexivity |].
  eapply typ_λ with (ℓ := c+2); [exact Hlaw |].
  destruct (TC.casts_typed c _ (GT & law) _ _ _ HS HT He) as [HF HB].
  destruct reverse; assumption.
Qed.

Theorem closed_casts_typing c :
  @typ nat RankSorts 0 ε (forward c) (forward_type c) /\
  @typ nat RankSorts 0 ε (backward c) (backward_type c).
Proof. split; apply program_typing. Qed.

Theorem closed_cast_types_sort c :
  @typ nat RankSorts 0 ε (forward_type c) (𝓤 (c+3)) /\
  @typ nat RankSorts 0 ε (backward_type c) (𝓤 (c+3)).
Proof. split; apply program_type_sort. Qed.

Theorem closed_casts_normal c :
  normalb (@forward c 0) = true /\ normalb (@backward c 0) = true /\
  normalb (@forward_type c 0) = true /\ normalb (@backward_type c 0) = true.
Proof. repeat split; reflexivity. Qed.

Definition run reverse c {n} (S T e : Term nat n) :=
  app (app (app (program reverse c) S) T) e.

Lemma replace_renaming m n (rho : Fin m -> Fin n) (t : Term nat m) :
  replace (fun i => var (rho i)) t = rename rho t.
Proof.
  pose proof (rename_replace rho (fun i => var i) t) as H.
  rewrite replace_var in H; symmetry; exact H.
Qed.

Theorem program_specializes reverse c n (S T e : Term nat n) :
  reduces_to nat n (run reverse c S T e) (cast_body reverse c S e).
Proof.
  destruct reverse; unfold run, program, cast_body, TC.forward, TC.backward,
    TC.forward_motive, TC.backward_motive, TC.identity, TC.type_law,
    IE.eq_type, IE.motive_type, BP.arr.
  all: eapply rtc_step; [apply step_app_left, step_app_left, step_beta |].
  all: eapply rtc_step; [apply step_app_left, step_beta |].
  all: eapply rtc_step; [apply step_beta |].
  all: syntax_simp; cbn [transpose fin_match eq_rect shift replace rename];
    rewrite ?replace_renaming; reflexivity.
Qed.

(** Original typing of all applications is established independently of
    reduction: recovery is not used as subject expansion. *)
Theorem run_typed reverse c n (G : Ctx nat n) S T e :
  @typ nat RankSorts n G S (𝓤 c) ->
  @typ nat RankSorts n G T (𝓤 c) ->
  @typ nat RankSorts n G e (TC.type_law c S T) ->
  @typ nat RankSorts n G (run reverse c S T e) (result_type reverse S T).
Proof.
  intros HS HT He.
  pose proof (program_typing reverse c n G) as HP.
  unfold program_type in HP. pose proof (typ_app (𝓤 c) HP HS) as Hfirst.
  assert (Efirst : subst (Π (𝓤 c)
      (BP.arr (TC.type_law c (var (fsucc fzero)) (var fzero))
        (result_type reverse (var (fsucc fzero)) (var fzero)))) S =
    Π (𝓤 c) (BP.arr (TC.type_law c (shift S) (var fzero))
      (result_type reverse (shift S) (var fzero)))).
  { destruct reverse; unfold result_type, TC.type_law, IE.eq_type,
      IE.motive_type, BP.arr; syntax_simp; unfold shift; autorewrite with syntax;
      cbn [weak transpose fin_match eq_rect shift replace rename];
      rewrite ?replace_renaming; reflexivity. }
  rewrite Efirst in Hfirst.
  pose proof (typ_app (𝓤 c) Hfirst HT) as Hsecond.
  assert (Esecond : subst
      (BP.arr (TC.type_law c (shift S) (var fzero))
        (result_type reverse (shift S) (var fzero))) T =
      BP.arr (TC.type_law c S T) (result_type reverse S T)).
  { destruct reverse; unfold result_type, TC.type_law, IE.eq_type,
      IE.motive_type, BP.arr; syntax_simp; unfold shift; autorewrite with syntax;
      cbn [weak transpose fin_match eq_rect shift replace rename];
      rewrite ?replace_renaming; reflexivity. }
  rewrite Esecond in Hsecond.
  unfold run. eapply BP.arr_apply; [exact Hsecond | exact He].
Qed.

Theorem closed_casts_reflexivity c n (S t : Term nat n) :
  reduces_to nat n
    (app (run false c S S (IE.refl_case (Datatypes.S c) (𝓤 c) S)) t) t /\
  reduces_to nat n
    (app (run true c S S (IE.refl_case (Datatypes.S c) (𝓤 c) S)) t) t.
Proof.
  destruct (TC.cast_application_reflexivity c n S S t) as [HF HB].
  split; eapply rtc_trans.
  - apply (@app_cong_par nat (reduces_to nat) _ _ n);
      [apply (program_specializes false) | reflexivity].
  - exact HF.
  - apply (@app_cong_par nat (reduces_to nat) _ _ n);
      [apply (program_specializes true) | reflexivity].
  - exact HB.
Qed.

Print Assumptions closed_casts_typing.
Print Assumptions closed_cast_types_sort.
Print Assumptions closed_casts_normal.
Print Assumptions program_specializes.
Print Assumptions run_typed.
Print Assumptions closed_casts_reflexivity.
End ClosedTarskiCasts.
