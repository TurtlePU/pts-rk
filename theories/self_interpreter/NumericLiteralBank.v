From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Ranks Reduction
  AbstractRewriting Congruence.
From PTSrk.NormalizationComplexity Require Import Rank Literals Greedy Morphisms.
From PTSrk.SelfInterpreter Require Import ChurchSyntax ChurchSyntaxFold
  BudgetInternalization UniformTelescope.
Import Context RankEstimate ListNotations.

Module NumericLiteralBank.

(** A numeric adapter for a finite literal bank.  The numeral is monomorphic
    Church iteration on a fixed finite-selector state.  All its annotations
    use only U_0; the fixed head itself stores the actual bounded sort literals.
    This is a sort-leaf operation, not internal certificate acceptance. *)

Fixpoint arrows count {n} : Term nat n :=
  match count with 0 => 𝓤 0 | S rest => Π (𝓤 0) (arrows rest) end.

Lemma arrows_rename count m n (rho : Fin m -> Fin n) :
  rename rho (arrows count) = arrows count.
Proof. revert m n rho; induction count; intros; cbn [arrows rename]; congruence. Qed.
Lemma arrows_replace count m n (sigma : Fin m -> Term nat n) :
  replace sigma (arrows count) = arrows count.
Proof. revert m n sigma; induction count; intros; cbn [arrows replace]; congruence. Qed.
Lemma arrows_step count n : @arrows (S count) n =
  ChurchSyntax.ChurchSyntax.arrow (𝓤 0) (arrows count).
Proof. unfold ChurchSyntax.ChurchSyntax.arrow, shift; cbn [arrows]; now rewrite arrows_rename. Qed.
Lemma arrows_sort count : forall n (G : Ctx nat n),
  @typ nat RankSorts n G (arrows count) (𝓤 (Nat.min count 1)).
Proof.
  induction count; intros; cbn [arrows].
  - constructor; reflexivity.
  - replace (Nat.min (S count) 1) with (Nat.max 1 (Nat.min count 1)) by lia.
    eapply typ_Π with (ℓₜ := 0) (ℓᵤ := Nat.min count 1);
      [constructor; reflexivity | apply IHcount | reflexivity].
Qed.
Lemma arrows_normal count n : normalb (@arrows count n) = true.
Proof. revert n; induction count; intros; cbn [arrows normalb]; [reflexivity | apply IHcount]. Qed.
Lemma arrows_literals count n : maxRankLiteral (@arrows count n) = 0.
Proof. revert n; induction count; intros; cbn [arrows maxRankLiteral]; [reflexivity | apply IHcount]. Qed.

Fixpoint constant count {n} (x : Term nat n) :=
  match count with 0 => x | S rest => lam (𝓤 0) (constant rest (shift x)) end.
Fixpoint duplicate count {n} (f : Term nat n) :=
  match count with
  | 0 => lam (𝓤 0) (app (app (shift f) (var fzero)) (var fzero))
  | S rest => lam (𝓤 0) (duplicate rest (app (shift f) (var fzero)))
  end.
Definition zero k {n} : Term nat n := lam (𝓤 0) (constant k (var fzero)).
Definition successor k {n} : Term nat n :=
  match k with
  | 0 => lam (arrows 1) (var fzero)
  | S rest => lam (arrows (S (S rest)))
      (lam (𝓤 0) (duplicate rest (var (fsucc fzero))))
  end.

Lemma constant_replace count : forall m n (sigma : Fin m -> Term nat n) x,
  replace sigma (constant count x) = constant count (replace sigma x).
Proof.
  induction count; intros; cbn [constant replace]; [reflexivity |].
  rewrite IHcount, replace_lift_shift; reflexivity.
Qed.
Lemma duplicate_replace count : forall m n (sigma : Fin m -> Term nat n) f,
  replace sigma (duplicate count f) = duplicate count (replace sigma f).
Proof.
  induction count; intros; cbn [duplicate replace];
    try rewrite IHcount; cbn [replace transpose fin_match];
    rewrite replace_lift_shift; reflexivity.
Qed.
Lemma constant_typed count : forall n (G : Ctx nat n) x,
  @typ nat RankSorts n G x (𝓤 0) ->
  @typ nat RankSorts n G (constant count x) (arrows count).
Proof.
  induction count; intros n G x HX; cbn [constant arrows]; [exact HX |].
  eapply typ_λ with (ℓ := 0); [constructor; reflexivity |].
  apply IHcount. change (typ (G & 𝓤 0) (shift x) (shift (𝓤 0))).
  apply weakening; exact HX.
Qed.
Lemma apply_arrow count n (G : Ctx nat n) f x :
  @typ nat RankSorts n G f (arrows (S count)) ->
  @typ nat RankSorts n G x (𝓤 0) ->
  @typ nat RankSorts n G (app f x) (arrows count).
Proof.
  intros Hf Hx; rewrite arrows_step in Hf.
  eapply ChurchSyntax.ChurchSyntax.arrow_application; eassumption.
Qed.
Lemma duplicate_typed count : forall n (G : Ctx nat n) f,
  @typ nat RankSorts n G f (arrows (S (S count))) ->
  @typ nat RankSorts n G (duplicate count f) (arrows (S count)).
Proof.
  induction count; intros n G f HF; cbn [duplicate arrows].
  - eapply typ_λ with (ℓ := 0); [constructor; reflexivity |].
    eapply (apply_arrow 0); [eapply (apply_arrow 1) |]; try constructor.
    rewrite <- (arrows_rename 2 n (S n) fsucc).
    apply weakening; exact HF.
  - eapply typ_λ with (ℓ := 0); [constructor; reflexivity |].
    apply IHcount, apply_arrow with (x := var fzero).
    + rewrite <- (arrows_rename (S (S (S count))) n (S n) fsucc).
      apply weakening; exact HF.
    + constructor.
Qed.
Theorem zero_typed k n (G : Ctx nat n) :
  @typ nat RankSorts n G (zero k) (arrows (S k)).
Proof.
  unfold zero; cbn [arrows]; eapply typ_λ with (ℓ := 0);
    [constructor; reflexivity | apply constant_typed; constructor].
Qed.
Theorem successor_typed k n (G : Ctx nat n) :
  @typ nat RankSorts n G (successor k)
    (ChurchSyntax.ChurchSyntax.unary (arrows (S k))).
Proof.
  assert (HF : @typ nat RankSorts n G (arrows (S k)) (𝓤 1)).
  { replace 1 with (Nat.min (S k) 1) by lia; apply arrows_sort. }
  unfold ChurchSyntax.ChurchSyntax.unary, ChurchSyntax.ChurchSyntax.arrow.
  unfold shift; rewrite arrows_rename.
  destruct k; cbn [successor]; eapply typ_λ with (ℓ := 1); [exact HF | |exact HF |].
  - change (typ (G & arrows 1) (var fzero) (shift (arrows 1))); constructor.
  - cbn [arrows]; eapply typ_λ with (ℓ := 0); [constructor; reflexivity |].
    apply duplicate_typed.
    replace (@arrows (S (S k)) (S (S n))) with
      (shift (shift (@arrows (S (S k)) n))) by
      (unfold shift; now rewrite !arrows_rename).
    change (typ ((G & arrows (S (S k))) & 𝓤 0) (var (fsucc fzero))
      (shift (shift (arrows (S (S k)))))).
    constructor.
Qed.

Fixpoint duplicate_last {A} (xs : list A) :=
  match xs with [] => [] | [x] => [x;x] | x :: rest => x :: duplicate_last rest end.
Definition advance {A} (xs : list A) :=
  match xs with [] => [] | [x] => [x] | _ :: rest => duplicate_last rest end.

Lemma arguments_reduces n args (f g : Term nat n) :
  reduces_to nat n f g ->
  reduces_to nat n (BudgetInternalization.BudgetInternalization.apply_arguments f args)
    (BudgetInternalization.BudgetInternalization.apply_arguments g args).
Proof.
  revert f g; induction args; intros f g H; cbn [BudgetInternalization.BudgetInternalization.apply_arguments];
    [exact H | apply IHargs, (@app_cong_l nat (reduces_to nat) _ n); exact H].
Qed.

Lemma constant_recovery count : forall n (x : Term nat n) args,
  length args = count ->
  reduces_to nat n
    (BudgetInternalization.BudgetInternalization.apply_arguments (constant count x) args) x.
Proof.
  induction count; intros n x args HL; destruct args; cbn in HL; try discriminate.
  - reflexivity.
  - cbn [constant BudgetInternalization.BudgetInternalization.apply_arguments].
    eapply rtc_trans; [apply arguments_reduces, rtc_in, step_beta |].
    unfold subst; rewrite constant_replace; syntax_simp.
    apply IHcount; lia.
Qed.

Lemma duplicate_recovery count : forall n (f : Term nat n) args,
  length args = S count ->
  reduces_to nat n
    (BudgetInternalization.BudgetInternalization.apply_arguments (duplicate count f) args)
    (BudgetInternalization.BudgetInternalization.apply_arguments f (duplicate_last args)).
Proof.
  induction count; intros n f args HL; destruct args as [|x xs]; cbn in HL; try discriminate.
  - destruct xs; [|discriminate]. cbn [duplicate duplicate_last BudgetInternalization.BudgetInternalization.apply_arguments].
    eapply rtc_step; [apply step_beta |]. unfold subst; syntax_simp; reflexivity.
  - cbn [duplicate BudgetInternalization.BudgetInternalization.apply_arguments].
    eapply rtc_trans; [apply arguments_reduces, rtc_in, step_beta |].
    unfold subst; rewrite duplicate_replace; syntax_simp.
    destruct xs as [|y ys]; cbn in HL; [discriminate |].
    change (reduces_to nat n
      (BudgetInternalization.BudgetInternalization.apply_arguments (duplicate count (app f x)) (y::ys))
      (BudgetInternalization.BudgetInternalization.apply_arguments (app f x) (duplicate_last (y::ys)))).
    apply IHcount; cbn; lia.
Qed.

Lemma zero_recovery k n (args : list (Term nat n)) x :
  length args = k ->
  reduces_to nat n (BudgetInternalization.BudgetInternalization.apply_arguments (zero k) (x::args)) x.
Proof.
  intro HL; cbn [zero BudgetInternalization.BudgetInternalization.apply_arguments].
  eapply rtc_trans; [apply arguments_reduces, rtc_in, step_beta |].
  unfold subst; rewrite constant_replace; cbn [replace fin_match].
  apply constant_recovery; exact HL.
Qed.

Lemma successor_recovery k n (f : Term nat n) args :
  length args = S k ->
  reduces_to nat n
    (BudgetInternalization.BudgetInternalization.apply_arguments (app (successor k) f) args)
    (BudgetInternalization.BudgetInternalization.apply_arguments f (advance args)).
Proof.
  intro HL; destruct k.
  - destruct args as [|x xs]; cbn in HL; [discriminate |].
    destruct xs; [|discriminate].
    apply arguments_reduces, rtc_in, step_beta.
  - cbn [successor]. eapply rtc_trans; [apply arguments_reduces, rtc_in, step_beta |].
    unfold subst; cbn [replace]; rewrite duplicate_replace; cbn [replace transpose fin_match].
    destruct args as [|x xs]; cbn in HL; [discriminate |].
    cbn [BudgetInternalization.BudgetInternalization.apply_arguments].
    eapply rtc_trans; [apply arguments_reduces, rtc_in, step_beta |].
    unfold subst; rewrite duplicate_replace; syntax_simp.
    destruct xs as [|y ys]; cbn in HL; [discriminate |].
    change (reduces_to nat n
      (BudgetInternalization.BudgetInternalization.apply_arguments (duplicate k f) (y::ys))
      (BudgetInternalization.BudgetInternalization.apply_arguments f (duplicate_last (y::ys)))).
    apply duplicate_recovery; cbn; lia.
Qed.

Fixpoint bank count ceiling start {n} : list (Term nat n) :=
  match count with
  | 0 => []
  | S rest => 𝓤 (Nat.min start ceiling) :: bank rest ceiling (S start)
  end.
Lemma bank_length count ceiling start n : length (@bank count ceiling start n) = count.
Proof. revert start; induction count; intros; cbn [bank length]; auto. Qed.
Lemma duplicate_bank count : forall ceiling start n,
  ceiling <= start + count ->
  duplicate_last (@bank (S count) ceiling start n) = bank (S (S count)) ceiling start.
Proof.
  induction count; intros ceiling start n H; cbn [bank duplicate_last].
  - repeat rewrite Nat.min_r by lia; reflexivity.
  - f_equal. apply IHcount; lia.
Qed.
Lemma advance_bank k start n :
  advance (@bank (S k) k start n) = bank (S k) k (S start).
Proof.
  destruct k; [cbn [bank advance]; now rewrite Nat.min_0_r |].
  change (duplicate_last (@bank (S k) (S k) (S start) n) = bank (S (S k)) (S k) (S start)).
  apply duplicate_bank; lia.
Qed.

Theorem iteration_recovery k i : forall n start,
  reduces_to nat n
    (BudgetInternalization.BudgetInternalization.apply_arguments
      (ChurchSyntax.ChurchSyntax.nat_fold (zero k) (successor k) i)
      (bank (S k) k start)) (𝓤 (Nat.min (start+i) k)).
Proof.
  induction i; intros n start; cbn [ChurchSyntax.ChurchSyntax.nat_fold].
  - rewrite Nat.add_0_r. apply zero_recovery, bank_length.
  - eapply rtc_trans; [apply successor_recovery, bank_length |].
    rewrite advance_bank.
    replace (start + S i) with (S start + i) by lia.
    apply IHi.
Qed.

Definition numeral_type k {n} :=
  ChurchSyntax.ChurchSyntax.unary
    (@ChurchSyntax.ChurchSyntax.unary n (arrows (S k))).
Definition numeral k i {n} : Term nat n :=
  lam (ChurchSyntax.ChurchSyntax.unary (arrows (S k)))
    (lam (arrows (S k))
      (ChurchSyntax.ChurchSyntax.nat_fold (var fzero) (var (fsucc fzero)) i)).
Definition head k {n} : Term nat n :=
  lam (numeral_type k)
    (BudgetInternalization.BudgetInternalization.apply_arguments
      (app (app (var fzero) (successor k)) (zero k)) (bank (S k) k 0)).

Lemma numeral_type_sort k n (G : Ctx nat n) :
  @typ nat RankSorts n G (numeral_type k) (𝓤 3).
Proof.
  unfold numeral_type; apply ChurchSyntax.ChurchSyntax.unary_sort,
    ChurchSyntax.ChurchSyntax.unary_sort.
  replace 1 with (Nat.min (S k) 1) by lia; apply arrows_sort.
Qed.
Theorem numeral_typed k i n (G : Ctx nat n) :
  @typ nat RankSorts n G (numeral k i) (numeral_type k).
Proof.
  unfold numeral, numeral_type, ChurchSyntax.ChurchSyntax.unary,
    ChurchSyntax.ChurchSyntax.arrow.
  unfold shift; cbn [rename]; rewrite !arrows_rename.
  eapply typ_λ with (ℓ := 2).
  - eapply typ_Π with (ℓₜ := 1) (ℓᵤ := 1); [| |reflexivity];
      replace 1 with (Nat.min (S k) 1) by lia; apply arrows_sort.
  - eapply typ_λ with (ℓ := 1).
    + replace 1 with (Nat.min (S k) 1) by lia; apply arrows_sort.
    + apply ChurchSyntax.ChurchSyntax.nat_fold_typed.
      * rewrite <- (arrows_rename (S k) (S n) (S (S n)) fsucc); constructor.
      * unfold ChurchSyntax.ChurchSyntax.unary.
        replace (ChurchSyntax.ChurchSyntax.arrow (arrows (S k)) (arrows (S k))) with
          (shift (shift (Π (@arrows (S k) n) (@arrows (S k) (S n))))) by
          (unfold ChurchSyntax.ChurchSyntax.arrow, shift; cbn [rename];
            rewrite !arrows_rename; reflexivity).
        constructor.
Qed.

Lemma arguments_typed n (G : Ctx nat n) args : forall f,
  @typ nat RankSorts n G f (arrows (length args)) ->
  Forall (fun a => @typ nat RankSorts n G a (𝓤 0)) args ->
  @typ nat RankSorts n G
    (BudgetInternalization.BudgetInternalization.apply_arguments f args) (𝓤 0).
Proof.
  induction args; intros f HF HA; cbn [BudgetInternalization.BudgetInternalization.apply_arguments] in *.
  - exact HF.
  - inversion HA; subst. apply IHargs; [apply apply_arrow; assumption | assumption].
Qed.
Lemma bank_typed count ceiling start n (G : Ctx nat n) :
  Forall (fun a => @typ nat RankSorts n G a (𝓤 0)) (bank count ceiling start).
Proof.
  revert start; induction count; intro start; cbn [bank]; constructor;
    [constructor; reflexivity | apply IHcount].
Qed.
Theorem head_typed k n (G : Ctx nat n) :
  @typ nat RankSorts n G (head k)
    (ChurchSyntax.ChurchSyntax.arrow (numeral_type k) (𝓤 0)).
Proof.
  unfold head, ChurchSyntax.ChurchSyntax.arrow at 1.
  eapply typ_λ with (ℓ := 3); [apply numeral_type_sort |].
  apply arguments_typed; [rewrite bank_length | apply bank_typed].
  eapply ChurchSyntax.ChurchSyntax.arrow_application with (X := arrows (S k));
    [|apply zero_typed].
  eapply ChurchSyntax.ChurchSyntax.arrow_application with
    (X := ChurchSyntax.ChurchSyntax.unary (arrows (S k))); [|apply successor_typed].
  change (typ (G & numeral_type k) (var fzero) (numeral_type k)).
  replace (@numeral_type k (S n)) with (shift (@numeral_type k n)) by
    (unfold numeral_type, shift; rewrite !ChurchSyntax.ChurchSyntax.unary_rename, !arrows_rename; reflexivity).
  constructor.
Qed.
Theorem head_type_sort k n (G : Ctx nat n) :
  @typ nat RankSorts n G
    (ChurchSyntax.ChurchSyntax.arrow (numeral_type k) (𝓤 0)) (𝓤 4).
Proof.
  change (typ G (ChurchSyntax.ChurchSyntax.arrow (numeral_type k) (𝓤 0))
    (𝓤 (Nat.max (S 3) 0))).
  apply ChurchSyntax.ChurchSyntax.arrow_sort;
    [apply numeral_type_sort | constructor; reflexivity].
Qed.

Lemma numeral_beta k i n (z s : Term nat n) :
  reduces_to nat n (app (app (numeral k i) s) z)
    (ChurchSyntax.ChurchSyntax.nat_fold z s i).
Proof.
  unfold numeral; eapply rtc_step; [apply step_app_left, step_beta |].
  unfold subst; cbn [replace]; rewrite ChurchSyntaxFold.ChurchSyntaxFold.nat_fold_replace.
  cbn [replace transpose fin_match].
  eapply rtc_step; [apply step_beta |].
  unfold subst; rewrite ChurchSyntaxFold.ChurchSyntaxFold.nat_fold_replace; syntax_simp.
  reflexivity.
Qed.
Lemma arguments_replace m n (sigma : Fin m -> Term nat n) args : forall f,
  replace sigma (BudgetInternalization.BudgetInternalization.apply_arguments f args) =
  BudgetInternalization.BudgetInternalization.apply_arguments (replace sigma f)
    (map (replace sigma) args).
Proof.
  induction args; intros; cbn [BudgetInternalization.BudgetInternalization.apply_arguments map replace];
    [reflexivity | apply IHargs].
Qed.
Lemma bank_replace m n (sigma : Fin m -> Term nat n) count ceiling : forall start,
  map (replace sigma) (bank count ceiling start) = bank count ceiling start.
Proof. induction count; intros; cbn [bank map replace]; [reflexivity | now rewrite IHcount]. Qed.
Lemma zero_replace k m n (sigma : Fin m -> Term nat n) :
  replace sigma (zero k) = zero k.
Proof. unfold zero; cbn [replace]; rewrite constant_replace; reflexivity. Qed.
Lemma successor_replace k m n (sigma : Fin m -> Term nat n) :
  replace sigma (successor k) = successor k.
Proof.
  destruct k; cbn [successor replace]; rewrite arrows_replace; [reflexivity |].
  rewrite duplicate_replace; reflexivity.
Qed.
Theorem numeric_sort_recovery k i n :
  reduces_to nat n (app (head k) (numeral k i)) (𝓤 (Nat.min i k)).
Proof.
  unfold head; eapply rtc_step; [apply step_beta |].
  unfold subst; rewrite arguments_replace, bank_replace.
  cbn [replace fin_match]; rewrite successor_replace, zero_replace.
  eapply rtc_trans; [apply arguments_reduces, numeral_beta |].
  exact (iteration_recovery k i n 0).
Qed.

Lemma arrow_normal n (X Y : Term nat n) :
  normalb (ChurchSyntax.ChurchSyntax.arrow X Y) = (normalb X && normalb Y).
Proof.
  unfold ChurchSyntax.ChurchSyntax.arrow; cbn [normalb]; unfold shift.
  now rewrite UniformTelescope.UniformTelescope.normalb_rename.
Qed.
Lemma constant_normal count : forall n (x : Term nat n),
  normalb x = true -> normalb (constant count x) = true.
Proof.
  induction count; intros n x H; cbn [constant normalb]; [exact H |].
  apply IHcount; unfold shift; now rewrite UniformTelescope.UniformTelescope.normalb_rename.
Qed.
Lemma duplicate_normal count : forall n (f : Term nat n),
  normalb f = true -> isLambda f = false -> normalb (duplicate count f) = true.
Proof.
  induction count; intros n f HN HL; cbn [duplicate normalb].
  - unfold shift; cbn [normalb isLambda];
      rewrite UniformTelescope.UniformTelescope.normalb_rename,
        UniformTelescope.UniformTelescope.isLambda_rename, HN, HL; reflexivity.
  - apply IHcount; [|reflexivity]. cbn [normalb]; unfold shift.
    rewrite UniformTelescope.UniformTelescope.normalb_rename,
      UniformTelescope.UniformTelescope.isLambda_rename, HN, HL; reflexivity.
Qed.
Lemma zero_normal k n : normalb (@zero k n) = true.
Proof. unfold zero; cbn [normalb]; apply constant_normal; reflexivity. Qed.
Lemma successor_normal k n : normalb (@successor k n) = true.
Proof.
  destruct k; cbn [successor normalb]; rewrite arrows_normal; [reflexivity |].
  apply duplicate_normal; reflexivity.
Qed.
Theorem numeral_normal k i n : normalb (@numeral k i n) = true.
Proof.
  unfold numeral, ChurchSyntax.ChurchSyntax.unary; cbn [normalb].
  rewrite arrow_normal, !arrows_normal.
  apply ChurchSyntax.ChurchSyntax.nat_fold_variables_normal.
Qed.
Lemma numeral_type_normal k n : normalb (@numeral_type k n) = true.
Proof.
  unfold numeral_type, ChurchSyntax.ChurchSyntax.unary.
  rewrite !arrow_normal, !arrows_normal; reflexivity.
Qed.
Lemma arguments_normal n (args : list (Term nat n)) : forall f,
  Forall (fun a => normalb a = true) args ->
  normalb f = true -> isLambda f = false ->
  normalb (BudgetInternalization.BudgetInternalization.apply_arguments f args) = true.
Proof.
  induction args; intros f HA HN HL; cbn [BudgetInternalization.BudgetInternalization.apply_arguments];
    [exact HN |].
  inversion HA; subst. apply IHargs; [assumption | |reflexivity].
  cbn [normalb]; rewrite HN, HL; rewrite H1; reflexivity.
Qed.
Lemma bank_normal count ceiling : forall start n,
  Forall (fun a => normalb a = true) (@bank count ceiling start n).
Proof.
  induction count; intros; cbn [bank]; constructor; [reflexivity | apply IHcount].
Qed.
Theorem head_normal k n : normalb (@head k n) = true.
Proof.
  unfold head; cbn [normalb]; rewrite numeral_type_normal.
  apply arguments_normal; [apply bank_normal | |reflexivity].
  cbn [normalb isLambda]; rewrite successor_normal, zero_normal; reflexivity.
Qed.
Theorem numeral_literal_zero k i n : maxRankLiteral (@numeral k i n) = 0.
Proof.
  assert (HF : forall n, maxRankLiteral
    (@ChurchSyntax.ChurchSyntax.nat_fold (S (S n)) (var fzero) (var (fsucc fzero)) i) = 0).
  { induction i; intros; cbn [ChurchSyntax.ChurchSyntax.nat_fold maxRankLiteral];
      [reflexivity | apply IHi]. }
  unfold numeral, ChurchSyntax.ChurchSyntax.unary, ChurchSyntax.ChurchSyntax.arrow.
  cbn [maxRankLiteral]; unfold shift; rewrite literal_rename, !arrows_literals, HF.
  reflexivity.
Qed.

Print Assumptions successor_typed.
Print Assumptions iteration_recovery.
Print Assumptions numeral_type_sort.
Print Assumptions numeral_typed.
Print Assumptions numeral_normal.
Print Assumptions numeral_literal_zero.
Print Assumptions head_typed.
Print Assumptions head_type_sort.
Print Assumptions head_normal.
Print Assumptions numeric_sort_recovery.

End NumericLiteralBank.
