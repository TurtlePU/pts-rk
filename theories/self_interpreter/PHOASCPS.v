From Stdlib Require Import Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting Congruence DefEq.
From PTSrk.NormalizationComplexity Require Import STLCEmbedding Morphisms Greedy RedexRanks.
From PTSrk.SelfInterpreter Require Import BrownPalsberg TypedHOAS.
Import Context ChurchSTLC.

(** Call-by-name continuation HANDLERS in the original annotated PTS.
    This is not a full dependent CPS translation and not a filling of the
    existing rank-preserving PHOAS signature: the final theorem explains
    exactly why that direct substitution fails.  The beta clauses concern
    actual constructor operations, not a continuation wrapper around an
    already evaluated whole program. *)
Module PHOASCPS.
Module BP := BrownPalsberg.BrownPalsberg.
Module TH := TypedHOAS.TypedHOAS.

Definition continuation {n} (A R : Term nat n) := BP.arr (BP.arr A R) R.
Definition continuation_rank a b := Nat.max (a+2) (b+1).
Definition return_value {n} (A R x : Term nat n) :=
  lam (BP.arr A R) (app (var fzero) (shift x)).
Definition function_value {n} (A B R : Term nat n) :=
  BP.arr (continuation A R) (continuation B R).
Definition abstraction {n} (A B R f : Term nat n) :=
  return_value (function_value A B R) R f.
Definition application {n} (A B R f x : Term nat n) :=
  lam (BP.arr B R)
    (app (shift f)
      (lam (shift (function_value A B R))
        (app (app (var fzero) (shift (shift x))) (var (fsucc fzero))))).

Lemma continuation_rename m n (rho : Fin m -> Fin n) A R :
  rename rho (continuation A R) = continuation (rename rho A) (rename rho R).
Proof. unfold continuation; rewrite !TH.arr_rename; reflexivity. Qed.
Lemma continuation_replace m n (sigma : Fin m -> Term nat n) A R :
  replace sigma (continuation A R) = continuation (replace sigma A) (replace sigma R).
Proof. unfold continuation; rewrite !TH.arr_replace; reflexivity. Qed.
Lemma continuation_shift n (A R : Term nat n) :
  shift (continuation A R) = continuation (shift A) (shift R).
Proof. apply continuation_rename. Qed.
Lemma function_value_rename m n (rho : Fin m -> Fin n) A B R :
  rename rho (function_value A B R) =
  function_value (rename rho A) (rename rho B) (rename rho R).
Proof. unfold function_value; rewrite TH.arr_rename, !continuation_rename; reflexivity. Qed.
Theorem continuation_sort n (G : Ctx nat n) A R a b :
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G R (𝓤 b) ->
  @typ nat RankSorts n G (continuation A R) (𝓤 (continuation_rank a b)).
Proof.
  intros HA HR; unfold continuation, continuation_rank.
  replace (Nat.max (a+2) (b+1)) with (Nat.max (S (Nat.max (S a) b)) b) by lia.
  apply BP.arr_sort; [apply BP.arr_sort; assumption | exact HR].
Qed.
Theorem return_value_typed n (G : Ctx nat n) A R x a b :
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G R (𝓤 b) ->
  @typ nat RankSorts n G x A ->
  @typ nat RankSorts n G (return_value A R x) (continuation A R).
Proof.
  intros HA HR Hx; unfold return_value, continuation, BP.arr at 1.
  eapply typ_λ with (ℓ := Nat.max (S a) b).
  - apply BP.arr_sort; assumption.
  - eapply BP.arr_apply with (A := shift A).
    + rewrite <- BP.arr_shift.
      change (typ (G & BP.arr A R) (var fzero) ((G & BP.arr A R) !! fzero)); constructor.
    + apply weakening; exact Hx.
Qed.
Theorem return_value_beta n (A R x k : Term nat n) :
  reduces_to nat n (app (return_value A R x) k) (app k x).
Proof.
  unfold return_value; eapply rtc_step; [apply step_beta |].
  unfold subst; cbn [replace fin_match]; syntax_simp; reflexivity.
Qed.
Definition function_rank a b r :=
  Nat.max (S (continuation_rank a r)) (continuation_rank b r).
Theorem function_value_sort n (G : Ctx nat n) A B R a b r :
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G B (𝓤 b) ->
  @typ nat RankSorts n G R (𝓤 r) ->
  @typ nat RankSorts n G (function_value A B R) (𝓤 (function_rank a b r)).
Proof. intros; unfold function_value, function_rank; apply BP.arr_sort; eapply continuation_sort; eassumption. Qed.
Theorem abstraction_typed n (G : Ctx nat n) A B R f a b r :
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G B (𝓤 b) ->
  @typ nat RankSorts n G R (𝓤 r) ->
  @typ nat RankSorts n G f (function_value A B R) ->
  @typ nat RankSorts n G (abstraction A B R f)
    (continuation (function_value A B R) R).
Proof.
  intros; unfold abstraction; eapply return_value_typed;
    [eapply function_value_sort; eassumption | eassumption | eassumption].
Qed.
Theorem application_typed n (G : Ctx nat n) A B R f x a b r :
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G B (𝓤 b) ->
  @typ nat RankSorts n G R (𝓤 r) ->
  @typ nat RankSorts n G f (continuation (function_value A B R) R) ->
  @typ nat RankSorts n G x (continuation A R) ->
  @typ nat RankSorts n G (application A B R f x) (continuation B R).
Proof.
  intros HA HB HR Hf Hx; unfold application, continuation at 1, BP.arr at 1.
  eapply typ_λ with (ℓ := Nat.max (S b) r).
  - apply BP.arr_sort; assumption.
  - eapply BP.arr_apply with (A := BP.arr (shift (function_value A B R)) (shift R)).
    + change (typ (G & BP.arr B R) (shift f)
        (continuation (shift (function_value A B R)) (shift R))).
      rewrite <- continuation_shift; apply weakening; exact Hf.
    + unfold BP.arr at 1; eapply typ_λ with (ℓ := function_rank a b r).
      * change (typ (G & BP.arr B R) (shift (function_value A B R)) (shift (𝓤 (function_rank a b r)))).
        apply weakening; eapply function_value_sort; eassumption.
      * eapply BP.arr_apply with (A := BP.arr (shift (shift B)) (shift (shift R))).
        -- eapply BP.arr_apply with (A := continuation (shift (shift A)) (shift (shift R))).
           ++ unfold function_value.
              rewrite <- !continuation_shift, <- !BP.arr_shift.
              change (typ ((G & BP.arr B R) & shift (function_value A B R))
                (var fzero) (((G & BP.arr B R) & shift (function_value A B R)) !! fzero)); constructor.
           ++ rewrite <- !continuation_shift; apply weakening, weakening; exact Hx.
        -- rewrite <- !BP.arr_shift.
           change (typ ((G & BP.arr B R) & shift (function_value A B R))
             (var (fsucc fzero)) (((G & BP.arr B R) & shift (function_value A B R)) !! fsucc fzero)); constructor.
Qed.

(** Administrative beta law at a supplied continuation; no eta conversion
    or function extensionality is added to the original calculus. *)
Theorem application_run n (A B R f x k : Term nat n) :
  reduces_to nat n
    (app (application A B R (abstraction A B R f) x) k)
    (app (app f x) k).
Proof.
  unfold application; eapply rtc_step; [apply step_beta |].
  unfold subst; cbn [replace]; syntax_simp;
    cbn [transpose fin_match weak]; syntax_simp.
  repeat rewrite replace_as_rename.
  unfold abstraction.
  eapply rtc_trans; [apply return_value_beta |].
  eapply rtc_step; [apply step_beta |].
  unfold subst; cbn [replace transpose fin_match]; syntax_simp; reflexivity.
Qed.
Theorem abstraction_application_run n (A B R x k : Term nat n) body :
  reduces_to nat n
    (app (application A B R
      (abstraction A B R (lam (continuation A R) body)) x) k)
    (app (subst body x) k).
Proof.
  eapply rtc_trans; [apply application_run |].
  apply rtc_in, step_app_left, step_beta.
Qed.

Theorem continuation_not_same_rank n (G : Ctx nat n) A R a b :
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G R (𝓤 b) ->
  ~ @typ nat RankSorts n G (continuation A R) (𝓤 a).
Proof.
  intros HA HR HC.
  pose proof (sort_rank_unique G _ _ _ (continuation_sort n G A R a b HA HR) HC).
  unfold continuation_rank in H; lia.
Qed.

(** The ordinary CBN rank recurrence, not an impossibility theorem about
    all CPS encodings.  Right-nested source arrows stay at source rank 1,
    while this structural translation requires unbounded target ranks. *)
Fixpoint value_rank a r (A : Ty) : nat :=
  match A with
  | base => a
  | arrow B C => Nat.max (S (continuation_rank (value_rank a r B) r))
      (continuation_rank (value_rank a r C) r)
  end.
Definition computation_rank a r A := continuation_rank (value_rank a r A) r.
Fixpoint value_type {n} (O R : Term nat n) (A : Ty) : Term nat n :=
  match A with
  | base => O
  | arrow B C => function_value (value_type O R B) (value_type O R C) R
  end.
Definition computation_type {n} (O R : Term nat n) A := continuation (value_type O R A) R.
Theorem value_type_sort A n (G : Ctx nat n) O R a r :
  @typ nat RankSorts n G O (𝓤 a) ->
  @typ nat RankSorts n G R (𝓤 r) ->
  @typ nat RankSorts n G (value_type O R A) (𝓤 (value_rank a r A)).
Proof.
  intros HO HR; induction A; cbn [value_type value_rank]; [exact HO |].
  apply function_value_sort; assumption.
Qed.
Theorem computation_type_sort A n (G : Ctx nat n) O R a r :
  @typ nat RankSorts n G O (𝓤 a) ->
  @typ nat RankSorts n G R (𝓤 r) ->
  @typ nat RankSorts n G (computation_type O R A) (𝓤 (computation_rank a r A)).
Proof.
  intros; unfold computation_type, computation_rank;
    eapply continuation_sort; [eapply value_type_sort |]; eassumption.
Qed.
Fixpoint right_arrow n := match n with 0 => base | S j => arrow base (right_arrow j) end.
Theorem right_arrow_source_rank n : order (right_arrow (S n)) = 1.
Proof.
  induction n; [reflexivity |].
  change (Nat.max 1 (order (right_arrow (S n))) = 1); rewrite IHn; reflexivity.
Qed.
Theorem right_arrow_cps_rank n : computation_rank 0 0 (right_arrow (S n)) = 2*n+5.
Proof.
  induction n; [reflexivity |].
  unfold computation_rank in *; cbn [right_arrow value_rank] in *.
  unfold continuation_rank in *; lia.
Qed.
Theorem no_rank_one_cps_budget K :
  exists A, order A = 1 /\ K < computation_rank 0 0 A.
Proof.
  exists (right_arrow (S K)); split;
    [apply right_arrow_source_rank | rewrite right_arrow_cps_rank; lia].
Qed.
Theorem no_rank_one_cps_type_budget K n (G : Ctx nat n) O R :
  @typ nat RankSorts n G O (𝓤 0) ->
  @typ nat RankSorts n G R (𝓤 0) ->
  exists A, order A = 1 /\
    forall r, @typ nat RankSorts n G (computation_type O R A) (𝓤 r) -> K < r.
Proof.
  intros HO HR; destruct (no_rank_one_cps_budget K) as [A [HA HK]].
  exists A; split; [exact HA | intros r Hr].
  pose proof (sort_rank_unique G _ _ _ (computation_type_sort A n G O R 0 0 HO HR) Hr).
  lia.
Qed.

Print Assumptions continuation_sort.
Print Assumptions return_value_typed.
Print Assumptions return_value_beta.
Print Assumptions abstraction_typed.
Print Assumptions application_typed.
Print Assumptions application_run.
Print Assumptions abstraction_application_run.
Print Assumptions continuation_not_same_rank.
Print Assumptions value_type_sort.
Print Assumptions computation_type_sort.
Print Assumptions no_rank_one_cps_budget.
Print Assumptions no_rank_one_cps_type_budget.
End PHOASCPS.
