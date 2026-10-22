From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Ranks DefEq
  Reduction AbstractRewriting.
From PTSrk.NormalizationComplexity Require Import Rank Literals Greedy RedexRanks.
From PTSrk.SelfInterpreter Require Import ChurchSyntax LiteralObstruction.
Import Context RankEstimate ListNotations.

Module BudgetInternalization.

(** Ordinary represented numbers cannot manufacture original sort literals.
    This applies to a reifier followed by an evaluator, independently of their
    typing, and allows arbitrarily many represented budgets, certificate
    fields and trace witnesses.  An argument that itself carries large target
    sort literals is explicitly outside the bounded-data premise.

    The result does NOT obstruct a fixed literal-bounded source fragment, or
    a consistency-specific evaluator whose only result type is Bottom. *)

Fixpoint apply_arguments {n} (head : Term nat n) (args : list (Term nat n)) :=
  match args with
  | [] => head
  | arg :: rest => apply_arguments (app head arg) rest
  end.

Fixpoint argument_ceiling {n} (args : list (Term nat n)) : nat :=
  match args with
  | [] => 0
  | arg :: rest => Nat.max (maxRankLiteral arg) (argument_ceiling rest)
  end.

Lemma application_literals n (args : list (Term nat n)) head :
  maxRankLiteral (apply_arguments head args) =
  Nat.max (maxRankLiteral head) (argument_ceiling args).
Proof.
  revert head; induction args as [|a rest IH]; intro head;
    cbn [apply_arguments argument_ceiling].
  - now rewrite Nat.max_0_r.
  - rewrite IH; cbn [maxRankLiteral]; lia.
Qed.

Lemma argument_ceiling_bound n (args : list (Term nat n)) ceiling :
  Forall (fun t => maxRankLiteral t <= ceiling) args ->
  argument_ceiling args <= ceiling.
Proof.
  intro H; induction H; cbn [argument_ceiling]; lia.
Qed.

Lemma argument_ceiling_witness n (args : list (Term nat n)) k :
  0 < k -> k <= argument_ceiling args ->
  exists arg, In arg args /\ k <= maxRankLiteral arg.
Proof.
  induction args as [|a rest IH]; cbn [argument_ceiling]; intros Hk Hbound.
  - lia.
  - destruct (Nat.le_decidable k (maxRankLiteral a)) as [Ha|Ha].
    + exists a; split; [now left | exact Ha].
    + destruct IH as [arg [Hin Hr]]; try lia.
      exists arg; split; [now right | exact Hr].
Qed.

Lemma normal_reduction_identity n (u v : Term nat n) :
  normalb u = true -> reduces_to nat n u v -> u = v.
Proof.
  intros Hnormal Hred; inversion Hred; subst; [reflexivity |].
  exfalso; eapply normalb_sound; eassumption.
Qed.

Lemma normal_conversion_literals n (t u : Term nat n) :
  normalb u = true -> def_equiv nat n t u ->
  maxRankLiteral u <= maxRankLiteral t.
Proof.
  intros Hnormal Hconv; apply def_equiv_prop in Hconv.
  destruct Hconv as [v [Ht Hu]].
  pose proof (normal_reduction_identity _ _ _ Hnormal Hu); subst v.
  now apply literal_reduction in Ht.
Qed.

Theorem recovered_sort_literal_provenance n (head : Term nat n) args k :
  def_equiv nat n (apply_arguments head args) (𝓤 k) ->
  k <= maxRankLiteral head \/
  exists arg, In arg args /\ k <= maxRankLiteral arg.
Proof.
  intro Hconv.
  pose proof (normal_conversion_literals n _ (𝓤 k) eq_refl Hconv) as Hbound.
  rewrite application_literals in Hbound; cbn [maxRankLiteral] in Hbound.
  destruct (Nat.le_decidable k (maxRankLiteral head)); [now left | right].
  apply argument_ceiling_witness; lia.
Qed.

(** Both phases are actual original syntax.  Quantifying their implementations
    here is stronger than assuming they have some particular PTS types. *)
Definition reify_and_evaluate {n} (reifier evaluator : Term nat n) args :=
  app evaluator (apply_arguments reifier args).

Theorem two_stage_normal_recovery_bound n
    (reifier evaluator source : Term nat n) args ceiling :
  Forall (fun t => maxRankLiteral t <= ceiling) args ->
  normalb source = true ->
  def_equiv nat n (reify_and_evaluate reifier evaluator args) source ->
  maxRankLiteral source <=
    Nat.max (Nat.max (maxRankLiteral evaluator) (maxRankLiteral reifier)) ceiling.
Proof.
  intros Hargs Hnormal Hconv.
  pose proof (normal_conversion_literals n _ _ Hnormal Hconv) as Hbound.
  unfold reify_and_evaluate in Hbound; cbn [maxRankLiteral] in Hbound.
  rewrite application_literals in Hbound.
  pose proof (argument_ceiling_bound _ _ _ Hargs); lia.
Qed.

Theorem two_stage_sort_literal_provenance n
    (reifier evaluator : Term nat n) args k :
  def_equiv nat n (reify_and_evaluate reifier evaluator args) (𝓤 k) ->
  k <= Nat.max (maxRankLiteral evaluator) (maxRankLiteral reifier) \/
  exists arg, In arg args /\ k <= maxRankLiteral arg.
Proof.
  intro Hconv.
  pose proof (normal_conversion_literals n _ (𝓤 k) eq_refl Hconv) as Hbound.
  unfold reify_and_evaluate in Hbound; cbn [maxRankLiteral] in Hbound.
  rewrite application_literals in Hbound; cbn [maxRankLiteral] in Hbound.
  destruct (Nat.le_decidable k
    (Nat.max (maxRankLiteral evaluator) (maxRankLiteral reifier)));
    [now left | right].
  apply argument_ceiling_witness; lia.
Qed.

Theorem no_unbounded_internal_strong_reification
    (reifier evaluator : Term nat 0) ceiling
    (data : nat -> list (Term nat 0)) :
  (forall k, Forall (fun t => maxRankLiteral t <= ceiling) (data k)) ->
  ~ (forall k, def_equiv nat 0
      (reify_and_evaluate reifier evaluator (data k)) (𝓤 k)).
Proof.
  intros Hdata Hrecover.
  set (k := S (Nat.max
    (Nat.max (maxRankLiteral evaluator) (maxRankLiteral reifier)) ceiling)).
  pose proof (two_stage_normal_recovery_bound 0 reifier evaluator
    (𝓤 k) (data k) ceiling (Hdata k) eq_refl (Hrecover k)) as Hbound.
  cbn [maxRankLiteral] in Hbound; unfold k in Hbound; lia.
Qed.

(** The existing raw HOAS representation stores a numeric label as Church
    numeral data.  Every entry below is originally typed and beta-normal,
    even when the represented numbers and the list length are unbounded.
    No claim that this particular list format already encodes proof checking
    or the draft's independent acceptance predicate is made. *)
Definition represented_numbers r (numbers : list nat) : list (Term nat 0) :=
  map (fun k => ChurchSyntax.ChurchSyntax.quote r (@𝓤 nat 0 k)) numbers.

Theorem represented_numbers_typed r numbers :
  Forall (fun t => @typ nat RankSorts 0 ε t
    (ChurchSyntax.ChurchSyntax.code_type r 0)) (represented_numbers r numbers).
Proof.
  unfold represented_numbers; apply Forall_map, Forall_forall.
  intros; apply ChurchSyntax.ChurchSyntax.quote_typing.
Qed.

Theorem represented_numbers_normal r numbers :
  Forall (fun t => normalb t = true) (represented_numbers r numbers).
Proof.
  unfold represented_numbers; apply Forall_map, Forall_forall.
  intros; apply ChurchSyntax.ChurchSyntax.quote_normal.
Qed.

Lemma represented_numbers_bounded r numbers :
  Forall (fun t => maxRankLiteral t <= r) (represented_numbers r numbers).
Proof.
  unfold represented_numbers; apply Forall_map, Forall_forall.
  intros; rewrite LiteralObstruction.LiteralObstruction.quote_literal_exact; lia.
Qed.

Corollary represented_budgets_do_not_internalize_unbounded_sorts
    (reifier evaluator : Term nat 0) r (numbers : nat -> list nat) :
  ~ (forall k, def_equiv nat 0
      (reify_and_evaluate reifier evaluator (represented_numbers r (numbers k)))
      (𝓤 k)).
Proof.
  apply no_unbounded_internal_strong_reification with (ceiling := r).
  intro k; apply represented_numbers_bounded.
Qed.

Theorem normal_sort_counterexample
    (reifier evaluator : Term nat 0) r (numbers : nat -> list nat) :
  exists k,
    @typ nat RankSorts 0 ε (𝓤 k) (𝓤 0) /\
    TypeRank ε (𝓤 k) 0 /\ normalb (@𝓤 nat 0 k) = true /\
    RedexBound ε (𝓤 k) 0 /\
    ~ def_equiv nat 0
      (reify_and_evaluate reifier evaluator (represented_numbers r (numbers k)))
      (𝓤 k).
Proof.
  exists (S (Nat.max
    (Nat.max (maxRankLiteral evaluator) (maxRankLiteral reifier)) r)).
  repeat split.
  - apply LiteralObstruction.LiteralObstruction.sort_typed.
  - apply LiteralObstruction.LiteralObstruction.sort_type_rank_zero.
  - apply LiteralObstruction.LiteralObstruction.sort_redex_bound_zero.
  - intro Hconv.
    pose proof (two_stage_normal_recovery_bound 0 reifier evaluator
      (𝓤 (S (Nat.max
        (Nat.max (maxRankLiteral evaluator) (maxRankLiteral reifier)) r))) _ r
      (represented_numbers_bounded r _) eq_refl Hconv) as Hbound.
    cbn [maxRankLiteral] in Hbound; lia.
Qed.

Print Assumptions application_literals.
Print Assumptions recovered_sort_literal_provenance.
Print Assumptions two_stage_normal_recovery_bound.
Print Assumptions two_stage_sort_literal_provenance.
Print Assumptions no_unbounded_internal_strong_reification.
Print Assumptions represented_numbers_typed.
Print Assumptions represented_numbers_normal.
Print Assumptions represented_budgets_do_not_internalize_unbounded_sorts.
Print Assumptions normal_sort_counterexample.

End BudgetInternalization.
