From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting.
From PTSrk.NormalizationComplexity Require Import Rank Literals Greedy Morphisms.
From PTSrk.SelfInterpreter Require Import PHOASTelescope ChurchSyntax.
Import Context RankEstimate.

Module FiniteLiteralBank.

(** A positive boundary case for internal represented budgets.  Fix a finite
    bank of original sort literals.  All its indices have one normal Church
    selector type, using only literal 0, and one normal originally typed head
    recovers the selected sort.  The number of entries does not increase the
    selector type's formation rank (1) or the head type's formation rank (2).

    These finite selectors are not unbounded Church numerals.  No parser,
    proof checker, numeral-to-selector conversion or full PHOAS reifier is
    supplied by this leaf construction. *)

Fixpoint context (count : nat) : Ctx nat count :=
  match count with 0 => ε | S rest => context rest & 𝓤 0 end.

Lemma context_wf count : @wf nat RankSorts count (context count).
Proof.
  induction count; cbn [context]; [constructor |].
  econstructor; [exact IHcount | constructor; reflexivity].
Qed.

Lemma context_lookup count (i : Fin count) : context count !! i = 𝓤 0.
Proof.
  induction i; [reflexivity |].
  change (shift (context n !! i) = 𝓤 0).
  rewrite IHi; reflexivity.
Qed.

Lemma context_normal count :
  PHOASTelescope.PHOASTelescope.normal_context (context count) = true.
Proof.
  induction count; cbn [context PHOASTelescope.PHOASTelescope.normal_context
    normalb]; [reflexivity | now rewrite IHcount].
Qed.

Definition selector_type count :=
  PHOASTelescope.PHOASTelescope.close_type (context count) (𝓤 0).
Definition selector {count} (i : Fin count) :=
  PHOASTelescope.PHOASTelescope.close_term (context count) (var i).

Lemma close_type_sort count : forall T r,
  @typ nat RankSorts count (context count) T (𝓤 r) ->
  @typ nat RankSorts 0 ε
    (PHOASTelescope.PHOASTelescope.close_type (context count) T)
    (𝓤 (Nat.max (Nat.min count 1) r)).
Proof.
  induction count; intros T r HT; cbn [context
    PHOASTelescope.PHOASTelescope.close_type] in *.
  - exact HT.
  - assert (Hform : @typ nat RankSorts count (context count)
        (Π (𝓤 0) T) (𝓤 (Nat.max 1 r))).
    { eapply typ_Π with (ℓₜ := 0) (ℓᵤ := r);
        [constructor; reflexivity | exact HT | reflexivity]. }
    specialize (IHcount _ _ Hform).
    replace (Nat.max (Nat.min count 1) (Nat.max 1 r)) with (Nat.max 1 r)
      in IHcount by lia.
    replace (Nat.min (S count) 1) with 1 by lia.
    exact IHcount.
Qed.

Theorem selector_type_sort k :
  @typ nat RankSorts 0 ε (selector_type (S k)) (𝓤 1).
Proof.
  unfold selector_type.
  replace 1 with (Nat.max (Nat.min (S k) 1) 0) by lia.
  apply close_type_sort; constructor; reflexivity.
Qed.

Theorem selector_typed count (i : Fin count) :
  @typ nat RankSorts 0 ε (selector i) (selector_type count).
Proof.
  unfold selector, selector_type.
  apply PHOASTelescope.PHOASTelescope.close_typing; [apply context_wf |].
  rewrite <- (context_lookup count i); constructor.
Qed.

Theorem selector_normal count (i : Fin count) : normalb (selector i) = true.
Proof.
  apply PHOASTelescope.PHOASTelescope.close_normal;
    [apply context_normal | reflexivity].
Qed.

Lemma close_term_literals count : forall (t : Term nat count),
  maxRankLiteral (PHOASTelescope.PHOASTelescope.close_term (context count) t) =
  maxRankLiteral t.
Proof.
  induction count; intro t; cbn [context PHOASTelescope.PHOASTelescope.close_term].
  - reflexivity.
  - rewrite IHcount; reflexivity.
Qed.

Theorem selector_literal_zero count (i : Fin count) :
  maxRankLiteral (selector i) = 0.
Proof. apply close_term_literals. Qed.

Definition filling {count n} (labels : Fin count -> nat) : Fin count -> Term nat n :=
  fun i => 𝓤 (labels i).

Lemma filling_typed count n (G : Ctx nat n) labels :
  TypedSub (context count) G (filling labels).
Proof.
  intro i; rewrite context_lookup; cbn [replace filling]; constructor; reflexivity.
Qed.

Definition head {count} (labels : Fin count -> nat) : Term nat 0 :=
  lam (selector_type count)
    (PHOASTelescope.PHOASTelescope.run (context count) (filling labels) (var fzero)).

Lemma lift_closed_one (t : Term nat 0) :
  @PHOASTelescope.PHOASTelescope.lift_closed 1 t = shift t.
Proof.
  unfold PHOASTelescope.PHOASTelescope.lift_closed, shift.
  apply rename_ext; intro i; inversion i.
Qed.

Theorem head_typed k (labels : Fin (S k) -> nat) :
  @typ nat RankSorts 0 ε (head labels)
    (ChurchSyntax.ChurchSyntax.arrow (selector_type (S k)) (𝓤 0)).
Proof.
  unfold head, ChurchSyntax.ChurchSyntax.arrow.
  eapply typ_λ with (ℓ := 1); [apply selector_type_sort |].
  change (typ (ε & selector_type (S k))
    (PHOASTelescope.PHOASTelescope.run (context (S k)) (filling labels) (var fzero))
    (replace (filling labels) (@𝓤 nat (S k) 0))).
  apply PHOASTelescope.PHOASTelescope.run_typing; [apply filling_typed |].
  rewrite lift_closed_one; constructor.
Qed.

Theorem head_type_sort k :
  @typ nat RankSorts 0 ε
    (ChurchSyntax.ChurchSyntax.arrow (selector_type (S k)) (𝓤 0)) (𝓤 2).
Proof.
  change (typ ε (ChurchSyntax.ChurchSyntax.arrow (selector_type (S k)) (𝓤 0))
    (𝓤 (Nat.max (S 1) 0))).
  apply ChurchSyntax.ChurchSyntax.arrow_sort;
    [apply selector_type_sort | constructor; reflexivity].
Qed.

Lemma close_type_normal count : forall T,
  normalb T = true ->
  normalb (PHOASTelescope.PHOASTelescope.close_type (context count) T) = true.
Proof.
  induction count; intros T HT; cbn [context PHOASTelescope.PHOASTelescope.close_type].
  - exact HT.
  - apply IHcount; exact HT.
Qed.

Lemma run_normal count : forall n labels (q : Term nat n),
  normalb q = true -> isLambda q = false ->
  normalb (PHOASTelescope.PHOASTelescope.run (context count) (filling labels) q) = true /\
  isLambda (PHOASTelescope.PHOASTelescope.run (context count) (filling labels) q) = false.
Proof.
  induction count; intros n labels q Hnormal Hlambda;
    cbn [context PHOASTelescope.PHOASTelescope.run].
  - auto.
  - destruct (IHcount n (fun i => labels (fsucc i)) q Hnormal Hlambda) as [HN HL].
    split; [|reflexivity].
    change ((normalb (PHOASTelescope.PHOASTelescope.run (context count)
      (filling (fun i => labels (fsucc i))) q) && true) &&
      negb (isLambda (PHOASTelescope.PHOASTelescope.run (context count)
        (filling (fun i => labels (fsucc i))) q)) = true).
    rewrite HN, HL; reflexivity.
Qed.

Theorem head_normal count (labels : Fin count -> nat) : normalb (head labels) = true.
Proof.
  unfold head; cbn [normalb].
  unfold selector_type; rewrite close_type_normal by reflexivity.
  exact (proj1 (run_normal count 1 labels (var fzero) eq_refl eq_refl)).
Qed.

Theorem selected_sort_recovery count (labels : Fin count -> nat) (i : Fin count) :
  reduces_to nat 0 (app (head labels) (selector i)) (𝓤 (labels i)).
Proof.
  unfold head; eapply rtc_step; [apply step_beta |].
  unfold subst; rewrite PHOASTelescope.PHOASTelescope.run_replace.
  cbn [replace fin_match filling].
  change (reduces_to nat 0
    (PHOASTelescope.PHOASTelescope.run (context count) (filling labels) (selector i))
    (replace (filling labels) (var i))).
  replace (selector i) with
    (@PHOASTelescope.PHOASTelescope.lift_closed 0 (selector i)).
  - apply PHOASTelescope.PHOASTelescope.run_closed_term.
  - unfold PHOASTelescope.PHOASTelescope.lift_closed.
    etransitivity; [|apply rename_id].
    apply rename_ext; intro j; inversion j.
Qed.

Lemma bounded_index k : forall i, i <= k ->
  exists j : Fin (S k), ChurchSyntax.ChurchSyntax.fin_index j = i.
Proof.
  induction k; intros i Hi; destruct i.
  - exists fzero; reflexivity.
  - lia.
  - exists fzero; reflexivity.
  - destruct (IHk i) as [j Hj]; [lia |].
    exists (fsucc j); cbn [ChurchSyntax.ChurchSyntax.fin_index]; now rewrite Hj.
Qed.

Theorem one_head_for_bounded_sorts k :
  exists decoder,
    @typ nat RankSorts 0 ε decoder
      (ChurchSyntax.ChurchSyntax.arrow (selector_type (S k)) (𝓤 0)) /\
    normalb decoder = true /\
    forall i, i <= k -> exists code,
      @typ nat RankSorts 0 ε code (selector_type (S k)) /\
      normalb code = true /\ maxRankLiteral code = 0 /\
      reduces_to nat 0 (app decoder code) (𝓤 i).
Proof.
  exists (@head (S k) (@ChurchSyntax.ChurchSyntax.fin_index (S k))).
  split; [apply head_typed |]. split; [apply head_normal |].
  intros i Hi; destruct (bounded_index k i Hi) as [j Hj].
  exists (selector j); split; [apply selector_typed |].
  split; [apply selector_normal |]. split; [apply selector_literal_zero |].
  rewrite <- Hj; apply selected_sort_recovery.
Qed.

Print Assumptions selector_type_sort.
Print Assumptions selector_typed.
Print Assumptions selector_normal.
Print Assumptions selector_literal_zero.
Print Assumptions head_typed.
Print Assumptions head_type_sort.
Print Assumptions head_normal.
Print Assumptions selected_sort_recovery.
Print Assumptions one_head_for_bounded_sorts.

End FiniteLiteralBank.
