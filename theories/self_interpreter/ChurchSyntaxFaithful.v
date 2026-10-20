From Stdlib Require Import Arith.PeanoNat.
From Equations Require Import Equations.
From PTSrk Require Import Syntax DefEq Reduction AbstractRewriting.
From PTSrk.NormalizationComplexity Require Import Greedy.
From PTSrk.SelfInterpreter Require Import ChurchSyntax.
Import ChurchSyntax.ChurchSyntax.

(** Exact faithfulness of raw HOAS, at a fixed original source scope.
    The carrier environment represents source variables by distinct target
    variables. Both original annotations and binding positions are retained.
    No source typing, erasure, or functional extensionality is used. *)

Lemma nat_fold_injective n (z s : Fin n) k :
  forall j, nat_fold (var z) (var s) k =
    nat_fold (var z) (var s) j -> k = j.
Proof.
  induction k; intros j H; destruct j; cbn [nat_fold] in H;
    try discriminate.
  - reflexivity.
  - f_equal. apply IHk. now injection H.
Qed.

Lemma fsucc_injective n (i j : Fin n) : fsucc i = fsucc j -> i = j.
Proof.
  intro H. exact (f_equal (fin_match i (fun k => k)) H).
Qed.

Lemma weak_injective m n (rho : Fin m -> Fin n) :
  (forall i j, rho i = rho j -> i = j) ->
  forall i j, weak rho i = weak rho j -> i = j.
Proof.
  intros Hinj i j H. dependent elimination i; dependent elimination j;
    cbn [weak fin_match] in H; try discriminate.
  - reflexivity.
  - f_equal. apply Hinj. now apply fsucc_injective in H.
Qed.

Lemma transpose_variable_environment m n (rho : Fin m -> Term nat n)
    (indices : Fin m -> Fin n) :
  (forall i, rho i = var (indices i)) ->
  forall i, transpose rho i = var (weak indices i).
Proof.
  intros Henv i. dependent elimination i.
  - reflexivity.
  - cbn [transpose fin_match weak]. rewrite Henv. reflexivity.
Qed.

Theorem ast_fold_injective m (t : Term nat m) :
  forall n (X : Term nat n) (z s u p l a : Fin n)
    (rho : Fin m -> Term nat n) (indices : Fin m -> Fin n),
  (forall i, rho i = var (indices i)) ->
  (forall i j, indices i = indices j -> i = j) ->
  p <> l -> p <> a -> l <> a ->
  forall t' : Term nat m,
    ast_fold X (var z) (var s) (var u) (var p) (var l) (var a) rho t =
    ast_fold X (var z) (var s) (var u) (var p) (var l) (var a) rho t' ->
    t = t'.
Proof.
  induction t; intros target X z s hu hp hl ha rho indices Henv Hinj Hpl Hpa Hla t' H;
    dependent elimination t'; cbn [ast_fold] in H;
    rewrite ?Henv in H; try discriminate; try congruence.
  - injection H as Hlabel. apply nat_fold_injective in Hlabel.
    now subst.
  - injection H as Hleft Hright. f_equal.
    + eapply (IHt1 target X z s hu hp hl ha rho indices); eassumption.
    + eapply (IHt2 (S target) (shift X) (fsucc z) (fsucc s)
        (fsucc hu) (fsucc hp) (fsucc hl) (fsucc ha)
        (transpose rho) (weak indices)).
      * apply transpose_variable_environment. exact Henv.
      * apply weak_injective. exact Hinj.
      * congruence.
      * congruence.
      * congruence.
      * exact Hright.
  - injection H as Hi. f_equal. apply Hinj. exact Hi.
  - injection H as Hleft Hright. f_equal.
    + eapply (IHt1 target X z s hu hp hl ha rho indices); eassumption.
    + eapply (IHt2 (S target) (shift X) (fsucc z) (fsucc s)
        (fsucc hu) (fsucc hp) (fsucc hl) (fsucc ha)
        (transpose rho) (weak indices)).
      * apply transpose_variable_environment. exact Henv.
      * apply weak_injective. exact Hinj.
      * congruence.
      * congruence.
      * congruence.
      * exact Hright.
  - injection H as Hleft Hright. f_equal.
    + eapply (IHt1 target X z s hu hp hl ha rho indices); eassumption.
    + eapply (IHt2 target X z s hu hp hl ha rho indices); eassumption.
Qed.

Lemma front_injective m n (i : Fin m) :
  forall j, @front m n i = @front m n j -> i = j.
Proof.
  induction i; intros j H; dependent elimination j;
    cbn [front] in H; try discriminate.
  - reflexivity.
  - f_equal. apply IHi. now apply fsucc_injective in H.
Qed.

Lemma up_injective m n (i j : Fin n) :
  @up m n i = @up m n j -> i = j.
Proof.
  induction m; cbn [up]; intro H; [exact H |].
  apply IHm. now apply fsucc_injective in H.
Qed.

Theorem body_injective n (t u : Term nat n) : body t = body u -> t = u.
Proof.
  unfold body. cbn [rename]. intro H.
  eapply ast_fold_injective with (indices := @front n 7) in H.
  - exact H.
  - reflexivity.
  - apply front_injective.
  - intro E. apply up_injective in E. discriminate.
  - intro E. apply up_injective in E. discriminate.
  - intro E. apply up_injective in E. discriminate.
Qed.

Lemma bind_vars_injective count n (X : Term nat n)
    (t u : Term nat (count+n)) :
  bind_vars count X t = bind_vars count X u -> t = u.
Proof.
  revert t u. induction count; intros t u; cbn [bind_vars]; intro H; [exact H |].
  apply IHcount in H. now injection H.
Qed.

Theorem quote_injective r n (t u : Term nat n) :
  quote r t = quote r u -> t = u.
Proof.
  intro H. apply body_injective. unfold quote in H.
  injection H as Hbody. now apply bind_vars_injective in Hbody.
Qed.

Theorem quote_indices_injective r s n (t u : Term nat n) :
  quote r t = quote s u -> r = s /\ t = u.
Proof.
  intro H. assert (Hr : r = s).
  { unfold quote in H. injection H as Hr Hbody. exact Hr. }
  subst s. split; [reflexivity | apply (quote_injective r n t u H)].
Qed.

Lemma normal_reduction_identity n (t u : Term nat n) :
  normalb t = true -> reduces_to nat n t u -> t = u.
Proof.
  intros Hnormal Hreduce. inversion Hreduce; subst; [reflexivity |].
  exfalso. eapply normalb_sound; eassumption.
Qed.

Lemma normal_conversion_identity n (t u : Term nat n) :
  normalb t = true -> normalb u = true -> def_equiv nat n t u -> t = u.
Proof.
  intros Ht Hu Hconv. apply def_equiv_prop in Hconv as [v [Htv Huv]].
  transitivity v.
  - eapply normal_reduction_identity; eassumption.
  - symmetry. eapply normal_reduction_identity; eassumption.
Qed.

(** Original beta conversion reduces annotations too. The result recovers
    literal annotated source syntax, not source beta-equivalence classes. *)
Theorem quote_conversion_injective r s n (t u : Term nat n) :
  def_equiv nat 0 (quote r t) (quote s u) -> r = s /\ t = u.
Proof.
  intro H. apply quote_indices_injective.
  eapply normal_conversion_identity;
    [apply quote_normal | apply quote_normal | exact H].
Qed.

Theorem quote_conversion_iff r s n (t u : Term nat n) :
  def_equiv nat 0 (quote r t) (quote s u) <-> r = s /\ t = u.
Proof.
  split; [apply quote_conversion_injective |].
  intros [Hr Ht]; subst s; subst u; reflexivity.
Qed.

Print Assumptions ast_fold_injective.
Print Assumptions body_injective.
Print Assumptions quote_injective.
Print Assumptions quote_indices_injective.
Print Assumptions quote_conversion_injective.
Print Assumptions quote_conversion_iff.
