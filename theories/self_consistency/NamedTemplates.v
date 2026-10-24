(** Native syntax infrastructure for checked PTS templates.  Substituting a
    closed argument commutes with the original annotated assembler; equivalent
    closed fragments may be replaced without unfolding their syntax.  These
    lemmas optimize proof checking, not the PTS typing rules or source graphs. *)
From Stdlib Require Import Lists.List Arith.PeanoNat.
From PTSrk Require Import -(notations) Syntax.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRStructural.
Import ListNotations.
Module NamedTemplates.
Import CommonCodes Core Structural.

Definition environment n := nat -> option (Term nat n).
Definition extend {n} (x : nat) (e : environment n) : environment (S n) :=
  fun y => if Nat.eqb y x then Some (var fzero) else option_map shift (e y).
Fixpoint evaluate {n} (t : named) (e : environment n) : option (Term nat n) :=
  match t with
  | NSort r => Some (𝓤 r)
  | NClosed c => Some (lift_closed c)
  | NVar x => e x
  | NPi x a b =>
      match evaluate a e, evaluate b (extend x e) with
      | Some a', Some b' => Some (Π a' b') | _, _ => None end
  | NArrow a b =>
      match evaluate a e, evaluate b e with
      | Some a', Some b' => Some (Arrow a' b') | _, _ => None end
  | NLam x a b =>
      match evaluate a e, evaluate b (extend x e) with
      | Some a', Some b' => Some (lam a' b') | _, _ => None end
  | NApp a b =>
      match evaluate a e, evaluate b e with
      | Some a', Some b' => Some (app a' b') | _, _ => None end
  end.

Lemma evaluate_ext t : forall n (e e' : environment n),
  (forall x, e x = e' x) -> evaluate t e = evaluate t e'.
Proof.
  induction t; intros k e e' H; cbn [evaluate].
  - reflexivity.
  - apply H.
  - rewrite (IHt1 _ e e' H).
    rewrite (IHt2 _ (extend n e) (extend n e')); [reflexivity|].
    intro x; unfold extend; rewrite H; reflexivity.
  - rewrite (IHt1 _ e e' H), (IHt2 _ e e' H); reflexivity.
  - rewrite (IHt1 _ e e' H).
    rewrite (IHt2 _ (extend n e) (extend n e')); [reflexivity|].
    intro x; unfold extend; rewrite H; reflexivity.
  - rewrite (IHt1 _ e e' H), (IHt2 _ e e' H); reflexivity.
  - reflexivity.
Qed.

Lemma extend_replace {m n} (rho : Fin m -> Term nat n) x e e' :
  (forall y, e' y = option_map (replace rho) (e y)) ->
  forall y, extend x e' y = option_map (replace (transpose rho)) (extend x e y).
Proof.
  intros H y; unfold extend; destruct (Nat.eqb y x).
  - reflexivity.
  - rewrite H; destruct (e y); cbn [option_map]; [rewrite replace_shift|]; reflexivity.
Qed.

Lemma evaluate_replace t : forall m n (rho : Fin m -> Term nat n) e e',
  (forall x, e' x = option_map (replace rho) (e x)) ->
  evaluate t e' = option_map (replace rho) (evaluate t e).
Proof.
  induction t; intros m k rho e e' H; cbn [evaluate].
  - reflexivity.
  - apply H.
  - rewrite (IHt1 _ _ rho _ _ H), (IHt2 _ _ (transpose rho) _ _ (extend_replace rho n e e' H)).
    destruct (evaluate t1 e), (evaluate t2 (extend n e)); reflexivity.
  - rewrite (IHt1 _ _ rho _ _ H), (IHt2 _ _ rho _ _ H).
    destruct (evaluate t1 e), (evaluate t2 e); cbn [option_map]; try reflexivity.
    rewrite replace_arrow; reflexivity.
  - rewrite (IHt1 _ _ rho _ _ H), (IHt2 _ _ (transpose rho) _ _ (extend_replace rho n e e' H)).
    destruct (evaluate t1 e), (evaluate t2 (extend n e)); reflexivity.
  - rewrite (IHt1 _ _ rho _ _ H), (IHt2 _ _ rho _ _ H).
    destruct (evaluate t1 e), (evaluate t2 e); reflexivity.
  - cbn [option_map]; rewrite replace_lift_closed; reflexivity.
Qed.

Definition names (xs : list nat) : environment (length xs) :=
  fun x => option_map (fun i => var i) (lookup xs x).
Lemma names_extend x xs y : names (x :: xs) y = extend x (names xs) y.
Proof.
  unfold names, extend; cbn [lookup]. destruct (Nat.eqb y x); [reflexivity|].
  destruct (lookup xs y); reflexivity.
Qed.
Lemma assemble_evaluate t : forall xs, assemble t xs = evaluate t (names xs).
Proof.
  induction t; intro xs; cbn [assemble evaluate].
  - reflexivity.
  - unfold names; destruct (lookup xs n); reflexivity.
  - rewrite IHt1, IHt2.
    rewrite (evaluate_ext t2 _ (names (n :: xs)) (extend n (names xs)) (names_extend n xs)).
    reflexivity.
  - rewrite IHt1, IHt2; destruct (evaluate t1 (names xs)), (evaluate t2 (names xs)); reflexivity.
  - rewrite IHt1, IHt2.
    rewrite (evaluate_ext t2 _ (names (n :: xs)) (extend n (names xs)) (names_extend n xs)).
    reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
  - reflexivity.
Qed.
Lemma close_evaluate t ok : evaluate t (names []) = Some (close t ok).
Proof.
  rewrite <- assemble_evaluate. unfold close. unfold closedb in ok.
  destruct (assemble t []); [reflexivity|discriminate ok].
Qed.

Definition singleton (x : nat) (u : closed_term) : environment 0 :=
  fun y => if Nat.eqb y x then Some u else None.
Lemma evaluate_subst t x u body :
  assemble t [x] = Some body ->
  evaluate t (singleton x u) = Some (subst body u).
Proof.
  intro H; rewrite assemble_evaluate in H.
  assert (E : forall y, singleton x u y =
    option_map (replace (fin_match u (fun i => var i))) (names [x] y)).
  { intro y; unfold names, singleton; cbn [lookup].
    destruct (Nat.eqb y x); reflexivity. }
  pose proof (evaluate_replace t 1 0 (fin_match u (fun i => var i))
    (names [x]) (singleton x u) E) as K.
  exact (eq_trans K (f_equal (option_map (replace (fin_match u (fun i => var i)))) H)).
Qed.

Definition update {n} (e : environment n) x (u : Term nat n) : environment n :=
  fun y => if Nat.eqb y x then Some u else e y.
Fixpoint substitute_named x (c : closed_term) (t : named) : named :=
  match t with
  | NSort r => NSort r
  | NClosed d => NClosed d
  | NVar y => if Nat.eqb y x then NClosed c else NVar y
  | NPi y a b => NPi y (substitute_named x c a)
      (if Nat.eqb y x then b else substitute_named x c b)
  | NArrow a b => NArrow (substitute_named x c a) (substitute_named x c b)
  | NLam y a b => NLam y (substitute_named x c a)
      (if Nat.eqb y x then b else substitute_named x c b)
  | NApp a b => NApp (substitute_named x c a) (substitute_named x c b)
  end.
Lemma extend_update_same {n} x (e : environment n) u y :
  extend x (update e x u) y = extend x e y.
Proof. unfold extend, update; destruct (Nat.eqb y x); reflexivity. Qed.
Lemma extend_update_other {n} x z (e : environment n) c :
  x <> z -> forall y,
  extend z (update e x (lift_closed c)) y =
  update (extend z e) x (lift_closed c) y.
Proof.
  intros H y; unfold extend, update.
  destruct (Nat.eqb y z) eqn:E, (Nat.eqb y x) eqn:F; cbn [option_map].
  - apply Nat.eqb_eq in E, F; subst; contradiction.
  - reflexivity.
  - rewrite lift_closed_shift; reflexivity.
  - reflexivity.
Qed.
Lemma evaluate_substitute_named t : forall n x c (e : environment n),
  evaluate (substitute_named x c t) e =
  evaluate t (update e x (lift_closed c)).
Proof.
  induction t; intros k x c e; cbn [substitute_named evaluate].
  - reflexivity.
  - unfold update; destruct (Nat.eqb n x); reflexivity.
  - rewrite IHt1. destruct (Nat.eqb n x) eqn:E.
    + apply Nat.eqb_eq in E; subst n.
      rewrite (evaluate_ext t2 _ (extend x (update e x (lift_closed c)))
        (extend x e) (extend_update_same x e (lift_closed c))); reflexivity.
    + rewrite IHt2. apply Nat.eqb_neq in E.
      rewrite (evaluate_ext t2 _ (extend n (update e x (lift_closed c)))
        (update (extend n e) x (lift_closed c)) (extend_update_other x n e c (not_eq_sym E))).
      reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
  - rewrite IHt1. destruct (Nat.eqb n x) eqn:E.
    + apply Nat.eqb_eq in E; subst n.
      rewrite (evaluate_ext t2 _ (extend x (update e x (lift_closed c)))
        (extend x e) (extend_update_same x e (lift_closed c))); reflexivity.
    + rewrite IHt2. apply Nat.eqb_neq in E.
      rewrite (evaluate_ext t2 _ (extend n (update e x (lift_closed c)))
        (update (extend n e) x (lift_closed c)) (extend_update_other x n e c (not_eq_sym E))).
      reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
  - reflexivity.
Qed.
Lemma assembled_substitution t x c body result :
  assemble t [x] = Some body ->
  assemble (substitute_named x c t) [] = Some result ->
  subst body c = result.
Proof.
  intros Hbody Hresult.
  pose proof (evaluate_subst t x c body Hbody) as H.
  rewrite assemble_evaluate, evaluate_substitute_named in Hresult.
  assert (E : evaluate t (update (names []) x (lift_closed c)) =
    evaluate t (singleton x c)).
  { apply evaluate_ext; intro y; unfold update, names, singleton.
    rewrite lift_closed_zero; destruct (Nat.eqb y x); reflexivity. }
  exact (f_equal (fun z => match z with Some v => v | None => c end)
    (eq_trans (eq_sym H) (eq_trans (eq_sym E) Hresult))).
Qed.

Lemma extend_preserves {m n} (rho : Fin m -> Term nat n) x e e' :
  (forall y a, e y = Some a -> e' y = Some (replace rho a)) ->
  forall y a, extend x e y = Some a ->
    extend x e' y = Some (replace (transpose rho) a).
Proof.
  intros H y a; unfold extend; destruct (Nat.eqb y x).
  - intro K; injection K as <-; reflexivity.
  - destruct (e y) as [b|] eqn:E; cbn [option_map]; [|discriminate].
    intro K; injection K as <-; rewrite (H y b E).
    cbn [option_map]; rewrite replace_shift; reflexivity.
Qed.

Lemma evaluate_preserves t : forall m n (rho : Fin m -> Term nat n) e e' u,
  (forall x a, e x = Some a -> e' x = Some (replace rho a)) ->
  evaluate t e = Some u -> evaluate t e' = Some (replace rho u).
Proof.
  induction t; intros m k rho e e' u H K; cbn [evaluate] in K |- *.
  - injection K as <-; reflexivity.
  - exact (H n u K).
  - destruct (evaluate t1 e) as [a|] eqn:Ea; [|discriminate].
    destruct (evaluate t2 (extend n e)) as [b|] eqn:Eb; [|discriminate].
    injection K as <-.
    rewrite (IHt1 _ _ rho e e' a H Ea).
    rewrite (IHt2 _ _ (transpose rho) (extend n e) (extend n e') b
      (extend_preserves rho n e e' H) Eb); reflexivity.
  - destruct (evaluate t1 e) as [a|] eqn:Ea; [|discriminate].
    destruct (evaluate t2 e) as [b|] eqn:Eb; [|discriminate].
    injection K as <-.
    rewrite (IHt1 _ _ rho e e' a H Ea), (IHt2 _ _ rho e e' b H Eb).
    rewrite replace_arrow; reflexivity.
  - destruct (evaluate t1 e) as [a|] eqn:Ea; [|discriminate].
    destruct (evaluate t2 (extend n e)) as [b|] eqn:Eb; [|discriminate].
    injection K as <-.
    rewrite (IHt1 _ _ rho e e' a H Ea).
    rewrite (IHt2 _ _ (transpose rho) (extend n e) (extend n e') b
      (extend_preserves rho n e e' H) Eb); reflexivity.
  - destruct (evaluate t1 e) as [a|] eqn:Ea; [|discriminate].
    destruct (evaluate t2 e) as [b|] eqn:Eb; [|discriminate].
    injection K as <-.
    rewrite (IHt1 _ _ rho e e' a H Ea), (IHt2 _ _ rho e e' b H Eb); reflexivity.
  - injection K as <-; rewrite replace_lift_closed; reflexivity.
Qed.

Lemma evaluate_closed t u :
  assemble t [] = Some u ->
  forall n (e : environment n), evaluate t e = Some (lift_closed u).
Proof.
  intros H n e; rewrite assemble_evaluate in H.
  pose proof (evaluate_preserves t 0 n
    (fun i => var (@empty_renaming n i)) (names []) e u) as E.
  assert (P : forall x a, names [] x = Some a ->
    e x = Some (replace (fun i => var (@empty_renaming n i)) a)).
  { intros x a K; discriminate K. }
  specialize (E P H).
  rewrite <- rename_as_replace in E; exact E.
Qed.
Lemma evaluate_close t ok : forall n (e : environment n),
  evaluate t e = Some (lift_closed (close t ok)).
Proof.
  apply evaluate_closed; rewrite assemble_evaluate; apply close_evaluate.
Qed.

Fixpoint plug x r t :=
  match t with
  | NSort k => NSort k | NClosed c => NClosed c
  | NVar y => if Nat.eqb y x then r else NVar y
  | NPi y a b => NPi y (plug x r a) (if Nat.eqb y x then b else plug x r b)
  | NArrow a b => NArrow (plug x r a) (plug x r b)
  | NLam y a b => NLam y (plug x r a) (if Nat.eqb y x then b else plug x r b)
  | NApp a b => NApp (plug x r a) (plug x r b)
  end.
Lemma plug_congruence t : forall x r s,
  (forall n (e : environment n), evaluate r e = evaluate s e) ->
  forall n (e : environment n), evaluate (plug x r t) e = evaluate (plug x s t) e.
Proof.
  induction t; intros x r s H k e; cbn [plug evaluate].
  - reflexivity.
  - destruct (Nat.eqb n x); [apply H|reflexivity].
  - rewrite (IHt1 x r s H). destruct (Nat.eqb n x); [reflexivity|].
    rewrite (IHt2 x r s H); reflexivity.
  - rewrite (IHt1 x r s H), (IHt2 x r s H); reflexivity.
  - rewrite (IHt1 x r s H). destruct (Nat.eqb n x); [reflexivity|].
    rewrite (IHt2 x r s H); reflexivity.
  - rewrite (IHt1 x r s H), (IHt2 x r s H); reflexivity.
  - reflexivity.
Qed.

End NamedTemplates.

