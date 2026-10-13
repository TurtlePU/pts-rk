From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia.
From PTSrk Require Import -(notations) Syntax AbstractRewriting Congruence Reduction.

(** Bottom-up greedy parallel beta reduction, including lambda annotations. *)
Fixpoint greedy {n} (t : Term nat n) : Term nat n :=
  match t with
  | 𝓤 r => 𝓤 r | var i => var i
  | Π A B => Π (greedy A) (greedy B)
  | lam A b => lam (greedy A) (greedy b)
  | app f u =>
      let f' := greedy f in let u' := greedy u in
      match f' with lam _ b => subst b u' | _ => app f' u' end
  end.

Theorem greedy_sound {n} (t : Term nat n) : reduces_to nat n t (greedy t).
Proof.
  induction t; cbn [greedy]; unfold reduces_to in *.
  - constructor.
  - apply (Π_cong_par nat (fun n => RTC (step nat n))); assumption.
  - constructor.
  - apply (λ_cong_par nat (fun n => RTC (step nat n))); assumption.
  - eapply rtc_trans with (y := app (greedy t1) (greedy t2)).
    + apply (app_cong_par nat (fun n => RTC (step nat n))); assumption.
    + destruct (greedy t1); try constructor.
      apply rtc_in. constructor.
Qed.

Definition isLambda {n} (t : Term nat n) : bool :=
  match t with lam _ _ => true | _ => false end.
Fixpoint normalb {n} (t : Term nat n) : bool :=
  match t with
  | 𝓤 _ | var _ => true
  | Π A B | lam A B => normalb A && normalb B
  | app f u => (normalb f && normalb u) && negb (isLambda f)
  end.
Theorem normalb_sound {n} (t : Term nat n) :
  normalb t = true -> forall u, ~ step nat n t u.
Proof.
  intros Hnormal u Hstep. induction Hstep; cbn [normalb isLambda] in Hnormal;
    repeat rewrite andb_true_iff in Hnormal; intuition discriminate.
Qed.

Fixpoint rounds {n} (k : nat) (t : Term nat n) : Term nat n :=
  match k with 0 => t | S k => rounds k (greedy t) end.
Theorem rounds_sound {n} k (t : Term nat n) : reduces_to nat n t (rounds k t).
Proof.
  revert t; induction k; intro t; cbn [rounds].
  - constructor.
  - eapply rtc_trans; [apply greedy_sound | apply IHk].
Qed.

(** A total bounded attempt, not a total normalization theorem: None means
    that the supplied number of rounds has not established normality. *)
Definition normalizeWithin {n} (fuel : nat) (t : Term nat n) : option (Term nat n) :=
  let u := rounds fuel t in if normalb u then Some u else None.
Theorem normalizeWithin_sound {n} k (t u : Term nat n) :
  normalizeWithin k t = Some u ->
  reduces_to nat n t u /\ forall v, ~ step nat n u v.
Proof.
  unfold normalizeWithin. destruct (normalb (rounds k t)) eqn:Hnormal;
    intro H; inversion H; subst.
  split; [apply rounds_sound | apply normalb_sound; exact Hnormal].
Qed.
