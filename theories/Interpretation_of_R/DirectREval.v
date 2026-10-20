(** Fuel-bounded beta evaluation in the ORIGINAL scoped PTSrk syntax.

    Architecture adapted from clayrat/pts-dependent-types, PTS/Eval.v,
    commit 7e6282d357c6f42217a9584f6c7493c594ae1aed. The implementation
    below keeps domain annotations and uses PTSrk.Reduction.step.
    No second PTS syntax, primitive eliminators, or eta rule is introduced.

    STATUS: proof scripts supplied, not compiled in the authoring container.
    Only SUCCESS is given a conversion contract. Exhaustion is inconclusive.
*)
From Stdlib Require Import Arith.PeanoNat Bool.Bool.
From Equations Require Import Equations.
From PTSrk Require Import Syntax AbstractRewriting Reduction DefEq.

Module RkEval.
Unset Implicit Arguments.

Fixpoint fin_eqb {n m} (i : Fin n) (j : Fin m) : bool :=
  match i, j with
  | fzero, fzero => true
  | fsucc i', fsucc j' => fin_eqb i' j'
  | _, _ => false
  end.

Lemma fin_eqb_sound {n} (i j : Fin n) : fin_eqb i j = true -> i = j.
Proof.
  revert j. induction i; intros j H; dependent elimination j;
    cbn in H; try discriminate; f_equal; auto.
Qed.

(** The two scope indices may differ while comparing subtrees; soundness
    is used only for two terms at the same scope. *)
Fixpoint term_eqb {n m} (t : Term nat n) (u : Term nat m) : bool :=
  match t, u with
  | 𝓤 i, 𝓤 j => Nat.eqb i j
  | var i, var j => fin_eqb i j
  | Π A B, Π C D => term_eqb A C && term_eqb B D
  | lam A b, lam C d => term_eqb A C && term_eqb b d
  | app f a, app g b => term_eqb f g && term_eqb a b
  | _, _ => false
  end.

Lemma term_eqb_sound {n} (t u : Term nat n) :
  term_eqb t u = true -> t = u.
Proof.
  revert u. induction t; intros u H; dependent elimination u;
    cbn in H; try discriminate.
  all: repeat match goal with
       | H : _ && _ = true |- _ => apply andb_true_iff in H as [? ?]
       end.
  all: f_equal; first [apply Nat.eqb_eq | apply fin_eqb_sound |
                      apply IHt1 | apply IHt2]; assumption.
Qed.

(** Inspect only the head. In particular, do not reduce a beta argument
    before substituting it. *)
Fixpoint head_step {n} (t : Term nat n) : option (Term nat n) :=
  match t with
  | app f a =>
      match f with
      | lam A b => Some (b ◁ a)
      | _ => option_map (fun f' => app f' a) (head_step f)
      end
  | _ => None
  end.

(** Leftmost outermost full beta step. Unlike the lab's unannotated Lam,
    an inactive lambda here still contains an annotation which is scanned.
    A root beta contraction discards an unused annotation as usual. *)
Fixpoint normal_step {n} (t : Term nat n) : option (Term nat n) :=
  match t with
  | 𝓤 _ | var _ => None
  | Π A B =>
      match normal_step A with
      | Some A' => Some (Π A' B)
      | None => option_map (Π A) (normal_step B)
      end
  | lam A b =>
      match normal_step A with
      | Some A' => Some (lam A' b)
      | None => option_map (lam A) (normal_step b)
      end
  | app f a =>
      match f with
      | lam A b => Some (b ◁ a)
      | _ =>
          match normal_step f with
          | Some f' => Some (app f' a)
          | None => option_map (app f) (normal_step a)
          end
      end
  end.

Lemma head_step_sound {n} (t u : Term nat n) :
  head_step t = Some u -> t →ᵝ u.
Proof.
  revert u. induction t; intros u H; cbn [head_step] in H;
    try discriminate.
  destruct t1; cbn [head_step] in H;
    try discriminate;
    repeat match type of H with
    | context [option_map _ ?v] =>
        destruct v eqn:?; cbn in H; try discriminate
    | context [match ?v with Some _ => _ | None => _ end] =>
        destruct v eqn:?; cbn in H; try discriminate
    end;
    inversion H; subst; eauto using step_beta, step_app_left.
Qed.

Lemma normal_step_sound {n} (t u : Term nat n) :
  normal_step t = Some u -> t →ᵝ u.
Proof.
  revert u. induction t; intros u H; cbn [normal_step] in H;
    try discriminate.
  - destruct (normal_step t1) eqn:E1; cbn in H.
    + inversion H; subst. apply step_pi_left. now apply IHt1.
    + destruct (normal_step t2) eqn:E2; cbn in H; try discriminate.
      inversion H; subst. apply step_pi_right. now apply IHt2.
  - destruct (normal_step t1) eqn:E1; cbn in H.
    + inversion H; subst. apply step_lam_left. now apply IHt1.
    + destruct (normal_step t2) eqn:E2; cbn in H; try discriminate.
      inversion H; subst. apply step_lam_right. now apply IHt2.
  - destruct t1; try (inversion H; subst; apply step_beta).
    all: match goal with
    | |- app ?f ?a →ᵝ _ =>
        change (match normal_step f with
                | Some f' => Some (app f' a)
                | None => option_map (app f) (normal_step a)
                end = Some u) in H;
        destruct (normal_step f) as [f'|] eqn:E1; cbn in H;
        [ inversion H; subst; apply step_app_left; now apply IHt1
        | destruct (normal_step a) as [a'|] eqn:E2; cbn in H;
          try discriminate; inversion H; subst;
          apply step_app_right; now apply IHt2 ]
    end.
Qed.

Inductive eval_result (n : nat) : Type :=
| Finished : Term nat n -> eval_result n
| Exhausted : Term nat n -> eval_result n.
Arguments Finished {n} _.
Arguments Exhausted {n} _.

Definition endpoint {n} (r : eval_result n) : Term nat n :=
  match r with Finished u | Exhausted u => u end.

Fixpoint run_steps {n}
    (next : Term nat n -> option (Term nat n))
    (fuel : nat) (t : Term nat n) : eval_result n :=
  match next t with
  | None => Finished t
  | Some u =>
      match fuel with
      | 0 => Exhausted t
      | S fuel' => run_steps next fuel' u
      end
  end.

Lemma run_steps_sound {n}
    (next : Term nat n -> option (Term nat n))
    (next_sound : forall t u, next t = Some u -> t →ᵝ u)
    fuel t : t ↠ᵝ endpoint (run_steps next fuel t).
Proof.
  revert t. induction fuel as [|fuel IH]; intros t;
    cbn [run_steps]; destruct (next t) as [u|] eqn:E;
    cbn [endpoint]; try reflexivity.
  eapply rtc_step; [exact (next_sound t u E) | apply IH].
Qed.

Definition whnf {n} fuel (t : Term nat n) := run_steps head_step fuel t.
Definition normalize {n} fuel (t : Term nat n) := run_steps normal_step fuel t.

Lemma whnf_sound {n} fuel (t u : Term nat n) :
  whnf fuel t = Finished u -> t ↠ᵝ u.
Proof.
  intro H. pose proof (run_steps_sound head_step (@head_step_sound n) fuel t) as E.
  unfold whnf in H. rewrite H in E. exact E.
Qed.
Lemma normalize_sound {n} fuel (t u : Term nat n) :
  normalize fuel t = Finished u -> t ↠ᵝ u.
Proof.
  intro H. pose proof (run_steps_sound normal_step (@normal_step_sound n) fuel t) as E.
  unfold normalize in H. rewrite H in E. exact E.
Qed.
Lemma reduction_equiv {n} (t u : Term nat n) : t ↠ᵝ u -> t =ᵝ u.
Proof. intro H. apply def_equiv_prop. exists u. split; [exact H | reflexivity]. Qed.

Inductive conv_result : Type := ConvEqual | ConvDifferent | ConvOutOfFuel.

Definition convert {n} fuel (A B : Term nat n) : conv_result :=
  if term_eqb A B then ConvEqual else
  match normalize fuel A, normalize fuel B with
  | Finished A', Finished B' =>
      if term_eqb A' B' then ConvEqual else ConvDifferent
  | _, _ => ConvOutOfFuel
  end.

(** This is the only contract used by typing. No negative or completeness
    theorem for the checker is assumed. *)
Theorem convert_equal_sound {n} fuel (A B : Term nat n) :
  convert fuel A B = ConvEqual -> A =ᵝ B.
Proof.
  unfold convert. destruct (term_eqb A B) eqn:E.
  - intros _. apply term_eqb_sound in E. subst B. reflexivity.
  - destruct (normalize fuel A) as [A'|A'] eqn:HA;
      destruct (normalize fuel B) as [B'|B'] eqn:HB; try discriminate.
    destruct (term_eqb A' B') eqn:EC; try discriminate.
    intros _. apply term_eqb_sound in EC. subst B'.
    apply def_equiv_prop. exists A'. split;
      eapply normalize_sound; eassumption.
Qed.
End RkEval.
