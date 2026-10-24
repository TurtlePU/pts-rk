(** Relabel sort literals without changing variable scope or annotations. *)
From Stdlib Require Import Lists.List Bool.Bool.
From Equations Require Import Equations.
From PTSrk Require Import Syntax Context Reduction DefEq AbstractRewriting.
From PTSrk.SelfConsistency Require Import NativeProofCodes CertificateAdequacy.
Import NativeProofCodes.NativeProofCodes.

Fixpoint relabel (rho : nat -> nat) {n} (t : Term nat n) : Term nat n :=
  match t with
  | 𝓤 r => 𝓤 (rho r) | var i => var i
  | Π A B => Π (relabel rho A) (relabel rho B)
  | lam A b => lam (relabel rho A) (relabel rho b)
  | app f u => app (relabel rho f) (relabel rho u)
  end.

Lemma relabel_rename rho {m n} (f : Fin m -> Fin n) (t : Term nat m) :
  relabel rho (rename f t) = rename f (relabel rho t).
Proof. revert n f; induction t; intros; cbn; f_equal; auto. Qed.

Lemma relabel_replace rho {m n} (f : Fin m -> Term nat n) (t : Term nat m) :
  relabel rho (replace f t) = replace (fun i => relabel rho (f i)) (relabel rho t).
Proof.
  revert n f; induction t; intros; cbn; f_equal; auto;
    rewrite IHt2; apply replace_ext; intro i; dependent elimination i;
    cbn; try reflexivity; apply relabel_rename.
Qed.

Lemma relabel_subst rho {n} (t : Term nat (S n)) u :
  relabel rho (subst t u) = subst (relabel rho t) (relabel rho u).
Proof.
  unfold subst; rewrite relabel_replace; apply replace_ext;
    intro i; dependent elimination i; reflexivity.
Qed.

Fixpoint relabel_context rho {n} (G : Ctx nat n) : Ctx nat n :=
  match G with ε => ε | G & A => relabel_context rho G & relabel rho A end.

Lemma relabel_index rho {n} (G : Ctx nat n) i :
  relabel rho (G !! i) = relabel_context rho G !! i.
Proof.
  induction G; dependent elimination i; cbn; unfold shift;
    rewrite relabel_rename; f_equal; auto.
Qed.

Theorem relabel_step rho {n} (t u : Term nat n) :
  step nat n t u -> step nat n (relabel rho t) (relabel rho u).
Proof.
  intro H; induction H; cbn; try (constructor; assumption).
  rewrite relabel_subst; constructor.
Qed.

Theorem relabel_conversion rho {n} (t u : Term nat n) :
  t =ᵝ u -> relabel rho t =ᵝ relabel rho u.
Proof.
  intro H; induction H; [reflexivity |].
  transitivity (relabel rho y); [|assumption].
  destruct H; [apply eq_in | symmetry; apply eq_in]; apply relabel_step; assumption.
Qed.

Fixpoint relabel_step_code rho {n} (p : StepCode n) : StepCode n :=
  match p with
  | Contract A b u => Contract (relabel rho A) (relabel rho b) (relabel rho u)
  | PiLeft p B => PiLeft (relabel_step_code rho p) (relabel rho B)
  | PiRight A p => PiRight (relabel rho A) (relabel_step_code rho p)
  | LamLeft p b => LamLeft (relabel_step_code rho p) (relabel rho b)
  | LamRight A p => LamRight (relabel rho A) (relabel_step_code rho p)
  | AppLeft p u => AppLeft (relabel_step_code rho p) (relabel rho u)
  | AppRight f p => AppRight (relabel rho f) (relabel_step_code rho p)
  end.

Lemma relabel_step_endpoints rho {n} (p : StepCode n) :
  step_source (relabel_step_code rho p) = relabel rho (step_source p) /\
  step_target (relabel_step_code rho p) = relabel rho (step_target p).
Proof.
  induction p; cbn; try destruct IHp as [E F];
    split; try rewrite E; try rewrite F; try reflexivity.
  symmetry; apply relabel_subst.
Qed.

Fixpoint relabel_equality rho {n} (p : EqualityCode n) : EqualityCode n :=
  match p with
  | Refl t => Refl (relabel rho t)
  | Reduce p => Reduce (relabel_step_code rho p)
  | Symmetry p => Symmetry (relabel_equality rho p)
  | Transitivity p q => Transitivity (relabel_equality rho p) (relabel_equality rho q)
  end.

Lemma relabel_equality_endpoints rho {n} (p : EqualityCode n) :
  equality_source (relabel_equality rho p) = relabel rho (equality_source p) /\
  equality_target (relabel_equality rho p) = relabel rho (equality_target p).
Proof.
  induction p; cbn; try tauto.
  - apply relabel_step_endpoints.
Qed.

Theorem relabel_equality_check rho {n} (p : EqualityCode n) :
  equality_check p = true -> equality_check (relabel_equality rho p) = true.
Proof.
  induction p; cbn; auto; intro H.
  repeat rewrite andb_true_iff in H |- *.
  destruct H as [[Hp Hq] E]; apply term_eqb_correct in E.
  repeat split; auto; apply term_eqb_correct.
  rewrite (proj2 (relabel_equality_endpoints rho p1)),
    (proj1 (relabel_equality_endpoints rho p2)), E; reflexivity.
Qed.

Lemma relabel_bottom rho : rho 0 = 0 -> relabel rho Bottom = Bottom.
Proof. intro H; unfold Bottom; cbn; rewrite H; reflexivity. Qed.

Fixpoint relabel_certificate rho {n} (p : Certificate n) : Certificate n :=
  match p with
  | SortRule r => SortRule (rho r)
  | VariableRule i A => VariableRule i (relabel rho A)
  | ProductRule A B a b p q => ProductRule (relabel rho A) (relabel rho B)
      (rho a) (rho b) (relabel_certificate rho p) (relabel_certificate rho q)
  | AbstractionRule A t B r p q => AbstractionRule
      (relabel rho A) (relabel rho t) (relabel rho B) (rho r)
      (relabel_certificate rho p) (relabel_certificate rho q)
  | ApplicationRule f u A B p q => ApplicationRule
      (relabel rho f) (relabel rho u) (relabel rho A) (relabel rho B)
      (relabel_certificate rho p) (relabel_certificate rho q)
  | ConversionRule t A B r p q e => ConversionRule
      (relabel rho t) (relabel rho A) (relabel rho B) (rho r)
      (relabel_certificate rho p) (relabel_certificate rho q) (relabel_equality rho e)
  end.

(** Only equations actually used by the finite tree are required. *)
Fixpoint products_respected rho {n} (p : Certificate n) : Prop :=
  match p with
  | SortRule _ | VariableRule _ _ => True
  | ProductRule A B a b p q =>
      rho (Nat.max (S a) b) = Nat.max (S (rho a)) (rho b) /\
      products_respected rho p /\ products_respected rho q
  | AbstractionRule _ _ _ _ p q | ApplicationRule _ _ _ _ p q |
    ConversionRule _ _ _ _ p q _ => products_respected rho p /\ products_respected rho q
  end.

Lemma relabel_subject rho {n} (p : Certificate n) :
  subject (relabel_certificate rho p) = relabel rho (subject p).
Proof. destruct p; reflexivity. Qed.

Lemma relabel_type rho {n} (p : Certificate n) :
  rho 0 = 0 -> products_respected rho p ->
  type (relabel_certificate rho p) = relabel rho (type p).
Proof.
  intros E H; destruct p; cbn in *; try reflexivity.
  - rewrite E; reflexivity.
  - destruct H as [H _]; rewrite H; reflexivity.
  - symmetry; apply relabel_subst.
Qed.

Lemma relabel_matches rho {n} (p : Certificate n) t A :
  rho 0 = 0 -> products_respected rho p -> matchesb p t A = true ->
  matchesb (relabel_certificate rho p) (relabel rho t) (relabel rho A) = true.
Proof.
  intros E H M; apply matchesb_correct in M; destruct M as [Mt MA].
  apply matchesb_correct; unfold matches; rewrite relabel_subject, relabel_type by assumption.
  rewrite Mt, MA; auto.
Qed.

Theorem relabel_certificate_check rho {n} (p : Certificate n) :
  rho 0 = 0 -> products_respected rho p -> forall G,
  check G p = true -> check (relabel_context rho G) (relabel_certificate rho p) = true.
Proof.
  intros E; induction p; intros H G C; cbn [check relabel_certificate] in C |- *;
    cbn [products_respected] in H.
  - reflexivity.
  - apply term_eqb_correct in C; apply term_eqb_correct.
    rewrite <- relabel_index, C; reflexivity.
  - destruct H as [Hr [Hp Hq]].
    repeat rewrite andb_true_iff in C |- *; destruct C as [[[Cp Cq] Mp] Mq].
    repeat split; try (apply IHp1; assumption); try (apply IHp2; assumption);
      try exact (IHp2 Hq (G & t) Cq);
      first [exact (relabel_matches rho p1 _ _ E Hp Mp) |
        exact (relabel_matches rho p2 _ _ E Hq Mq)].
  - destruct H as [Hp Hq].
    repeat rewrite andb_true_iff in C |- *; destruct C as [[[Cp Cq] Mp] Mq].
    repeat split; try (apply IHp1; assumption); try (apply IHp2; assumption);
      try exact (IHp2 Hq (G & t) Cq);
      first [exact (relabel_matches rho p1 _ _ E Hp Mp) |
        exact (relabel_matches rho p2 _ _ E Hq Mq)].
  - destruct H as [Hp Hq].
    repeat rewrite andb_true_iff in C |- *; destruct C as [[[Cp Cq] Mp] Mq].
    repeat split; try (apply IHp1; assumption); try (apply IHp2; assumption);
      first [exact (relabel_matches rho p1 _ _ E Hp Mp) |
        exact (relabel_matches rho p2 _ _ E Hq Mq)].
  - destruct H as [Hp Hq].
    repeat rewrite andb_true_iff in C |- *.
    destruct C as [[[[[[Cp Cq] Mp] Mq] Ce] Es] Et].
    repeat split; try (apply IHp1; assumption); try (apply IHp2; assumption).
    + exact (relabel_matches rho p1 _ _ E Hp Mp).
    + exact (relabel_matches rho p2 _ _ E Hq Mq).
    + apply relabel_equality_check; assumption.
    + apply term_eqb_correct in Es; apply term_eqb_correct.
      rewrite (proj1 (relabel_equality_endpoints rho e)), Es; reflexivity.
    + apply term_eqb_correct in Et; apply term_eqb_correct.
      rewrite (proj2 (relabel_equality_endpoints rho e)), Et; reflexivity.
Qed.

Fixpoint relabel_context_code rho {n} (c : ContextCode n) : ContextCode n :=
  match c with
  | EmptyContext => EmptyContext
  | ExtendContext c r p => ExtendContext (relabel_context_code rho c)
      (rho r) (relabel_certificate rho p)
  end.

Lemma relabel_context_code_decode rho {n} (c : ContextCode n) :
  context (relabel_context_code rho c) = relabel_context rho (context c).
Proof. induction c; cbn; [reflexivity | rewrite IHc, relabel_subject; reflexivity]. Qed.

Fixpoint context_products_respected rho {n} (c : ContextCode n) : Prop :=
  match c with
  | EmptyContext => True
  | ExtendContext c r p => context_products_respected rho c /\ products_respected rho p
  end.

Theorem relabel_context_check rho {n} (c : ContextCode n) :
  rho 0 = 0 -> context_products_respected rho c -> context_check c = true ->
  context_check (relabel_context_code rho c) = true.
Proof.
  intros E; induction c; cbn [context_products_respected context_check relabel_context_code];
    intros H C; [reflexivity |].
  destruct H as [Hc Hp]; repeat rewrite Bool.andb_true_iff in C |- *.
  destruct C as [[Cc Cp] T]; repeat split.
  - apply IHc; assumption.
  - rewrite relabel_context_code_decode; apply relabel_certificate_check; assumption.
  - apply term_eqb_correct in T; apply term_eqb_correct.
    rewrite relabel_type by assumption; rewrite T; reflexivity.
Qed.
