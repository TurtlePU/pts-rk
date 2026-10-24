From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From PTSrk.Combinatory Require Import ChurchFinite.
Import ListNotations.

(** Independent finite Horn proof types in the ORIGINAL annotated PTS.
    One type variable X_a : U_1 is quantified for each finite atom.  A rule
    contributes its curried implication; the final result is X_query.
    No semantic truth table, model, source derivation or desired conclusion
    is built into the type.  Elimination below applies to every native term
    of this Church type, not just terms emitted from external proof trees. *)
Module HornProofEncoding.
Module CF := ChurchFinite.ChurchFinite.

Definition Clause k := (list (Fin k) * Fin k)%type.

Fixpoint rule_type {k n} (ps : list (Fin k)) (a : Fin k)
  (env : Fin k -> Term nat n) : Term nat n :=
  match ps with
  | [] => env a
  | b :: rest => Π (env b) (rule_type rest a (fun i => shift (env i)))
  end.
Definition rule_rank {k} (ps : list (Fin k)) :=
  match ps with [] => 1 | _ :: _ => 2 end.

Fixpoint matrix {k n} (clauses : list (Clause k)) (a : Fin k)
  (env : Fin k -> Term nat n) : Term nat n :=
  match clauses with
  | [] => env a
  | (ps, b) :: rest =>
      Π (rule_type ps b env) (matrix rest a (fun i => shift (env i)))
  end.
Fixpoint matrix_rank {k} (clauses : list (Clause k)) :=
  match clauses with
  | [] => 1
  | (ps, _) :: rest => Nat.max (S (rule_rank ps)) (matrix_rank rest)
  end.

Fixpoint forall_types (k : nat) {n} : Term nat (CF.scope k n) -> Term nat n :=
  match k with
  | 0 => fun body => body
  | S j => fun body => Π (𝓤 1) (forall_types j body)
  end.
Definition proof_type {n} k (clauses : list (Clause k)) (a : Fin k)
  : Term nat n := forall_types k (matrix clauses a (@CF.branch k n)).
Definition specialize {n} k (p : Term nat n) (values : Fin k -> Term nat n)
  : Term nat n := CF.apps k p values.

Lemma rule_type_ext k ps a n (env env' : Fin k -> Term nat n) :
  (forall i, env i = env' i) -> rule_type ps a env = rule_type ps a env'.
Proof.
  revert n env env'; induction ps; intros n env env' H;
    cbn [rule_type]; [apply H |].
  rewrite H; f_equal; apply IHps; intro i; now rewrite H.
Qed.
Lemma rule_type_replace k ps a : forall m n (sigma : Fin m -> Term nat n)
  (env : Fin k -> Term nat m),
  replace sigma (rule_type ps a env) =
  rule_type ps a (fun i => replace sigma (env i)).
Proof.
  induction ps; intros; cbn [rule_type replace]; [reflexivity |].
  rewrite IHps; f_equal; apply rule_type_ext; intro i; apply CF.replace_shift.
Qed.
Lemma rule_type_rename k ps a m n (rho : Fin m -> Fin n)
  (env : Fin k -> Term nat m) :
  rename rho (rule_type ps a env) = rule_type ps a (fun i => rename rho (env i)).
Proof.
  rewrite <- (replace_var (rule_type ps a env)) at 1.
  rewrite rename_replace, rule_type_replace; apply rule_type_ext; intro i.
  rewrite <- rename_replace, replace_var; reflexivity.
Qed.
Lemma rule_type_sorted k ps a : forall n (G : Ctx nat n)
  (env : Fin k -> Term nat n),
  (forall i, @typ nat RankSorts n G (env i) (𝓤 1)) ->
  @typ nat RankSorts n G (rule_type ps a env) (𝓤 (rule_rank ps)).
Proof.
  induction ps; intros n G env HE; cbn [rule_type rule_rank]; [apply HE |].
  eapply typ_Π with (ℓₜ := 1) (ℓᵤ := rule_rank ps).
  - apply HE.
  - apply IHps; intro i.
    change (typ (G & env a0) (shift (env i)) (shift (𝓤 1))).
    apply weakening, HE.
  - destruct ps; reflexivity.
Qed.
Lemma matrix_ext k clauses a n (env env' : Fin k -> Term nat n) :
  (forall i, env i = env' i) -> matrix clauses a env = matrix clauses a env'.
Proof.
  revert n env env'; induction clauses as [|[ps b] rest IH]; intros n env env' H;
    cbn [matrix]; [apply H |].
  f_equal; [apply rule_type_ext, H | apply IH; intro i; now rewrite H].
Qed.
Lemma matrix_replace k clauses a : forall m n (sigma : Fin m -> Term nat n)
  (env : Fin k -> Term nat m),
  replace sigma (matrix clauses a env) =
  matrix clauses a (fun i => replace sigma (env i)).
Proof.
  induction clauses as [|[ps b] rest IH]; intros; cbn [matrix replace];
    [reflexivity |].
  rewrite rule_type_replace, IH; f_equal; apply matrix_ext; intro i;
    apply CF.replace_shift.
Qed.
Lemma matrix_rename k clauses a m n (rho : Fin m -> Fin n)
  (env : Fin k -> Term nat m) :
  rename rho (matrix clauses a env) = matrix clauses a (fun i => rename rho (env i)).
Proof.
  rewrite <- (replace_var (matrix clauses a env)) at 1.
  rewrite rename_replace, matrix_replace; apply matrix_ext; intro i.
  rewrite <- rename_replace, replace_var; reflexivity.
Qed.
Lemma matrix_rank_bounds k (clauses : list (Clause k)) :
  1 <= matrix_rank clauses <= 3.
Proof.
  induction clauses as [|[ps b] rest IH]; cbn [matrix_rank]; [lia |].
  destruct ps; cbn [rule_rank]; lia.
Qed.
Lemma matrix_sorted k clauses a : forall n (G : Ctx nat n)
  (env : Fin k -> Term nat n),
  (forall i, @typ nat RankSorts n G (env i) (𝓤 1)) ->
  @typ nat RankSorts n G (matrix clauses a env) (𝓤 (matrix_rank clauses)).
Proof.
  induction clauses as [|[ps b] rest IH]; intros n G env HE;
    cbn [matrix matrix_rank]; [apply HE |].
  eapply typ_Π; [apply rule_type_sorted, HE | | reflexivity].
  apply IH; intro i; change
    (typ (G & rule_type ps b env) (shift (env i)) (shift (𝓤 1))).
  apply weakening, HE.
Qed.

Lemma forall_types_replace k : forall m n (sigma : Fin m -> Term nat n) body,
  replace sigma (forall_types k body) =
  forall_types k (replace (CF.under k sigma) body).
Proof.
  induction k; intros; cbn [forall_types replace CF.under]; [reflexivity |].
  now rewrite IHk.
Qed.
Lemma forall_types_sorted k : forall n (G : Ctx nat n) body r,
  1 <= r ->
  @typ nat RankSorts (CF.scope k n) (CF.telescope k G (𝓤 1)) body (𝓤 r) ->
  @typ nat RankSorts n G (forall_types k body) (𝓤 r).
Proof.
  induction k; intros n G body r Hr HB; cbn [forall_types]; [exact HB |].
  eapply typ_Π with (ℓₜ := 0) (ℓᵤ := r).
  - constructor; reflexivity.
  - apply IHk; assumption.
  - change (r = Nat.max 1 r); lia.
Qed.
Lemma forall_types_bind_typed k : forall n (G : Ctx nat n) body B,
  @typ nat RankSorts (CF.scope k n) (CF.telescope k G (𝓤 1)) body B ->
  @typ nat RankSorts n G (CF.bind k (𝓤 1) body) (forall_types k B).
Proof.
  induction k; intros n G body B HB; cbn [CF.bind forall_types]; [exact HB |].
  eapply typ_λ with (ℓ := 0); [constructor; reflexivity |].
  apply IHk; exact HB.
Qed.

Theorem proof_type_replace k clauses a m n (sigma : Fin m -> Term nat n) :
  replace sigma (@proof_type m k clauses a) = @proof_type n k clauses a.
Proof.
  unfold proof_type; rewrite forall_types_replace, matrix_replace.
  f_equal; apply matrix_ext; intro i; apply CF.under_branch.
Qed.
Theorem proof_type_rename k clauses a m n (rho : Fin m -> Fin n) :
  rename rho (@proof_type m k clauses a) = @proof_type n k clauses a.
Proof.
  rewrite <- (replace_var (@proof_type m k clauses a)) at 1.
  rewrite rename_replace; apply proof_type_replace.
Qed.
Theorem proof_type_sorted {n} (G : Ctx nat n) k clauses a :
  @typ nat RankSorts n G (proof_type k clauses a) (𝓤 (matrix_rank clauses)).
Proof.
  unfold proof_type; apply forall_types_sorted.
  - apply matrix_rank_bounds.
  - apply matrix_sorted; intro i.
    rewrite <- (@CF.lift_sort k n 1); apply CF.branch_typed.
Qed.
Theorem proof_type_rank_bound k (clauses : list (Clause k)) :
  matrix_rank clauses <= 3.
Proof. apply matrix_rank_bounds. Qed.

(** Dependent specialization: the result is literal simultaneous replacement
    by the supplied atom types.  No exhaustiveness/canonicity assumption on
    the represented proof is used. *)
Lemma forall_types_apply_typed k : forall m n (G : Ctx nat n)
  (sigma : Fin m -> Term nat n) body p values,
  @typ nat RankSorts n G p (replace sigma (forall_types k body)) ->
  (forall i : Fin k, @typ nat RankSorts n G (values i) (𝓤 1)) ->
  @typ nat RankSorts n G (CF.apps k p values)
    (replace (CF.filling k sigma values) body).
Proof.
  induction k; intros m n G sigma body p values HP HV;
    cbn [CF.apps CF.filling forall_types replace] in *; [exact HP |].
  apply IHk; [|intro i; apply HV].
  rewrite <- CF.substituted_body.
  eapply typ_app; [exact HP | apply HV].
Qed.
Theorem specialize_typed {n} (G : Ctx nat n) k clauses a p values :
  @typ nat RankSorts n G p (proof_type k clauses a) ->
  (forall i : Fin k, @typ nat RankSorts n G (values i) (𝓤 1)) ->
  @typ nat RankSorts n G (specialize k p values) (matrix clauses a values).
Proof.
  intros HP HV; unfold specialize.
  assert (HE : replace (CF.filling k (fun i : Fin n => var i) values)
    (matrix clauses a (@CF.branch k n)) = matrix clauses a values).
  { rewrite matrix_replace; apply matrix_ext; intro i; apply CF.filling_branch. }
  rewrite <- HE; apply forall_types_apply_typed; [|exact HV].
  rewrite replace_var; exact HP.
Qed.

Print Assumptions rule_type_ext.
Print Assumptions rule_type_replace.
Print Assumptions rule_type_rename.
Print Assumptions rule_type_sorted.
Print Assumptions matrix_ext.
Print Assumptions matrix_replace.
Print Assumptions matrix_rename.
Print Assumptions matrix_rank_bounds.
Print Assumptions matrix_sorted.
Print Assumptions forall_types_replace.
Print Assumptions forall_types_sorted.
Print Assumptions forall_types_bind_typed.
Print Assumptions proof_type_replace.
Print Assumptions proof_type_rename.
Print Assumptions proof_type_sorted.
Print Assumptions proof_type_rank_bound.
Print Assumptions forall_types_apply_typed.
Print Assumptions specialize_typed.
End HornProofEncoding.
