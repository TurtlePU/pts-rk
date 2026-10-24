From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From PTSrk.Combinatory Require Import ChurchFinite HornProofEncoding.
Import ListNotations.

(** An internally indexed Church encoding of a fixed finite Horn theory.
    The query is an arbitrary ORIGINAL PTS term of the atom-code type.
    Its motive ranges over all rank-one predicates on atom codes; neither
    a model nor a truth table occurs in the proof type. *)
Module IndexedHornEncoding.
Module CF := ChurchFinite.ChurchFinite.
Module E := HornProofEncoding.HornProofEncoding.

Definition code_type {n} k : Term nat n := CF.choice_type 0 k.
Definition predicate_type {n} k : Term nat n := Π (code_type k) (𝓤 1).
Definition lift_clause {k} (c : E.Clause k) : E.Clause (S k) :=
  (map fsucc (fst c), fsucc (snd c)).
Definition lift_clauses {k} (cs : list (E.Clause k)) := map lift_clause cs.
Definition atom_env {k n} (P q : Term nat n) : Fin (S k) -> Term nat n :=
  fin_match (app P q) (fun i => app P (CF.selector 0 k i)).
Definition body {k n} (cs : list (E.Clause k)) (P q : Term nat n) :=
  E.matrix (lift_clauses cs) fzero (atom_env P q).
Definition proof_type {k n} (cs : list (E.Clause k)) (q : Term nat n) :=
  Π (predicate_type k) (body cs (var fzero) (shift q)).

Lemma code_type_replace k m n (sigma : Fin m -> Term nat n) :
  replace sigma (@code_type m k) = @code_type n k.
Proof. apply CF.choice_type_replace. Qed.
Lemma code_type_rename k m n (rho : Fin m -> Fin n) :
  rename rho (@code_type m k) = @code_type n k.
Proof. apply CF.choice_type_rename. Qed.
Theorem code_type_sorted {n} (G : Ctx nat n) k :
  @typ nat RankSorts n G (code_type k) (𝓤 1).
Proof.
  replace 1 with (CF.choice_rank 0 k) by
    (unfold CF.choice_rank; destruct k; reflexivity).
  apply CF.choice_type_sorted.
Qed.
Lemma predicate_type_replace k m n (sigma : Fin m -> Term nat n) :
  replace sigma (@predicate_type m k) = @predicate_type n k.
Proof. unfold predicate_type; cbn [replace]; now rewrite code_type_replace. Qed.
Lemma predicate_type_rename k m n (rho : Fin m -> Fin n) :
  rename rho (@predicate_type m k) = @predicate_type n k.
Proof. unfold predicate_type; cbn [rename]; now rewrite code_type_rename. Qed.
Theorem predicate_type_sorted {n} (G : Ctx nat n) k :
  @typ nat RankSorts n G (predicate_type k) (𝓤 2).
Proof.
  unfold predicate_type; eapply typ_Π with (ℓₜ := 1) (ℓᵤ := 0).
  - apply code_type_sorted.
  - constructor; reflexivity.
  - reflexivity.
Qed.
Theorem predicate_apply_sorted {n} (G : Ctx nat n) k P q :
  @typ nat RankSorts n G P (predicate_type k) ->
  @typ nat RankSorts n G q (code_type k) ->
  @typ nat RankSorts n G (app P q) (𝓤 1).
Proof.
  intros HP HQ; change (typ G (app P q) (subst (𝓤 1) q)).
  eapply typ_app; eassumption.
Qed.

Lemma atom_env_replace k m n (sigma : Fin m -> Term nat n) P q i :
  replace sigma (@atom_env k m P q i) =
  atom_env (replace sigma P) (replace sigma q) i.
Proof.
  dependent elimination i as [fzero | fsucc i];
    cbn [atom_env fin_match replace]; [reflexivity |].
  now rewrite CF.selector_replace.
Qed.
Lemma atom_env_rename k m n (rho : Fin m -> Fin n) P q i :
  rename rho (@atom_env k m P q i) =
  atom_env (rename rho P) (rename rho q) i.
Proof.
  dependent elimination i as [fzero | fsucc i];
    cbn [atom_env fin_match rename]; [reflexivity |].
  now rewrite CF.selector_rename.
Qed.
Theorem atom_env_sorted {n} (G : Ctx nat n) k P q :
  @typ nat RankSorts n G P (predicate_type k) ->
  @typ nat RankSorts n G q (code_type k) ->
  forall i, @typ nat RankSorts n G (@atom_env k n P q i) (𝓤 1).
Proof.
  intros HP HQ i; dependent elimination i as [fzero | fsucc i];
    cbn [atom_env fin_match]; eapply predicate_apply_sorted; eauto.
  apply CF.selector_typed.
Qed.
Lemma body_replace k (cs : list (E.Clause k)) m n
  (sigma : Fin m -> Term nat n) P q :
  replace sigma (body cs P q) = body cs (replace sigma P) (replace sigma q).
Proof.
  unfold body; rewrite E.matrix_replace; apply E.matrix_ext; intro i.
  apply atom_env_replace.
Qed.
Lemma body_rename k (cs : list (E.Clause k)) m n
  (rho : Fin m -> Fin n) P q :
  rename rho (body cs P q) = body cs (rename rho P) (rename rho q).
Proof.
  unfold body; rewrite E.matrix_rename; apply E.matrix_ext; intro i.
  apply atom_env_rename.
Qed.
Theorem body_sorted {n} (G : Ctx nat n) k (cs : list (E.Clause k)) P q :
  @typ nat RankSorts n G P (predicate_type k) ->
  @typ nat RankSorts n G q (code_type k) ->
  @typ nat RankSorts n G (body cs P q) (𝓤 (E.matrix_rank (lift_clauses cs))).
Proof. intros HP HQ; apply E.matrix_sorted; now apply atom_env_sorted. Qed.

Theorem proof_type_replace k (cs : list (E.Clause k)) m n
  (sigma : Fin m -> Term nat n) q :
  replace sigma (proof_type cs q) = proof_type cs (replace sigma q).
Proof.
  unfold proof_type; cbn [replace]; rewrite predicate_type_replace, body_replace.
  cbn [replace transpose fin_match]; now rewrite CF.replace_shift.
Qed.
Theorem proof_type_rename k (cs : list (E.Clause k)) m n
  (rho : Fin m -> Fin n) q :
  rename rho (proof_type cs q) = proof_type cs (rename rho q).
Proof.
  unfold proof_type; cbn [rename]; rewrite predicate_type_rename, body_rename.
  cbn [rename weak fin_match]; now rewrite CF.rename_shift.
Qed.
Theorem proof_type_sorted {n} (G : Ctx nat n) k (cs : list (E.Clause k)) q :
  @typ nat RankSorts n G q (code_type k) ->
  @typ nat RankSorts n G (proof_type cs q) (𝓤 3).
Proof.
  intro HQ; unfold proof_type; eapply typ_Π with
    (ℓₜ := 2) (ℓᵤ := E.matrix_rank (lift_clauses cs)).
  - apply predicate_type_sorted.
  - apply body_sorted.
    + rewrite <- (@predicate_type_rename k n (S n) fsucc).
      change (typ (G & predicate_type k) (var fzero)
        ((G & predicate_type k) !! fzero)); constructor.
    + rewrite <- (@code_type_rename k n (S n) fsucc).
      apply weakening; exact HQ.
  - change (3 = Nat.max 3 (E.matrix_rank (lift_clauses cs))).
    pose proof (E.matrix_rank_bounds (S k) (lift_clauses cs)); lia.
Qed.

(** Specialization is valid for every represented proof and every typed
    predicate, including open terms.  It is ordinary PTS application. *)
Theorem specialize_typed {n} (G : Ctx nat n) k (cs : list (E.Clause k)) q p P :
  @typ nat RankSorts n G p (proof_type cs q) ->
  @typ nat RankSorts n G P (predicate_type k) ->
  @typ nat RankSorts n G (app p P) (body cs P q).
Proof.
  intros Hp HP; replace (body cs P q) with
    (subst (body cs (var fzero) (shift q)) P).
  - eapply typ_app; eassumption.
  - unfold subst; rewrite body_replace; cbn [replace fin_match].
    unfold shift; rewrite replace_rename; cbn [fin_match]; now rewrite replace_var.
Qed.

Print Assumptions code_type_replace.
Print Assumptions code_type_rename.
Print Assumptions code_type_sorted.
Print Assumptions predicate_type_replace.
Print Assumptions predicate_type_rename.
Print Assumptions predicate_type_sorted.
Print Assumptions predicate_apply_sorted.
Print Assumptions atom_env_replace.
Print Assumptions atom_env_rename.
Print Assumptions atom_env_sorted.
Print Assumptions body_replace.
Print Assumptions body_rename.
Print Assumptions body_sorted.
Print Assumptions proof_type_replace.
Print Assumptions proof_type_rename.
Print Assumptions proof_type_sorted.
Print Assumptions specialize_typed.
End IndexedHornEncoding.
