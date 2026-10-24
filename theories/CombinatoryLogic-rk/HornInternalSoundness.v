From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From PTSrk.Combinatory Require Import FiniteHorn FiniteModelRealization
  FiniteModelSoundness NativeCanonicity ChurchFinite HornProofEncoding
  HornProofRealization.
Import ListNotations.

(** A genuine internal consumer of arbitrary finite Horn proof inhabitants.
    Its domain is the model-INDEPENDENT Church encoding.  Only its target
    and its handler witnesses use a Boolean model.  No induction over an
    external source proof, representation/canonicity assumption on the input,
    or native consistency theorem is used to type the consumer. *)
Module HornInternalSoundness.
Module E := HornProofEncoding.HornProofEncoding.
Module R := FiniteModelRealization.FiniteModelRealization.
Module FMS := FiniteModelSoundness.FiniteModelSoundness.
Module CF := ChurchFinite.ChurchFinite.

Lemma semantic_rule k ps a (truth : Fin k -> bool) : forall n,
  E.rule_type ps a (fun i => @R.truth_type n (truth i)) =
  R.clause_type (map truth ps) (truth a).
Proof.
  induction ps as [|b rest IH]; intro n; cbn [E.rule_type R.clause_type map].
  - reflexivity.
  - f_equal; etransitivity; [apply E.rule_type_ext; intro i;
      apply R.truth_type_rename | apply IH].
Qed.

Fixpoint feed {k n} (truth : Fin k -> bool) (clauses : list (E.Clause k))
  (consumer : Term nat n) : Term nat n :=
  match clauses with
  | [] => consumer
  | (ps, a) :: rest => feed truth rest
      (app consumer (R.realize_clause (map truth ps) (truth a)))
  end.

Definition valid_clauses {k} (truth : Fin k -> bool) clauses :=
  Forall (fun c : E.Clause k =>
    R.clause_valid (map truth (fst c)) (truth (snd c)) = true) clauses.

Theorem model_valid k (truth : Fin k -> bool) clauses :
  FiniteHorn.Model clauses (fun a => truth a = true) -> valid_clauses truth clauses.
Proof.
  intros HM; apply Forall_forall; intros [ps a] HC; cbn.
  exact (FMS.selected_clause_valid clauses truth HM ps a HC).
Qed.

Theorem feed_typed k (truth : Fin k -> bool) clauses :
  valid_clauses truth clauses -> forall n (G : Ctx nat n) a p,
  @typ nat RankSorts n G p
    (E.matrix clauses a (fun i => R.truth_type (truth i))) ->
  @typ nat RankSorts n G (feed truth clauses p) (R.truth_type (truth a)).
Proof.
  intro HV; induction HV as [|[ps b] rest HC HR IH]; intros n G a p HP;
    cbn [feed E.matrix] in *; [exact HP |].
  apply IH.
  replace (E.matrix rest a (fun i => @R.truth_type n (truth i))) with
    (subst (E.matrix rest a (fun i => shift (@R.truth_type n (truth i))))
      (@R.realize_clause n (map truth ps) (truth b))).
  - eapply typ_app; [exact HP |].
    rewrite semantic_rule; now apply R.realize_clause_typed.
  - unfold subst; rewrite E.matrix_replace; apply E.matrix_ext; intro i;
      apply CF.subst_shift.
Qed.

Definition reflect {n} k clauses a (truth : Fin k -> bool) : Term nat n :=
  lam (E.proof_type k clauses a)
    (feed truth clauses
      (E.specialize k (var fzero) (fun i => R.truth_type (truth i)))).
Definition reflection_type {n} k clauses a (truth : Fin k -> bool) : Term nat n :=
  Π (E.proof_type k clauses a) (R.truth_type (truth a)).

Theorem reflect_typed {n} (G : Ctx nat n) k clauses a truth :
  FiniteHorn.Model clauses (fun i : Fin k => truth i = true) ->
  @typ nat RankSorts n G (reflect k clauses a truth)
    (reflection_type k clauses a truth).
Proof.
  intro HM; unfold reflect, reflection_type; eapply typ_λ.
  - apply E.proof_type_sorted.
  - apply feed_typed; [now apply model_valid |].
    apply E.specialize_typed; [|intro i; apply R.truth_type_sorted].
    rewrite <- (@E.proof_type_rename k clauses a n (S n) fsucc).
    change (typ (G & E.proof_type k clauses a) (var fzero)
      ((G & E.proof_type k clauses a) !! fzero)); constructor.
Qed.

Theorem reflection_type_sorted {n} (G : Ctx nat n) k clauses a truth :
  @typ nat RankSorts n G (reflection_type k clauses a truth)
    (𝓤 (S (E.matrix_rank clauses))).
Proof.
  unfold reflection_type; eapply typ_Π.
  - apply E.proof_type_sorted.
  - apply R.truth_type_sorted.
  - change (S (E.matrix_rank clauses) = Nat.max (S (E.matrix_rank clauses)) 1).
    pose proof (E.matrix_rank_bounds k clauses); lia.
Qed.
Theorem reflection_type_rank_bound k (clauses : list (E.Clause k)) :
  S (E.matrix_rank clauses) <= 4.
Proof. pose proof (E.matrix_rank_bounds k clauses); lia. Qed.

Theorem arbitrary_proof_sound {n} (G : Ctx nat n) k clauses a truth p :
  FiniteHorn.Model clauses (fun i : Fin k => truth i = true) ->
  @typ nat RankSorts n G p (E.proof_type k clauses a) ->
  @typ nat RankSorts n G (app (reflect k clauses a truth) p)
    (R.truth_type (truth a)).
Proof.
  intros HM HP; replace (R.truth_type (truth a)) with
    (subst (@R.truth_type (S n) (truth a)) p).
  - eapply typ_app; [now apply reflect_typed | exact HP].
  - unfold subst; apply R.truth_type_replace.
Qed.

Theorem false_query_internal_refuter {n} (G : Ctx nat n) k clauses a truth :
  FiniteHorn.Model clauses (fun i : Fin k => truth i = true) -> truth a = false ->
  @typ nat RankSorts n G (reflect k clauses a truth)
    (Π (E.proof_type k clauses a) (R.truth_type false)).
Proof. intros HM HF; pose proof (reflect_typed G k clauses a truth HM) as H;
  unfold reflection_type in H; now rewrite HF in H. Qed.

(** External consequences of the internal term.  Only these converse and
    noninhabitation statements appeal to native Void canonicity. *)
Theorem arbitrary_closed_proof_true k clauses a truth p :
  FiniteHorn.Model clauses (fun i : Fin k => truth i = true) ->
  @typ nat RankSorts 0 ε p (E.proof_type k clauses a) -> truth a = true.
Proof.
  intros HM HP; pose proof (arbitrary_proof_sound ε k clauses a truth p HM HP) as H.
  destruct (truth a); [reflexivity |].
  exfalso; exact (NativeCanonicity.void_empty _ H).
Qed.
Theorem arbitrary_closed_proof_derivable k clauses a p
  (eq_dec : forall i j : Fin k, {i = j} + {i <> j}) :
  @typ nat RankSorts 0 ε p (E.proof_type k clauses a) ->
  FiniteHorn.Derives clauses a.
Proof.
  intro HP.
  pose proof (arbitrary_closed_proof_true k clauses a
    (FMS.finite_truth eq_dec clauses) p
    (FMS.finite_truth_model eq_dec clauses) HP) as H.
  unfold FMS.finite_truth in H; apply FiniteHorn.member_spec in H.
  now apply FiniteHorn.saturation_exact in H.
Qed.

Theorem proof_inhabited_exact k clauses a :
  (exists p, @typ nat RankSorts 0 ε p (E.proof_type k clauses a)) <->
  FiniteHorn.Derives clauses a.
Proof.
  split.
  - intros [p HP]; exact (arbitrary_closed_proof_derivable k clauses a p
      HornProofRealization.index_eq_dec HP).
  - apply HornProofRealization.source_derivation_represented.
Qed.

Print Assumptions semantic_rule.
Print Assumptions model_valid.
Print Assumptions feed_typed.
Print Assumptions reflect_typed.
Print Assumptions reflection_type_sorted.
Print Assumptions reflection_type_rank_bound.
Print Assumptions arbitrary_proof_sound.
Print Assumptions false_query_internal_refuter.
Print Assumptions arbitrary_closed_proof_true.
Print Assumptions arbitrary_closed_proof_derivable.
Print Assumptions proof_inhabited_exact.
End HornInternalSoundness.
