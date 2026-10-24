From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks Reduction AbstractRewriting
  Congruence DefEq.
From PTSrk.Combinatory Require Import ChurchFinite FiniteHorn
  FiniteModelRealization HornProofEncoding HornInternalSoundness
  IndexedHornEncoding IndexedHornRealization FiniteTypeDispatch.
Import ListNotations.

(** Internal soundness of a fixed finite Horn theory with an INTERNALLY
    varying query. The domain is the model-independent indexed proof type.
    The consumer accepts every native query and every native proof inhabitant;
    no canonicity or exhaustiveness premise is used in its typing. *)
Module IndexedHornSoundness.
Module CF := ChurchFinite.ChurchFinite.
Module E := HornProofEncoding.HornProofEncoding.
Module H := HornInternalSoundness.HornInternalSoundness.
Module I := IndexedHornEncoding.IndexedHornEncoding.
Module IR := IndexedHornRealization.IndexedHornRealization.
Module D := FiniteTypeDispatch.FiniteTypeDispatch.
Module R := FiniteModelRealization.FiniteModelRealization.

Definition truth_predicate {k n} (truth : Fin k -> bool) : Term nat n :=
  D.table k 1 (fun i => R.truth_type (truth i)).

Lemma truth_predicate_replace k (truth : Fin k -> bool) m n
  (sigma : Fin m -> Term nat n) :
  replace sigma (@truth_predicate k m truth) = @truth_predicate k n truth.
Proof.
  unfold truth_predicate; rewrite D.table_replace; apply D.table_ext; intro i.
  apply R.truth_type_replace.
Qed.
Lemma truth_predicate_rename k (truth : Fin k -> bool) m n
  (rho : Fin m -> Fin n) :
  rename rho (@truth_predicate k m truth) = @truth_predicate k n truth.
Proof.
  unfold truth_predicate; rewrite D.table_rename; apply D.table_ext; intro i.
  apply R.truth_type_rename.
Qed.
Theorem truth_predicate_typed {n} (G : Ctx nat n) k (truth : Fin k -> bool) :
  @typ nat RankSorts n G (truth_predicate truth) (I.predicate_type k).
Proof. apply D.table_typed; intro i; apply R.truth_type_sorted. Qed.
Theorem truth_query_sorted {n} (G : Ctx nat n) k (truth : Fin k -> bool) q :
  @typ nat RankSorts n G q (I.code_type k) ->
  @typ nat RankSorts n G (app (truth_predicate truth) q) (𝓤 1).
Proof. intro HQ; eapply I.predicate_apply_sorted; [apply truth_predicate_typed | exact HQ]. Qed.
Theorem truth_selector_beta {n} k (truth : Fin k -> bool) (a : Fin k) :
  reduces_to nat n (app (truth_predicate truth) (CF.selector 0 k a))
    (R.truth_type (truth a)).
Proof.
  exact (@D.table_selector_beta n k 1 (fun i => R.truth_type (truth i)) a).
Qed.

Lemma body_cons k ps a (cs : list (E.Clause k)) n (P q : Term nat n) :
  I.body ((ps, a) :: cs) P q =
  Π (E.rule_type ps a (fun i => app P (CF.selector 0 k i)))
    (I.body cs (shift P) (shift q)).
Proof.
  unfold I.body; cbn [I.lift_clauses I.lift_clause map E.matrix fst snd].
  rewrite IR.rule_lifted with (env := fun i => app P (CF.selector 0 k i))
    by reflexivity.
  f_equal; apply E.matrix_ext; intro i; apply I.atom_env_rename.
Qed.

Theorem semantic_handler_typed {n} (G : Ctx nat n) k
  (truth : Fin k -> bool) ps a :
  R.clause_valid (map truth ps) (truth a) = true ->
  @typ nat RankSorts n G (R.realize_clause (map truth ps) (truth a))
    (E.rule_type ps a (fun i => app (truth_predicate truth) (CF.selector 0 k i))).
Proof.
  intro HV; eapply typ_conv with
    (T := E.rule_type ps a (fun i => R.truth_type (truth i))).
  - rewrite H.semantic_rule; now apply R.realize_clause_typed.
  - apply E.rule_type_sorted; intro i; apply truth_query_sorted, CF.selector_typed.
  - symmetry; apply D.reduction_equiv, D.rule_type_reduces; intro i.
    apply truth_selector_beta.
Qed.

Theorem feed_typed k (truth : Fin k -> bool) cs :
  H.valid_clauses truth cs -> forall n (G : Ctx nat n) q p,
  @typ nat RankSorts n G p (I.body cs (truth_predicate truth) q) ->
  @typ nat RankSorts n G (H.feed truth cs p) (app (truth_predicate truth) q).
Proof.
  intro HV; induction HV as [|[ps a] rest HC HR IH]; intros n G q p HP;
    cbn [H.feed] in *; [exact HP |].
  rewrite body_cons in HP; unfold shift at 1 in HP;
    rewrite truth_predicate_rename in HP.
  apply IH.
  replace (I.body rest (truth_predicate truth) q) with
    (subst (I.body rest (truth_predicate truth) (shift q))
      (@R.realize_clause n (map truth ps) (truth a))).
  - eapply typ_app; [exact HP | now apply semantic_handler_typed].
  - unfold subst; rewrite I.body_replace, truth_predicate_replace.
    unfold shift; rewrite replace_rename; cbn [fin_match]; now rewrite replace_var.
Qed.

Definition reflect_at {k n} (cs : list (E.Clause k)) (truth : Fin k -> bool)
  (q : Term nat n) : Term nat n :=
  lam (I.proof_type cs q)
    (H.feed truth cs (app (var fzero) (truth_predicate truth))).
Definition reflection_at_type {k n} (cs : list (E.Clause k))
  (truth : Fin k -> bool) (q : Term nat n) : Term nat n :=
  Π (I.proof_type cs q) (app (truth_predicate truth) (shift q)).

Theorem reflect_at_typed {n} (G : Ctx nat n) k cs (truth : Fin k -> bool) q :
  FiniteHorn.Model cs (fun i => truth i = true) ->
  @typ nat RankSorts n G q (I.code_type k) ->
  @typ nat RankSorts n G (reflect_at cs truth q) (reflection_at_type cs truth q).
Proof.
  intros HM HQ; unfold reflect_at, reflection_at_type; eapply typ_λ.
  - now apply I.proof_type_sorted.
  - apply feed_typed; [now apply H.model_valid |].
    apply I.specialize_typed with (q := shift q); [|apply truth_predicate_typed].
    unfold shift.
    rewrite <- (@I.proof_type_rename k cs n (S n) (fun x => fsucc x) q).
    change (typ (G & I.proof_type cs q) (var fzero)
      ((G & I.proof_type cs q) !! fzero)); constructor.
Qed.
Theorem reflection_at_type_sorted {n} (G : Ctx nat n) k cs
  (truth : Fin k -> bool) q :
  @typ nat RankSorts n G q (I.code_type k) ->
  @typ nat RankSorts n G (reflection_at_type cs truth q) (𝓤 4).
Proof.
  intro HQ; unfold reflection_at_type; eapply typ_Π with (ℓₜ := 3) (ℓᵤ := 1).
  - now apply I.proof_type_sorted.
  - apply truth_query_sorted.
    rewrite <- (@I.code_type_rename k n (S n) fsucc); now apply weakening.
  - reflexivity.
Qed.
Lemma reflection_at_type_replace k cs (truth : Fin k -> bool) m n
  (sigma : Fin m -> Term nat n) q :
  replace sigma (reflection_at_type cs truth q) =
  reflection_at_type cs truth (replace sigma q).
Proof.
  unfold reflection_at_type; cbn [replace];
    rewrite I.proof_type_replace, truth_predicate_replace, CF.replace_shift; reflexivity.
Qed.

Definition uniform_reflect {k n} (cs : list (E.Clause k)) (truth : Fin k -> bool)
  : Term nat n := lam (I.code_type k) (reflect_at cs truth (var fzero)).
Definition uniform_reflection_type {k n} (cs : list (E.Clause k))
  (truth : Fin k -> bool) : Term nat n :=
  Π (I.code_type k) (reflection_at_type cs truth (var fzero)).

Theorem uniform_reflect_typed {n} (G : Ctx nat n) k cs (truth : Fin k -> bool) :
  FiniteHorn.Model cs (fun i => truth i = true) ->
  @typ nat RankSorts n G (uniform_reflect cs truth) (uniform_reflection_type cs truth).
Proof.
  intro HM; unfold uniform_reflect, uniform_reflection_type; eapply typ_λ.
  - apply I.code_type_sorted.
  - apply reflect_at_typed; [exact HM |].
    rewrite <- (@I.code_type_rename k n (S n) fsucc).
    change (typ (G & I.code_type k) (var fzero)
      ((G & I.code_type k) !! fzero)); constructor.
Qed.
Theorem uniform_reflection_type_sorted {n} (G : Ctx nat n) k cs
  (truth : Fin k -> bool) :
  @typ nat RankSorts n G (uniform_reflection_type cs truth) (𝓤 4).
Proof.
  unfold uniform_reflection_type; eapply typ_Π with (ℓₜ := 1) (ℓᵤ := 4).
  - apply I.code_type_sorted.
  - apply reflection_at_type_sorted.
    rewrite <- (@I.code_type_rename k n (S n) fsucc).
    change (typ (G & I.code_type k) (var fzero)
      ((G & I.code_type k) !! fzero)); constructor.
  - reflexivity.
Qed.
Theorem uniform_query_typed {n} (G : Ctx nat n) k cs
  (truth : Fin k -> bool) q :
  FiniteHorn.Model cs (fun i => truth i = true) ->
  @typ nat RankSorts n G q (I.code_type k) ->
  @typ nat RankSorts n G (app (uniform_reflect cs truth) q)
    (reflection_at_type cs truth q).
Proof.
  intros HM HQ; replace (reflection_at_type cs truth q) with
    (subst (reflection_at_type cs truth (var fzero)) q).
  - eapply typ_app; [now apply uniform_reflect_typed | exact HQ].
  - unfold subst; rewrite reflection_at_type_replace; reflexivity.
Qed.
Theorem arbitrary_query_sound {n} (G : Ctx nat n) k cs
  (truth : Fin k -> bool) q p :
  FiniteHorn.Model cs (fun i => truth i = true) ->
  @typ nat RankSorts n G q (I.code_type k) ->
  @typ nat RankSorts n G p (I.proof_type cs q) ->
  @typ nat RankSorts n G (app (app (uniform_reflect cs truth) q) p)
    (app (truth_predicate truth) q).
Proof.
  intros HM HQ HP; replace (app (truth_predicate truth) q) with
    (subst (app (truth_predicate truth) (shift q)) p).
  - eapply typ_app; [now apply uniform_query_typed | exact HP].
  - unfold subst; cbn [replace]; rewrite truth_predicate_replace.
    unfold shift; rewrite replace_rename; cbn [fin_match]; now rewrite replace_var.
Qed.
Theorem canonical_query_sound {n} (G : Ctx nat n) k cs
  (truth : Fin k -> bool) a p :
  FiniteHorn.Model cs (fun i => truth i = true) ->
  @typ nat RankSorts n G p (I.proof_type cs (CF.selector 0 k a)) ->
  @typ nat RankSorts n G
    (app (app (uniform_reflect cs truth) (CF.selector 0 k a)) p)
    (R.truth_type (truth a)).
Proof.
  intros HM HP; eapply typ_conv.
  - apply arbitrary_query_sound; [exact HM | apply CF.selector_typed | exact HP].
  - apply R.truth_type_sorted.
  - apply D.reduction_equiv, truth_selector_beta.
Qed.

Print Assumptions truth_predicate_replace.
Print Assumptions truth_predicate_rename.
Print Assumptions truth_predicate_typed.
Print Assumptions truth_query_sorted.
Print Assumptions truth_selector_beta.
Print Assumptions body_cons.
Print Assumptions semantic_handler_typed.
Print Assumptions feed_typed.
Print Assumptions reflect_at_typed.
Print Assumptions reflection_at_type_sorted.
Print Assumptions reflection_at_type_replace.
Print Assumptions uniform_reflect_typed.
Print Assumptions uniform_reflection_type_sorted.
Print Assumptions uniform_query_typed.
Print Assumptions arbitrary_query_sound.
Print Assumptions canonical_query_sound.
End IndexedHornSoundness.
