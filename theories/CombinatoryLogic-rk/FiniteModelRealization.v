From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From PTSrk.Combinatory Require Import FiniteHorn FiniteUniversalHorn
  NativeCanonicity.
Import ListNotations.

(** Proof-producing finite semantic satisfaction in the ORIGINAL PTS.
    Truth values denote independently fixed propositions, not a typing checker
    or an assumed soundness predicate.  All finite indices are external Rocq
    parameters: the output is literal original, annotated PTS syntax.

    Universal quantification over an externally fixed finite domain is expanded
    to its complete list of semantic valuations.  The resulting closed PTS
    proposition is a continuation conjunction of all these clauses.  This is
    not an unguarded universal theorem about every Church-code inhabitant, nor
    one internal reflection theorem over arbitrary represented fragments. *)
Module FiniteModelRealization.

Definition truth_type {n} (b : bool) : Term nat n :=
  if b then Π (𝓤 0) (𝓤 0) else Π (𝓤 0) (var fzero).
Definition truth_witness {n} : Term nat n := lam (𝓤 0) (var fzero).

Lemma truth_type_rename b m n (rho : Fin m -> Fin n) :
  rename rho (truth_type b) = @truth_type n b.
Proof. destruct b; reflexivity. Qed.
Lemma truth_type_replace b m n (sigma : Fin m -> Term nat n) :
  replace sigma (truth_type b) = @truth_type n b.
Proof. destruct b; reflexivity. Qed.
Lemma truth_type_sorted {n} (G : Ctx nat n) b :
  @typ nat RankSorts n G (truth_type b) (𝓤 1).
Proof.
  destruct b; unfold truth_type; eapply typ_Π with (ℓₜ := 0) (ℓᵤ := 0).
  all: try (constructor; reflexivity); try reflexivity.
Qed.
Lemma truth_witness_typed {n} (G : Ctx nat n) :
  @typ nat RankSorts n G truth_witness (truth_type true).
Proof.
  unfold truth_witness, truth_type; eapply typ_λ with (ℓ := 0).
  - constructor; reflexivity.
  - change (typ (G & 𝓤 0) (var fzero) ((G & 𝓤 0) !! fzero)); constructor.
Qed.

Fixpoint clause_type {n} (premises : list bool) conclusion : Term nat n :=
  match premises with
  | [] => truth_type conclusion
  | b :: rest => Π (truth_type b) (clause_type rest conclusion)
  end.
Definition clause_rank (premises : list bool) :=
  match premises with [] => 1 | _ :: _ => 2 end.
Definition clause_holds premises conclusion :=
  forallb (fun b => b) premises = true -> conclusion = true.
Definition clause_valid premises conclusion :=
  negb (forallb (fun b => b) premises) || conclusion.

Lemma clause_valid_spec ps b : clause_valid ps b = true <-> clause_holds ps b.
Proof.
  unfold clause_valid, clause_holds.
  destruct (forallb (fun b => b) ps), b; simpl; intuition discriminate.
Qed.
Lemma clause_type_rename ps b : forall m n (rho : Fin m -> Fin n),
  rename rho (clause_type ps b) = @clause_type n ps b.
Proof. induction ps; intros; cbn [clause_type rename];
  [apply truth_type_rename | now rewrite truth_type_rename, IHps]. Qed.
Lemma clause_type_replace ps b : forall m n (sigma : Fin m -> Term nat n),
  replace sigma (clause_type ps b) = @clause_type n ps b.
Proof. induction ps; intros; cbn [clause_type replace];
  [apply truth_type_replace | now rewrite truth_type_replace, IHps]. Qed.
Lemma clause_type_sorted ps b : forall n (G : Ctx nat n),
  @typ nat RankSorts n G (clause_type ps b) (𝓤 (clause_rank ps)).
Proof.
  induction ps; intros; cbn [clause_type clause_rank]; [apply truth_type_sorted |].
  eapply typ_Π with (ℓₜ := 1) (ℓᵤ := clause_rank ps).
  - apply truth_type_sorted.
  - apply IHps.
  - destruct ps; reflexivity.
Qed.

Fixpoint ignore_premises {n} (premises : list bool) (t : Term nat n) : Term nat n :=
  match premises with
  | [] => t
  | b :: rest => lam (truth_type b) (ignore_premises rest (shift t))
  end.
Lemma ignore_premises_typed ps : forall n (G : Ctx nat n) t b,
  @typ nat RankSorts n G t (truth_type b) ->
  @typ nat RankSorts n G (ignore_premises ps t) (clause_type ps b).
Proof.
  induction ps; intros; cbn [ignore_premises clause_type]; [assumption |].
  eapply typ_λ with (ℓ := 1); [apply truth_type_sorted |].
  apply IHps. rewrite <- (@truth_type_rename b n (S n) fsucc).
  apply weakening; assumption.
Qed.

(** The false-premise branch returns that premise itself after discarding
    the remaining hypotheses.  No unrestricted ex-falso rule is used. *)
Fixpoint reject_premises {n} (premises : list bool) : Term nat n :=
  match premises with
  | [] => truth_witness
  | true :: rest => lam (truth_type true) (reject_premises rest)
  | false :: rest => lam (truth_type false) (ignore_premises rest (var fzero))
  end.
Definition realize_clause {n} ps (b : bool) : Term nat n :=
  if b then ignore_premises ps truth_witness else reject_premises ps.

Lemma reject_premises_typed ps : forall n (G : Ctx nat n),
  forallb (fun b => b) ps = false ->
  @typ nat RankSorts n G (reject_premises ps) (clause_type ps false).
Proof.
  induction ps as [|b ps IH]; intros n G H; [discriminate |].
  destruct b; cbn [reject_premises clause_type] in *;
    eapply typ_λ with (ℓ := 1); try apply truth_type_sorted.
  - apply IH; exact H.
  - apply ignore_premises_typed.
    change (typ (G & truth_type false) (var fzero)
      ((G & truth_type false) !! fzero)); constructor.
Qed.
Theorem realize_clause_typed {n} (G : Ctx nat n) ps b :
  clause_valid ps b = true ->
  @typ nat RankSorts n G (realize_clause ps b) (clause_type ps b).
Proof.
  intro H; destruct b; cbn [realize_clause].
  - apply ignore_premises_typed, truth_witness_typed.
  - apply reject_premises_typed.
    unfold clause_valid in H; destruct (forallb (fun b => b) ps); intuition discriminate.
Qed.

Definition BoolClause := (list bool * bool)%type.
Definition all_valid (clauses : list BoolClause) :=
  forallb (fun c => clause_valid (fst c) (snd c)) clauses.
Fixpoint continuation {n} (clauses : list BoolClause) : Term nat n :=
  match clauses with
  | [] => truth_type false
  | (ps, b) :: rest => Π (clause_type ps b) (continuation rest)
  end.
Fixpoint continuation_rank (clauses : list BoolClause) :=
  match clauses with
  | [] => 1
  | (ps, b) :: rest => Nat.max (S (clause_rank ps)) (continuation_rank rest)
  end.
Definition satisfaction_type {n} clauses : Term nat n :=
  Π (continuation clauses) (truth_type false).
Fixpoint supply_clauses {n} (clauses : list BoolClause) (consumer : Term nat n)
  : Term nat n :=
  match clauses with
  | [] => consumer
  | (ps, b) :: rest => supply_clauses rest (app consumer (realize_clause ps b))
  end.
Definition satisfaction_witness {n} clauses : Term nat n :=
  lam (continuation clauses) (supply_clauses clauses (var fzero)).

Lemma continuation_rename clauses : forall m n (rho : Fin m -> Fin n),
  rename rho (continuation clauses) = @continuation n clauses.
Proof. induction clauses as [|[ps b] rest IH]; intros; cbn [continuation rename];
  [apply truth_type_rename | now rewrite clause_type_rename, IH]. Qed.
Lemma continuation_replace clauses : forall m n (sigma : Fin m -> Term nat n),
  replace sigma (continuation clauses) = @continuation n clauses.
Proof. induction clauses as [|[ps b] rest IH]; intros; cbn [continuation replace];
  [apply truth_type_replace | now rewrite clause_type_replace, IH]. Qed.
Lemma continuation_sorted clauses : forall n (G : Ctx nat n),
  @typ nat RankSorts n G (continuation clauses) (𝓤 (continuation_rank clauses)).
Proof.
  induction clauses as [|[ps b] rest IH]; intros; cbn [continuation continuation_rank].
  - apply truth_type_sorted.
  - eapply typ_Π; [apply clause_type_sorted | apply IH | reflexivity].
Qed.
Lemma continuation_rank_bounds clauses : 1 <= continuation_rank clauses <= 3.
Proof.
  induction clauses as [|[ps b] rest IH]; cbn [continuation_rank]; [lia |].
  destruct ps; cbn [clause_rank]; lia.
Qed.
Theorem satisfaction_type_sorted {n} (G : Ctx nat n) clauses :
  @typ nat RankSorts n G (satisfaction_type clauses)
    (𝓤 (S (continuation_rank clauses))).
Proof.
  unfold satisfaction_type; eapply typ_Π.
  - apply continuation_sorted.
  - apply truth_type_sorted.
  - cbn [rule RankSorts]; symmetry; apply Nat.max_l; lia.
Qed.
Theorem satisfaction_rank_bound clauses : S (continuation_rank clauses) <= 4.
Proof. pose proof (continuation_rank_bounds clauses); lia. Qed.

Lemma supply_clauses_typed clauses : forall n (G : Ctx nat n) q,
  all_valid clauses = true ->
  @typ nat RankSorts n G q (continuation clauses) ->
  @typ nat RankSorts n G (supply_clauses clauses q) (truth_type false).
Proof.
  induction clauses as [|[ps b] rest IH]; intros n G q HC Hq;
    cbn [supply_clauses continuation] in *; [exact Hq |].
  change (clause_valid ps b && all_valid rest = true) in HC.
  apply andb_true_iff in HC; destruct HC as [Hc Hr].
  apply IH; [exact Hr |].
  replace (continuation rest) with
    (subst (@continuation (S n) rest) (@realize_clause n ps b)).
  - eapply typ_app; [exact Hq | now apply realize_clause_typed].
  - unfold subst; apply continuation_replace.
Qed.
Theorem satisfaction_witness_typed {n} (G : Ctx nat n) clauses :
  all_valid clauses = true ->
  @typ nat RankSorts n G (satisfaction_witness clauses) (satisfaction_type clauses).
Proof.
  intro H; unfold satisfaction_witness, satisfaction_type.
  eapply typ_λ; [apply continuation_sorted |].
  apply supply_clauses_typed; [exact H |].
  rewrite <- (@continuation_rename clauses n (S n) fsucc).
  change (typ (G & continuation clauses) (var fzero)
    ((G & continuation clauses) !! fzero)); constructor.
Qed.

(** An invalid clause has an internal refuter: feed its all-true premises
    their actual Top witnesses and obtain Void.  This proves that the
    continuation conjunction cannot certify a false finite truth table. *)
Fixpoint supply_true {n} (ps : list bool) (q : Term nat n) : Term nat n :=
  match ps with [] => q | _ :: rest => supply_true rest (app q truth_witness) end.
Lemma supply_true_typed ps : forall n (G : Ctx nat n) q,
  forallb (fun b => b) ps = true ->
  @typ nat RankSorts n G q (clause_type ps false) ->
  @typ nat RankSorts n G (supply_true ps q) (truth_type false).
Proof.
  induction ps as [|b ps IH]; intros n G q HP Hq;
    cbn [supply_true clause_type] in *; [exact Hq |].
  destruct b; [|discriminate].
  apply IH; [exact HP |].
  replace (clause_type ps false) with
    (subst (@clause_type (S n) ps false) (@truth_witness n)).
  - eapply typ_app; [exact Hq | apply truth_witness_typed].
  - unfold subst; apply clause_type_replace.
Qed.
Lemma invalid_clause_refuted {n} (G : Ctx nat n) ps b q :
  clause_valid ps b = false ->
  @typ nat RankSorts n G q (clause_type ps b) ->
  @typ nat RankSorts n G (supply_true ps q) (truth_type false).
Proof.
  unfold clause_valid; intros HC Hq; destruct b.
  - rewrite orb_true_r in HC; discriminate.
  - apply supply_true_typed; [|exact Hq].
    destruct (forallb (fun b => b) ps); [reflexivity | discriminate].
Qed.
Fixpoint ignore_clauses {n} clauses (t : Term nat n) : Term nat n :=
  match clauses with
  | [] => t
  | (ps, b) :: rest => lam (clause_type ps b) (ignore_clauses rest (shift t))
  end.
Lemma ignore_clauses_typed clauses : forall n (G : Ctx nat n) t,
  @typ nat RankSorts n G t (truth_type false) ->
  @typ nat RankSorts n G (ignore_clauses clauses t) (continuation clauses).
Proof.
  induction clauses as [|[ps b] rest IH]; intros; cbn [ignore_clauses continuation];
    [assumption |].
  eapply typ_λ; [apply clause_type_sorted |].
  apply IH; rewrite <- (@truth_type_rename false n (S n) fsucc).
  apply weakening; assumption.
Qed.
Fixpoint refute_clauses {n} clauses : Term nat n :=
  match clauses with
  | [] => truth_witness
  | (ps, b) :: rest => lam (clause_type ps b)
      (if clause_valid ps b then refute_clauses rest
       else ignore_clauses rest (supply_true ps (var fzero)))
  end.
Theorem refute_clauses_typed clauses : forall n (G : Ctx nat n),
  all_valid clauses = false ->
  @typ nat RankSorts n G (refute_clauses clauses) (continuation clauses).
Proof.
  induction clauses as [|[ps b] rest IH]; intros n G HC; [discriminate |].
  cbn [refute_clauses continuation]; eapply typ_λ; [apply clause_type_sorted |].
  change (clause_valid ps b && all_valid rest = false) in HC.
  destruct (clause_valid ps b) eqn:Hc.
  - apply IH; exact HC.
  - apply ignore_clauses_typed, invalid_clause_refuted with (b := b); [exact Hc |].
    rewrite <- (@clause_type_rename ps b n (S n) fsucc).
    change (typ (G & clause_type ps b) (var fzero)
      ((G & clause_type ps b) !! fzero)); constructor.
Qed.
Theorem satisfaction_inhabited_exact clauses :
  (exists t, @typ nat RankSorts 0 ε t (satisfaction_type clauses)) <->
  all_valid clauses = true.
Proof.
  split.
  - intros [t Ht]; destruct (all_valid clauses) eqn:HC; [reflexivity |].
    exfalso; apply (NativeCanonicity.void_empty (app t (refute_clauses clauses))).
    change (typ ε (app t (refute_clauses clauses)) (truth_type false)).
    replace (truth_type false) with
      (subst (@truth_type 1 false) (@refute_clauses 0 clauses)).
    + eapply typ_app; [exact Ht | now apply refute_clauses_typed].
    + unfold subst; apply truth_type_replace.
  - intro H; exists (satisfaction_witness clauses); now apply satisfaction_witness_typed.
Qed.

Section SemanticInstances.
Context {Atom : Type}.
Variable truth : Atom -> bool.
Definition positive_clause (c : list Atom * Atom) : BoolClause :=
  (map truth (fst c), truth (snd c)).
Definition negative_clause (ps : list Atom) : BoolClause := (map truth ps, false).
Definition semantic_clauses positive negative :=
  map positive_clause positive ++ map negative_clause negative.

Lemma all_true_map ps :
  forallb (fun b => b) (map truth ps) = true <-> Forall (fun a => truth a = true) ps.
Proof.
  rewrite forallb_forall, Forall_forall; split; intros H x Hx.
  - apply H, in_map, Hx.
  - apply in_map_iff in Hx; destruct Hx as [a [<- Ha]]; now apply H.
Qed.
Theorem semantic_clauses_valid positive negative :
  FiniteHorn.ConsistentModel positive negative (fun a => truth a = true) ->
  all_valid (semantic_clauses positive negative) = true.
Proof.
  intros [HP HN]; apply forallb_forall.
  intros c Hc; apply in_app_or in Hc; destruct Hc as [Hc | Hc];
    apply in_map_iff in Hc; destruct Hc as [a [<- Ha]]; apply clause_valid_spec.
  - unfold positive_clause, clause_holds; cbn; intro H.
    apply HP with (premises := fst a); [|now apply all_true_map].
    unfold FiniteHorn.Rules; now rewrite <- surjective_pairing.
  - unfold negative_clause, clause_holds; cbn; intro H; exfalso.
    eapply HN; [exact Ha | now apply all_true_map].
Qed.
Theorem semantic_clauses_valid_exact positive negative :
  all_valid (semantic_clauses positive negative) = true <->
  FiniteHorn.ConsistentModel positive negative (fun a => truth a = true).
Proof.
  split; [|apply semantic_clauses_valid].
  intro HC; unfold all_valid in HC; rewrite forallb_forall in HC; split.
  - intros ps a HR HP.
    pose proof (HC (positive_clause (ps, a))) as H.
    apply clause_valid_spec in H.
    + apply H, all_true_map, HP.
    + apply in_or_app; left; now apply in_map.
  - intros ps HP Hall.
    pose proof (HC (negative_clause ps)) as H.
    assert (HV : clause_valid (map truth ps) false = true).
    { apply H, in_or_app; right; now apply in_map. }
    apply clause_valid_spec in HV; specialize (HV (proj2 (all_true_map ps) Hall)).
    discriminate.
Qed.
Theorem finite_model_internal_certificate positive negative :
  FiniteHorn.ConsistentModel positive negative (fun a => truth a = true) ->
  @typ nat RankSorts 0 ε
    (satisfaction_witness (semantic_clauses positive negative))
    (satisfaction_type (semantic_clauses positive negative)).
Proof. intro H; apply satisfaction_witness_typed, semantic_clauses_valid, H. Qed.
End SemanticInstances.

Section CheckedCandidate.
Context {D Atom : Type}.
Variable elements : list D.
Hypothesis complete : forall x : D, In x elements.
Variable atom_eq_dec : forall a b : Atom, {a = b} + {a <> b}.
Variable positive : list (@FiniteUniversalHorn.PositiveSchema D Atom).
Variable negative : list (@FiniteUniversalHorn.NegativeSchema D Atom).

Definition candidate_positive := FiniteUniversalHorn.compile_positive elements positive.
Definition candidate_negative := FiniteUniversalHorn.compile_negative elements negative.
Definition candidate_boolean a :=
  FiniteHorn.member atom_eq_dec a (FiniteHorn.saturation atom_eq_dec candidate_positive).
Definition candidate_clauses :=
  semantic_clauses candidate_boolean candidate_positive candidate_negative.
Definition candidate_certificate : Term nat 0 := satisfaction_witness candidate_clauses.
Definition candidate_certificate_type : Term nat 0 := satisfaction_type candidate_clauses.

Lemma candidate_boolean_model :
  FiniteUniversalHorn.check_candidate elements atom_eq_dec positive negative = true ->
  FiniteHorn.ConsistentModel candidate_positive candidate_negative
    (fun a => candidate_boolean a = true).
Proof.
  intro HC; split.
  - intros ps a HR HP; apply FiniteHorn.member_spec.
    apply FiniteHorn.saturation_model with (premises := ps); [exact HR |].
    eapply Forall_impl; [|exact HP]; intros b Hb; now apply FiniteHorn.member_spec in Hb.
  - intros ps HP Hall.
    apply (proj1 (FiniteHorn.check_denials_spec atom_eq_dec candidate_positive
      candidate_negative) HC ps HP).
    eapply Forall_impl; [|exact Hall]; intros b Hb; now apply FiniteHorn.member_spec in Hb.
Qed.
Theorem checked_candidate_internal_certificate :
  FiniteUniversalHorn.check_candidate elements atom_eq_dec positive negative = true ->
  @typ nat RankSorts 0 ε candidate_certificate candidate_certificate_type.
Proof.
  intro H; apply finite_model_internal_certificate, candidate_boolean_model, H.
Qed.
Theorem candidate_certificate_inhabited_exact :
  (exists t, @typ nat RankSorts 0 ε t candidate_certificate_type) <->
  FiniteUniversalHorn.check_candidate elements atom_eq_dec positive negative = true.
Proof.
  unfold candidate_certificate_type; rewrite satisfaction_inhabited_exact.
  split; [|intro H; apply semantic_clauses_valid, candidate_boolean_model, H].
  intro H; apply semantic_clauses_valid_exact in H; destruct H as [_ HN].
  apply FiniteHorn.check_denials_spec.
  intros ps HP Hall; apply (HN ps HP).
  eapply Forall_impl; [|exact Hall]; intros b Hb; now apply FiniteHorn.member_spec.
Qed.
Theorem candidate_covers_every_positive_valuation s
  (v : Vector.t D (projT1 s)) :
  In s positive -> In (positive_clause candidate_boolean (projT2 s v)) candidate_clauses.
Proof.
  intro H; apply in_or_app; left; apply in_map.
  apply FiniteUniversalHorn.positive_instance_in; assumption.
Qed.
Theorem candidate_covers_every_negative_valuation s
  (v : Vector.t D (projT1 s)) :
  In s negative -> In (negative_clause candidate_boolean (projT2 s v)) candidate_clauses.
Proof.
  intro H; apply in_or_app; right; apply in_map.
  apply FiniteUniversalHorn.negative_instance_in; assumption.
Qed.
Theorem every_positive_instance_internal s (v : Vector.t D (projT1 s)) :
  FiniteUniversalHorn.check_candidate elements atom_eq_dec positive negative = true ->
  In s positive ->
  let c := positive_clause candidate_boolean (projT2 s v) in
  @typ nat RankSorts 0 ε (realize_clause (fst c) (snd c))
    (clause_type (fst c) (snd c)).
Proof.
  intros HC HS; apply realize_clause_typed.
  pose proof (semantic_clauses_valid candidate_boolean candidate_positive candidate_negative
    (candidate_boolean_model HC)) as H.
  unfold all_valid in H; rewrite forallb_forall in H; apply H.
  now apply candidate_covers_every_positive_valuation.
Qed.
Theorem every_negative_instance_internal s (v : Vector.t D (projT1 s)) :
  FiniteUniversalHorn.check_candidate elements atom_eq_dec positive negative = true ->
  In s negative ->
  let c := negative_clause candidate_boolean (projT2 s v) in
  @typ nat RankSorts 0 ε (realize_clause (fst c) (snd c))
    (clause_type (fst c) (snd c)).
Proof.
  intros HC HS; apply realize_clause_typed.
  pose proof (semantic_clauses_valid candidate_boolean candidate_positive candidate_negative
    (candidate_boolean_model HC)) as H.
  unfold all_valid in H; rewrite forallb_forall in H; apply H.
  now apply candidate_covers_every_negative_valuation.
Qed.
Theorem internal_certificate_iff_universal_model :
  (exists t, @typ nat RankSorts 0 ε t candidate_certificate_type) <->
  exists truth, FiniteUniversalHorn.UniversalModel positive negative truth.
Proof.
  rewrite candidate_certificate_inhabited_exact.
  apply FiniteUniversalHorn.candidate_satisfiable_iff, complete.
Qed.
End CheckedCandidate.

Example universal_identity_internal_certificate :
  @typ nat RankSorts 0 ε
    (candidate_certificate FiniteUniversalHorn.boolean_domain Bool.bool_dec
      [FiniteUniversalHorn.identity_schema] [FiniteUniversalHorn.forbid_false])
    (candidate_certificate_type FiniteUniversalHorn.boolean_domain Bool.bool_dec
      [FiniteUniversalHorn.identity_schema] [FiniteUniversalHorn.forbid_false]).
Proof. apply checked_candidate_internal_certificate; reflexivity. Qed.
Example second_valuation_has_no_internal_certificate :
  ~ exists t, @typ nat RankSorts 0 ε t
    (candidate_certificate_type FiniteUniversalHorn.boolean_domain Bool.bool_dec
      [FiniteUniversalHorn.fact_schema] [FiniteUniversalHorn.forbid_false]).
Proof.
  intro H; apply candidate_certificate_inhabited_exact in H; discriminate.
Qed.

Print Assumptions truth_type_sorted.
Print Assumptions truth_witness_typed.
Print Assumptions realize_clause_typed.
Print Assumptions satisfaction_type_sorted.
Print Assumptions satisfaction_rank_bound.
Print Assumptions satisfaction_witness_typed.
Print Assumptions refute_clauses_typed.
Print Assumptions satisfaction_inhabited_exact.
Print Assumptions semantic_clauses_valid.
Print Assumptions semantic_clauses_valid_exact.
Print Assumptions finite_model_internal_certificate.
Print Assumptions checked_candidate_internal_certificate.
Print Assumptions candidate_certificate_inhabited_exact.
Print Assumptions candidate_covers_every_positive_valuation.
Print Assumptions candidate_covers_every_negative_valuation.
Print Assumptions every_positive_instance_internal.
Print Assumptions every_negative_instance_internal.
Print Assumptions internal_certificate_iff_universal_model.
Print Assumptions universal_identity_internal_certificate.
Print Assumptions second_valuation_has_no_internal_certificate.
End FiniteModelRealization.
