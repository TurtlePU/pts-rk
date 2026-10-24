From Stdlib Require Import Lists.List Bool.Bool.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From PTSrk.Combinatory Require Import GroundHorn FiniteHorn FiniteUniversalHorn
  NativeCanonicity FiniteModelRealization.
Import ListNotations.

(** Constructive deduction translation, not merely table evaluation.
    Source proof trees carry only selected-clause membership and recursively
    supplied premises.  They carry no native PTS typing judgment.  Compilation
    applies the actual clause-realization terms to compiled subproofs.

    The source tree lives in Rocq Type so that the compiler really computes an
    original PTS term.  Its inhabited propositions agree exactly with the
    existing independent Horn derivability relation.  External finite model
    parameters are not represented budget arguments; this is not one internal
    uniform reflection theorem about all Church-coded proofs. *)
Module FiniteModelSoundness.
Module R := FiniteModelRealization.FiniteModelRealization.
Module GH := GroundHorn.GroundHorn.

Section ProofTrees.
Context {Atom : Type}.
Variable clauses : list (list Atom * Atom).

Inductive Proof : Atom -> Type :=
| use_clause ps a : In (ps, a) clauses -> Proofs ps -> Proof a
with Proofs : list Atom -> Type :=
| proofs_nil : Proofs []
| proofs_cons a ps : Proof a -> Proofs ps -> Proofs (a :: ps).

Scheme Proof_ind' := Induction for Proof Sort Prop
  with Proofs_ind' := Induction for Proofs Sort Prop.

Theorem proof_derivable a (p : Proof a) : FiniteHorn.Derives clauses a.
Proof.
  induction p using Proof_ind' with
    (P0 := fun ps _ => GH.DerivesAll (FiniteHorn.Rules clauses) ps).
  - econstructor; eassumption.
  - constructor.
  - constructor; assumption.
Qed.
Theorem derivation_has_proof a : FiniteHorn.Derives clauses a -> inhabited (Proof a).
Proof.
  intro H; refine (@GH.Derives_ind' Atom (FiniteHorn.Rules clauses)
    (fun a _ => inhabited (Proof a)) (fun ps _ => inhabited (Proofs ps)) _ _ _ a H).
  - intros ps b HR subs [p]; constructor; econstructor; eassumption.
  - constructor; constructor.
  - intros b ps p [ip] subs [ips]; constructor; now constructor.
Qed.
Theorem proof_exact a : inhabited (Proof a) <-> FiniteHorn.Derives clauses a.
Proof. split; [intros [p]; now apply proof_derivable | apply derivation_has_proof]. Qed.

Variable truth : Atom -> bool.
Fixpoint compile {a} (p : Proof a) : Term nat 0 :=
  match p with
  | use_clause ps b _ subs =>
      supply subs (R.realize_clause (map truth ps) (truth b))
  end
with supply {ps} (p : Proofs ps) (q : Term nat 0) : Term nat 0 :=
  match p with
  | proofs_nil => q
  | proofs_cons a rest head tail => supply tail (app q (compile head))
  end.

Hypothesis model : FiniteHorn.Model clauses (fun a => truth a = true).

Lemma selected_clause_valid ps a : In (ps, a) clauses ->
  R.clause_valid (map truth ps) (truth a) = true.
Proof.
  intro HR; apply R.clause_valid_spec; intro Hps.
  apply model with (premises := ps); [exact HR | now apply R.all_true_map].
Qed.
Theorem compile_typed a (p : Proof a) :
  @typ nat RankSorts 0 ε (compile p) (R.truth_type (truth a)).
Proof.
  induction p using Proof_ind' with
    (P0 := fun ps subs => forall b q,
      @typ nat RankSorts 0 ε q (R.clause_type (map truth ps) b) ->
      @typ nat RankSorts 0 ε (supply subs q) (R.truth_type b)).
  - cbn [compile]; apply IHp, R.realize_clause_typed, selected_clause_valid, i.
  - intros b q Hq; exact Hq.
  - intros b q Hq; cbn [supply]; apply IHp0.
    replace (R.clause_type (map truth ps) b) with
      (subst (@R.clause_type 1 (map truth ps) b) (compile p)).
    + eapply typ_app; [exact Hq | exact IHp].
    + unfold subst; apply R.clause_type_replace.
Qed.
Theorem supply_typed ps (p : Proofs ps) b q :
  @typ nat RankSorts 0 ε q (R.clause_type (map truth ps) b) ->
  @typ nat RankSorts 0 ε (supply p q) (R.truth_type b).
Proof.
  revert b q; induction p; intros b q Hq; cbn [supply]; [exact Hq |].
  apply IHp. replace (R.clause_type (map truth ps) b) with
    (subst (@R.clause_type 1 (map truth ps) b) (compile p)).
  - eapply typ_app; [exact Hq | apply compile_typed].
  - unfold subst; apply R.clause_type_replace.
Qed.
Theorem false_conclusion_compiles_to_void a (p : Proof a) : truth a = false ->
  @typ nat RankSorts 0 ε (compile p) NativeCanonicity.Void.
Proof. intro H; pose proof (compile_typed a p) as HT; now rewrite H in HT. Qed.
Theorem every_derivation_has_native_realization a : FiniteHorn.Derives clauses a ->
  exists t, @typ nat RankSorts 0 ε t (R.truth_type (truth a)).
Proof.
  intro H; destruct (derivation_has_proof a H) as [p].
  exists (compile p); apply compile_typed.
Qed.
Theorem false_query_underivable a : truth a = false -> ~ FiniteHorn.Derives clauses a.
Proof.
  intros HF HD; destruct (derivation_has_proof a HD) as [p].
  apply (NativeCanonicity.void_empty (compile p)).
  now apply false_conclusion_compiles_to_void.
Qed.

Variable denials : list (list Atom).
Hypothesis denied : FiniteHorn.Denials denials (fun a => truth a = true).
Definition compile_denial ps (p : Proofs ps) : Term nat 0 :=
  supply p (R.realize_clause (map truth ps) false).
Theorem denial_compiles_to_void ps (p : Proofs ps) : In ps denials ->
  @typ nat RankSorts 0 ε (compile_denial ps p) NativeCanonicity.Void.
Proof.
  intro HP; change (typ ε (supply p (R.realize_clause (map truth ps) false))
    (R.truth_type false)).
  apply supply_typed, R.realize_clause_typed, R.clause_valid_spec.
  intro H; exfalso; apply (denied ps HP), R.all_true_map, H.
Qed.
Theorem denied_proofs_impossible ps : In ps denials -> ~ inhabited (Proofs ps).
Proof.
  intros HP [p]; apply (NativeCanonicity.void_empty (compile_denial ps p)).
  now apply denial_compiles_to_void.
Qed.
End ProofTrees.

Section CheckedFiniteModel.
Context {Atom : Type}.
Variable atom_eq_dec : forall a b : Atom, {a = b} + {a <> b}.
Variable clauses : list (list Atom * Atom).
Variable denials : list (list Atom).
Definition finite_truth a := FiniteHorn.member atom_eq_dec a (FiniteHorn.saturation atom_eq_dec clauses).
Lemma finite_truth_model : FiniteHorn.Model clauses (fun a => finite_truth a = true).
Proof.
  intros ps a HR HP; apply FiniteHorn.member_spec.
  apply FiniteHorn.saturation_model with (premises := ps); [exact HR |].
  eapply Forall_impl; [|exact HP]; intros b Hb; now apply FiniteHorn.member_spec in Hb.
Qed.
Theorem checked_deduction_translation a (p : Proof clauses a) :
  @typ nat RankSorts 0 ε (compile clauses finite_truth p) (R.truth_type (finite_truth a)).
Proof. apply compile_typed, finite_truth_model. Qed.
Theorem checked_denial_translation ps (p : Proofs clauses ps) :
  FiniteHorn.check_denials atom_eq_dec clauses denials = true -> In ps denials ->
  @typ nat RankSorts 0 ε (compile_denial clauses finite_truth ps p) NativeCanonicity.Void.
Proof.
  intros HC HP; apply denial_compiles_to_void with (denials := denials).
  - apply finite_truth_model.
  - intros rest HR Hall.
    apply (proj1 (FiniteHorn.check_denials_spec atom_eq_dec clauses denials) HC rest HR).
    eapply Forall_impl; [|exact Hall]; intros b Hb; now apply FiniteHorn.member_spec in Hb.
  - exact HP.
Qed.
End CheckedFiniteModel.

Print Assumptions proof_derivable.
Print Assumptions derivation_has_proof.
Print Assumptions proof_exact.
Print Assumptions selected_clause_valid.
Print Assumptions compile_typed.
Print Assumptions supply_typed.
Print Assumptions false_conclusion_compiles_to_void.
Print Assumptions every_derivation_has_native_realization.
Print Assumptions false_query_underivable.
Print Assumptions denial_compiles_to_void.
Print Assumptions denied_proofs_impossible.
Print Assumptions finite_truth_model.
Print Assumptions checked_deduction_translation.
Print Assumptions checked_denial_translation.
End FiniteModelSoundness.
