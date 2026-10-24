From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat Lia.
From PTSrk.Combinatory Require Import GroundHorn.
Import ListNotations.

(** Executable exact models of FINITE GROUND Horn theories with denials.
    Each atom is a nullary predicate.  The domain is fixed to [unit], so
    finiteness of the domain does not identify different predicate symbols.
    These are not models of the original ungrounded PTS signature. *)
Module FiniteHorn.
Section FiniteSystem.
Context {Atom : Type}.
Variable atom_eq_dec : forall a b : Atom, {a = b} + {a <> b}.
Variable clauses : list (list Atom * Atom).

Definition Rules premises conclusion := In (premises, conclusion) clauses.
Definition Derives := GroundHorn.Derives Rules.
Definition Model := GroundHorn.Model Rules.

Definition member (a : Atom) (known : list Atom) : bool :=
  if in_dec atom_eq_dec a known then true else false.
Definition enabled (known premises : list Atom) : bool :=
  forallb (fun a => member a known) premises.

Lemma member_spec a known : member a known = true <-> In a known.
Proof. unfold member; destruct (in_dec atom_eq_dec a known); intuition discriminate. Qed.

Lemma enabled_spec known premises :
  enabled known premises = true <-> Forall (fun a => In a known) premises.
Proof.
  unfold enabled. rewrite forallb_forall, Forall_forall.
  split; intros H a Ha; apply member_spec; auto.
Qed.

Definition round (known : list Atom) : list Atom :=
  nodup atom_eq_dec
    (known ++ map snd (filter (fun clause => enabled known (fst clause)) clauses)).
Definition heads : list Atom := map snd clauses.

Lemma round_spec known a :
  In a (round known) <->
  In a known \/ exists premises,
    Rules premises a /\ Forall (fun b => In b known) premises.
Proof.
  unfold round. rewrite nodup_In, in_app_iff.
  split; intros [H | H]; [now left | right | now left | right].
  - apply in_map_iff in H. destruct H as [[ps c] [E H]]. simpl in E; subst c.
    apply filter_In in H. exists ps. destruct H as [H H']; split; auto.
    now apply enabled_spec.
  - destruct H as [ps [H H']]. apply in_map_iff. exists (ps, a).
    split; [reflexivity | apply filter_In; split; auto].
    now apply enabled_spec.
Qed.

Lemma round_inflationary known : incl known (round known).
Proof. intros a H; apply round_spec; now left. Qed.

Lemma round_nodup known : NoDup (round known).
Proof. apply NoDup_nodup. Qed.

Lemma round_heads known : incl known heads -> incl (round known) heads.
Proof.
  intros H a Ha; apply round_spec in Ha. destruct Ha as [Ha | [ps [Ha _]]].
  - now apply H.
  - unfold heads; apply in_map_iff; exists (ps, a); auto.
Qed.

Lemma round_monotone known larger :
  incl known larger -> incl (round known) (round larger).
Proof.
  intros H a Ha; apply round_spec in Ha; apply round_spec.
  destruct Ha as [Ha | [ps [HR HP]]]; [left; auto | right].
  exists ps; split; auto. rewrite Forall_forall in *; auto.
Qed.

Fixpoint rounds (fuel : nat) (known : list Atom) : list Atom :=
  match fuel with
  | 0 => known
  | S k => rounds k (round known)
  end.

Lemma rounds_inflationary k known : incl known (rounds k known).
Proof.
  revert known; induction k; simpl; intros known a Ha; auto.
  apply IHk, round_inflationary, Ha.
Qed.

Lemma rounds_heads k known : incl known heads -> incl (rounds k known) heads.
Proof. revert known; induction k; simpl; intros; auto using round_heads. Qed.

Lemma rounds_nodup k known : NoDup known -> NoDup (rounds k known).
Proof. revert known; induction k; simpl; auto using round_nodup. Qed.

Definition Closed (known : list Atom) := incl (round known) known.

Lemma closed_model known : Closed known <-> Model (fun a => In a known).
Proof.
  split.
  - intros H ps a HR HP. apply H, round_spec; right; now exists ps.
  - intros H a Ha; apply round_spec in Ha; destruct Ha as [Ha | [ps [HR HP]]]; auto.
    eapply H; eassumption.
Qed.

Lemma closed_rounds k known : Closed known -> Closed (rounds k known).
Proof.
  revert known; induction k; simpl; intros known H; auto.
  apply IHk. unfold Closed in *.
  intros a Ha. apply round_inflationary, H.
  apply (round_monotone _ _ H), Ha.
Qed.

(** At each nonstationary pass at least one new head is inserted.  Therefore
    [length clauses] passes suffice, even with duplicate clauses/heads. *)
Theorem rounds_closed k known :
  NoDup known -> incl known heads -> length heads <= k + length known ->
  Closed (rounds k known).
Proof.
  revert known; induction k; intros known Hnd Hheads Hlen; simpl.
  - assert (Hreverse : incl heads known).
    { eapply NoDup_length_incl; eauto; lia. }
    intros a Ha; apply Hreverse, round_heads with known; assumption.
  - destruct (Nat.eq_dec (length known) (length (round known))) as [E | E].
    + assert (HC : Closed known).
      { unfold Closed.
        apply (NoDup_length_incl (l := known) (l' := round known));
          auto using round_inflationary; lia. }
      exact (closed_rounds (S k) known HC).
    + apply IHk; [apply round_nodup | now apply round_heads |].
      assert (length known <= length (round known)) by
        (apply NoDup_incl_length; auto using round_inflationary).
      lia.
Qed.

Definition saturation : list Atom := rounds (length clauses) [].

Theorem saturation_closed : Closed saturation.
Proof.
  apply rounds_closed; [constructor | intros a H; contradiction |].
  unfold heads; rewrite length_map; simpl; lia.
Qed.

Theorem saturation_model : Model (fun a => In a saturation).
Proof. apply closed_model, saturation_closed. Qed.

Lemma round_sound known : Forall Derives known -> Forall Derives (round known).
Proof.
  rewrite !Forall_forall. intros H a Ha; apply round_spec in Ha.
  destruct Ha as [Ha | [ps [HR HP]]]; auto.
  eapply GroundHorn.by_rule; [exact HR | apply GroundHorn.derivesAll_iff].
  rewrite Forall_forall in *; intros b Hb; exact (H b (HP b Hb)).
Qed.

Lemma rounds_sound k known : Forall Derives known -> Forall Derives (rounds k known).
Proof. revert known; induction k; simpl; auto using round_sound. Qed.

Theorem saturation_exact a : In a saturation <-> Derives a.
Proof.
  split.
  - intro H. assert (HA : Forall Derives saturation) by
      (apply rounds_sound; constructor).
    rewrite Forall_forall in HA; auto.
  - intro H. apply (GroundHorn.derivation_sound Rules a H), saturation_model.
Qed.

Theorem saturation_least valuation :
  Model valuation -> forall a, In a saturation -> valuation a.
Proof.
  intros HM a Ha; apply saturation_exact in Ha.
  exact (GroundHorn.derivation_sound Rules a Ha valuation HM).
Qed.

Theorem saturation_size : length saturation <= length clauses.
Proof.
  unfold saturation. rewrite <- (length_map snd clauses).
  apply NoDup_incl_length; [apply rounds_nodup; constructor |].
  apply rounds_heads; intros a H; contradiction.
Qed.

(** A denial forbids simultaneous truth of its premises.  Singleton
    denials [a] exclude inhabitants of the represented contradiction atom. *)
Definition Denials (denials : list (list Atom)) (valuation : Atom -> Prop) :=
  forall premises, In premises denials -> ~ Forall valuation premises.
Definition ConsistentModel denials valuation := Model valuation /\ Denials denials valuation.
Definition check_denials (denials : list (list Atom)) : bool :=
  forallb (fun premises => negb (enabled saturation premises)) denials.

Lemma check_denials_spec denials :
  check_denials denials = true <-> Denials denials (fun a => In a saturation).
Proof.
  unfold check_denials, Denials; rewrite forallb_forall.
  split; intros H ps HP.
  - specialize (H ps HP); rewrite negb_true_iff in H.
    intros Hall; apply enabled_spec in Hall; congruence.
  - specialize (H ps HP). apply negb_true_iff.
    destruct (enabled saturation ps) eqn:E; [|reflexivity].
    exfalso; apply H, enabled_spec, E.
Qed.

Theorem denial_model_exists_iff denials :
  check_denials denials = true <->
  exists valuation, ConsistentModel denials valuation.
Proof.
  split.
  - intro H; exists (fun a => In a saturation); split.
    + apply saturation_model.
    + now apply check_denials_spec.
  - intros [valuation [HM HD]]. apply check_denials_spec.
    intros ps HP Hall; apply (HD ps HP).
    apply Forall_impl with (P := fun a => In a saturation); [|exact Hall].
    intros a Ha; now apply saturation_least with (a := a).
Qed.

Theorem denied_atoms_empty denials valuation a :
  ConsistentModel denials valuation -> In [a] denials -> ~ valuation a.
Proof.
  intros [_ HD] Ha Hval. apply (HD [a] Ha); repeat constructor; assumption.
Qed.

Theorem constrained_consequence_exact denials a :
  check_denials denials = true ->
  ((forall valuation, ConsistentModel denials valuation -> valuation a) <-> Derives a).
Proof.
  intro HC; split.
  - intro H; apply saturation_exact. apply H; split.
    + apply saturation_model.
    + now apply check_denials_spec.
  - intros H valuation [HM _]. exact (GroundHorn.derivation_sound Rules a H valuation HM).
Qed.

(** Fixed singleton first-order structures for this nullary signature.
    Every assignment into the domain gives the same atomic interpretation. *)
Definition domain := unit.
Definition singleton_truth (_ : domain) (a : Atom) := In a saturation.

Theorem fixed_finite_model denials :
  check_denials denials = true ->
  (forall x : domain, x = tt) /\
  (forall assignment : nat -> domain,
     ConsistentModel denials (singleton_truth (assignment 0))).
Proof.
  intro H; split; [now intros [] |].
  intros assignment; split; [apply saturation_model | now apply check_denials_spec].
Qed.

(** A finite signed diagram fixes each observed predicate to its computed
    least-model value.  Its negative literals are an ADDITION to the Horn
    theory, not consequences inferred from nonderivability alone. *)
Definition Diagram (observed : list Atom) (valuation : Atom -> Prop) :=
  forall a, In a observed -> (valuation a <-> In a saturation).
Definition CompletedModel denials observed valuation :=
  ConsistentModel denials valuation /\ Diagram observed valuation.

Theorem completed_model_exists_iff denials observed :
  check_denials denials = true <->
  exists valuation, CompletedModel denials observed valuation.
Proof.
  split.
  - intro H; exists (fun a => In a saturation); split.
    + split; [apply saturation_model | now apply check_denials_spec].
    + intros a Ha; reflexivity.
  - intros [valuation [H _]]. apply denial_model_exists_iff; now exists valuation.
Qed.

Inductive Formula : Type :=
| atom : Atom -> Formula
| bottom : Formula
| conjunction : Formula -> Formula -> Formula
| disjunction : Formula -> Formula -> Formula
| implication : Formula -> Formula -> Formula.

Fixpoint formula_atoms (f : Formula) : list Atom :=
  match f with
  | atom a => [a]
  | bottom => []
  | conjunction f g | disjunction f g | implication f g =>
      formula_atoms f ++ formula_atoms g
  end.

Fixpoint satisfies (valuation : Atom -> Prop) (f : Formula) : Prop :=
  match f with
  | atom a => valuation a
  | bottom => False
  | conjunction f g => satisfies valuation f /\ satisfies valuation g
  | disjunction f g => satisfies valuation f \/ satisfies valuation g
  | implication f g => satisfies valuation f -> satisfies valuation g
  end.

Fixpoint evaluate (f : Formula) : bool :=
  match f with
  | atom a => member a saturation
  | bottom => false
  | conjunction f g => evaluate f && evaluate g
  | disjunction f g => evaluate f || evaluate g
  | implication f g => negb (evaluate f) || evaluate g
  end.

Lemma satisfies_extensional f valuation other :
  (forall a, In a (formula_atoms f) -> (valuation a <-> other a)) ->
  (satisfies valuation f <-> satisfies other f).
Proof.
  induction f; simpl; intro H.
  - apply H; simpl; auto.
  - reflexivity.
  - rewrite IHf1, IHf2; [reflexivity | |];
      intros a Ha; apply H, in_app_iff; auto.
  - rewrite IHf1, IHf2; [reflexivity | |];
      intros a Ha; apply H, in_app_iff; auto.
  - rewrite IHf1, IHf2; [reflexivity | |];
      intros a Ha; apply H, in_app_iff; auto.
Qed.

Theorem formula_evalb_spec f :
  satisfies (fun a => In a saturation) f <-> evaluate f = true.
Proof.
  induction f; simpl.
  - symmetry; apply member_spec.
  - intuition discriminate.
  - rewrite IHf1, IHf2, andb_true_iff; reflexivity.
  - rewrite IHf1, IHf2, orb_true_iff; reflexivity.
  - rewrite IHf1, IHf2. destruct (evaluate f1), (evaluate f2); simpl;
      intuition discriminate.
Qed.

Theorem completed_formula_reflection denials observed valuation f :
  CompletedModel denials observed valuation ->
  incl (formula_atoms f) observed ->
  (satisfies valuation f <-> evaluate f = true).
Proof.
  intros [_ HD] Hf. rewrite <- formula_evalb_spec.
  apply satisfies_extensional; intros a Ha; apply HD, Hf, Ha.
Qed.

Theorem completed_formula_consequence denials observed f :
  check_denials denials = true -> incl (formula_atoms f) observed ->
  ((forall valuation, CompletedModel denials observed valuation -> satisfies valuation f)
    <-> evaluate f = true).
Proof.
  intros HC Hf; split.
  - intro H. destruct (proj1 (completed_model_exists_iff denials observed) HC)
      as [valuation HV].
    apply (proj1 (completed_formula_reflection denials observed valuation f HV Hf)), H, HV.
  - intros H valuation HV.
    apply (proj2 (completed_formula_reflection denials observed valuation f HV Hf)), H.
Qed.

(** Any embedding of these finite clauses into a separately specified source
    rule system transports saturation soundness.  No converse source-to-finite
    completeness, or consistency of a concrete source, is assumed here. *)
Theorem saturation_source_sound (SourceRules : list Atom -> Atom -> Prop) :
  (forall ps a, Rules ps a -> SourceRules ps a) ->
  forall a, In a saturation -> GroundHorn.Derives SourceRules a.
Proof.
  intros Hinclude a Ha. apply saturation_least with (a := a); [|exact Ha].
  intros ps c HR HP. eapply GroundHorn.by_rule; [apply Hinclude, HR |].
  apply GroundHorn.derivesAll_iff, HP.
Qed.

End FiniteSystem.

Section Regressions.
Definition example_clauses : list (list nat * nat) :=
  [([1], 2); ([], 0); ([0], 1); ([4], 4)].

Example chain_computes :
  member Nat.eq_dec 2 (saturation Nat.eq_dec example_clauses) = true.
Proof. reflexivity. Qed.

Example unsupported_cycle_rejected :
  member Nat.eq_dec 4 (saturation Nat.eq_dec example_clauses) = false.
Proof. reflexivity. Qed.

Example consistent_denials_accepted :
  check_denials Nat.eq_dec example_clauses [[3]; [4]] = true.
Proof. reflexivity. Qed.

Example derived_denial_rejected :
  check_denials Nat.eq_dec example_clauses [[2]] = false.
Proof. reflexivity. Qed.

Example negative_completion_computes :
  evaluate Nat.eq_dec example_clauses (implication (atom 4) bottom) = true.
Proof. reflexivity. Qed.
End Regressions.

Print Assumptions rounds_closed.
Print Assumptions saturation_exact.
Print Assumptions saturation_least.
Print Assumptions saturation_size.
Print Assumptions denial_model_exists_iff.
Print Assumptions denied_atoms_empty.
Print Assumptions constrained_consequence_exact.
Print Assumptions fixed_finite_model.
Print Assumptions completed_model_exists_iff.
Print Assumptions formula_evalb_spec.
Print Assumptions completed_formula_reflection.
Print Assumptions completed_formula_consequence.
Print Assumptions saturation_source_sound.
Print Assumptions consistent_denials_accepted.
Print Assumptions derived_denial_rejected.
Print Assumptions negative_completion_computes.
End FiniteHorn.
