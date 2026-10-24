From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk.Combinatory Require Import GroundHorn.
Import ListNotations.

(** Explicit numerical fragments of independently specified Horn deductions.
    Syntax size, syntax depth and proof height are separate budgets.  No guard
    mentions the desired interpretation, typing judgment or soundness result.
    A quantified rule advances the proof-height stratum; it is not asserted
    to close the last stratum under another unbounded inference. *)
Module GuardedHornFragments.
Section System.
Context {Atom : Type}.
Variable Rules : list Atom -> Atom -> Prop.
Variables size depth : Atom -> nat.

Definition Guard N d a := size a <= N /\ depth a <= d.

Inductive Proof : Atom -> Type :=
| by_rule premises conclusion :
    Rules premises conclusion -> Proofs premises -> Proof conclusion
with Proofs : list Atom -> Type :=
| proofs_nil : Proofs []
| proofs_cons a rest : Proof a -> Proofs rest -> Proofs (a :: rest).

Scheme Proof_ind' := Induction for Proof Sort Prop
  with Proofs_ind' := Induction for Proofs Sort Prop.

Fixpoint proof_height a (p : Proof a) : nat :=
  match p with by_rule _ _ _ ps => S (proofs_height _ ps) end
with proofs_height ps (p : Proofs ps) : nat :=
  match p with
  | proofs_nil => 0
  | proofs_cons a rest q qs => Nat.max (proof_height a q) (proofs_height rest qs)
  end.

Fixpoint proof_max (weight : Atom -> nat) a (p : Proof a) : nat :=
  match p with
  | by_rule ps a _ qs => Nat.max (weight a) (proofs_max weight ps qs)
  end
with proofs_max (weight : Atom -> nat) ps (p : Proofs ps) : nat :=
  match p with
  | proofs_nil => 0
  | proofs_cons a rest q qs =>
      Nat.max (proof_max weight a q) (proofs_max weight rest qs)
  end.

Definition proof_size a (p : Proof a) := proof_max size a p.
Definition proof_depth a (p : Proof a) := proof_max depth a p.

Inductive Bounded : nat -> nat -> nat -> Atom -> Prop :=
| bounded_rule h N d premises conclusion :
    Rules premises conclusion -> Guard N d conclusion ->
    BoundedAll h N d premises -> Bounded (S h) N d conclusion
with BoundedAll : nat -> nat -> nat -> list Atom -> Prop :=
| bounded_nil h N d : BoundedAll h N d []
| bounded_cons h N d a rest :
    Bounded h N d a -> BoundedAll h N d rest ->
    BoundedAll h N d (a :: rest).

Scheme Bounded_ind' := Induction for Bounded Sort Prop
  with BoundedAll_ind' := Induction for BoundedAll Sort Prop.

Lemma bounded_all_iff h N d premises :
  BoundedAll h N d premises <-> Forall (Bounded h N d) premises.
Proof.
  split.
  - intro H; induction H; constructor; assumption.
  - intro H; induction H; constructor; assumption.
Qed.

Theorem bounded_step h N d premises conclusion :
  Rules premises conclusion -> Guard N d conclusion ->
  Forall (Bounded h N d) premises -> Bounded (S h) N d conclusion.
Proof.
  intros HR HG HP; eapply bounded_rule; [exact HR|exact HG|].
  apply bounded_all_iff; exact HP.
Qed.

Theorem bounded_sound h N d a :
  Bounded h N d a -> GroundHorn.Derives Rules a.
Proof.
  intro H; induction H using Bounded_ind' with
    (P0 := fun h N d ps _ => GroundHorn.DerivesAll Rules ps).
  - eapply GroundHorn.by_rule; eassumption.
  - constructor.
  - constructor; assumption.
Qed.

Theorem bounded_monotone h N d a : Bounded h N d a ->
  forall h' N' d', h <= h' -> N <= N' -> d <= d' -> Bounded h' N' d' a.
Proof.
  intro H; induction H using Bounded_ind' with
    (P0 := fun h N d ps _ => forall h' N' d',
      h <= h' -> N <= N' -> d <= d' -> BoundedAll h' N' d' ps).
  - intros h' N' d' HH HN HD; destruct h' as [|h']; [lia|].
    eapply bounded_rule; [eassumption| |].
    + unfold Guard in *; lia.
    + apply IHBounded; lia.
  - intros; constructor.
  - intros; constructor; [apply IHBounded | apply IHBounded0]; assumption.
Qed.

Lemma bounded_all_monotone h N d ps : BoundedAll h N d ps ->
  forall h' N' d', h <= h' -> N <= N' -> d <= d' -> BoundedAll h' N' d' ps.
Proof.
  intros HP h' N' d' HH HN HD.
  apply bounded_all_iff in HP; apply bounded_all_iff.
  induction HP; constructor; eauto using bounded_monotone.
Qed.

Theorem bounded_guard h N d a : Bounded h N d a -> Guard N d a.
Proof. intro H; inversion H; assumption. Qed.

Theorem bounded_zero N d a : ~ Bounded 0 N d a.
Proof. intro H; inversion H. Qed.

Theorem proof_computed_bounds a (p : Proof a) :
  Bounded (proof_height a p) (proof_size a p) (proof_depth a p) a.
Proof.
  unfold proof_size, proof_depth.
  induction p using Proof_ind' with
    (P0 := fun ps qs => BoundedAll (proofs_height ps qs)
      (proofs_max size ps qs) (proofs_max depth ps qs) ps); cbn.
  - eapply bounded_rule; [eassumption| |].
    + unfold Guard; split; apply Nat.le_max_l.
    + eapply bounded_all_monotone; [exact IHp|lia|apply Nat.le_max_r|apply Nat.le_max_r].
  - constructor.
  - constructor.
    + eapply bounded_monotone; [exact IHp|apply Nat.le_max_l|apply Nat.le_max_l|apply Nat.le_max_l].
    + eapply bounded_all_monotone; [exact IHp0|apply Nat.le_max_r|apply Nat.le_max_r|apply Nat.le_max_r].
Qed.

Theorem proof_exact a : inhabited (Proof a) <-> GroundHorn.Derives Rules a.
Proof.
  split.
  - intros [p]; apply bounded_sound with
      (h := proof_height a p) (N := proof_size a p) (d := proof_depth a p).
    apply proof_computed_bounds.
  - intro H; refine (GroundHorn.Derives_ind' Rules
      (fun a _ => inhabited (Proof a))
      (fun ps _ => inhabited (Proofs ps)) _ _ _ a H).
    + intros ps b HR HP [qs]; constructor; econstructor; eassumption.
    + constructor; constructor.
    + intros b rest HB [p] HR [ps].
      constructor; constructor; assumption.
Qed.

Theorem finite_budget_coverage a : GroundHorn.Derives Rules a <->
  exists h N d, Bounded h N d a.
Proof.
  split.
  - intro H; apply proof_exact in H; destruct H as [p].
    exists (proof_height a p), (proof_size a p), (proof_depth a p).
    apply proof_computed_bounds.
  - intros (h & N & d & H); eapply bounded_sound; exact H.
Qed.

Theorem finite_family_coverage atoms :
  Forall (GroundHorn.Derives Rules) atoms <->
  exists h N d, Forall (Bounded h N d) atoms.
Proof.
  split.
  - intro HP; induction HP as [|a rest HA HP IH].
    + exists 0, 0, 0; constructor.
    + apply finite_budget_coverage in HA.
      destruct HA as (h & N & d & HB), IH as (k & M & e & HQ).
      exists (Nat.max h k), (Nat.max N M), (Nat.max d e); constructor.
      * eapply bounded_monotone; [exact HB|apply Nat.le_max_l|apply Nat.le_max_l|apply Nat.le_max_l].
      * apply bounded_all_iff.
        eapply bounded_all_monotone; [apply bounded_all_iff; exact HQ|apply Nat.le_max_r|apply Nat.le_max_r|apply Nat.le_max_r].
  - intros (h & N & d & HP); induction HP; constructor; eauto using bounded_sound.
Qed.

(** [staged] is false outside the chosen height range. Its Horn schemas have
    predicates P_0,...,P_H and send premises at h to a head at S h. *)
Definition staged H N d h a := h <= H /\ Bounded h N d a.

Theorem staged_overflow H N d h a : H < h -> ~ staged H N d h a.
Proof. unfold staged; lia. Qed.

Theorem staged_step H N d h premises conclusion :
  h < H -> Rules premises conclusion -> Guard N d conclusion ->
  Forall (staged H N d h) premises -> staged H N d (S h) conclusion.
Proof.
  intros HH HR HG HP; split; [lia|].
  eapply bounded_step; [exact HR|exact HG|].
  apply Forall_forall; intros a HA.
  apply Forall_forall with (x := a) in HP; [exact (proj2 HP)|exact HA].
Qed.

Theorem staged_quantified_rule {Valuation : Type} H N d h
  (premises : Valuation -> list Atom) (conclusion : Valuation -> Atom) :
  (forall rho, Rules (premises rho) (conclusion rho)) ->
  forall rho, h < H -> Guard N d (conclusion rho) ->
    Forall (staged H N d h) (premises rho) ->
    staged H N d (S h) (conclusion rho).
Proof. intros HR rho HH HG HP; eapply staged_step; eauto. Qed.

Theorem staged_sound H N d h a : staged H N d h a -> GroundHorn.Derives Rules a.
Proof. intros [_ HB]; eapply bounded_sound; exact HB. Qed.

Theorem staged_family_coverage atoms :
  Forall (GroundHorn.Derives Rules) atoms <->
  exists H N d, Forall (staged H N d H) atoms.
Proof.
  split.
  - intro HP; apply finite_family_coverage in HP.
    destruct HP as (H & N & d & HP); exists H, N, d.
    induction HP; constructor; [split; [lia|assumption]|assumption].
  - intros (H & N & d & HP); induction HP; constructor; eauto using staged_sound.
Qed.

Theorem staged_denial H N d h (forbidden : Atom -> Prop) :
  (forall a, forbidden a -> ~ GroundHorn.Derives Rules a) ->
  forall a, forbidden a -> ~ staged H N d h a.
Proof. intros HF a HA HB; apply (HF a HA); eapply staged_sound; exact HB. Qed.

End System.

(** Even with no syntax growth, a height-bounded relation need not satisfy
    a rule at the SAME height: its premise can use the entire budget. *)
Inductive ChainRule : list nat -> nat -> Prop :=
| chain_zero : ChainRule [] 0
| chain_next n : ChainRule [n] (S n).

Lemma chain_height_bound h N d n :
  Bounded ChainRule (fun _ => 0) (fun _ => 0) h N d n -> n < h.
Proof.
  intro HB; refine (Bounded_ind' ChainRule (fun _ => 0) (fun _ => 0)
    (fun h N d n _ => n < h)
    (fun h N d ps _ => Forall (fun n => n < h) ps) _ _ _ h N d n HB).
  - intros k s t ps a HR HG HP IH.
    inversion HR; subst; [lia|]. inversion IH; subst; lia.
  - intros; constructor.
  - intros; constructor; assumption.
Qed.

Theorem same_level_closure_fails :
  Bounded ChainRule (fun _ => 0) (fun _ => 0) 1 0 0 0 /\
  ChainRule [0] 1 /\
  ~ Bounded ChainRule (fun _ => 0) (fun _ => 0) 1 0 0 1.
Proof.
  split.
  - apply bounded_step with (premises := []); constructor; unfold Guard; lia.
  - split; [constructor|]. intro H; apply chain_height_bound in H; lia.
Qed.

Print Assumptions bounded_all_iff.
Print Assumptions bounded_step.
Print Assumptions bounded_sound.
Print Assumptions bounded_monotone.
Print Assumptions bounded_all_monotone.
Print Assumptions bounded_guard.
Print Assumptions bounded_zero.
Print Assumptions proof_computed_bounds.
Print Assumptions proof_exact.
Print Assumptions finite_budget_coverage.
Print Assumptions finite_family_coverage.
Print Assumptions staged_overflow.
Print Assumptions staged_step.
Print Assumptions staged_quantified_rule.
Print Assumptions staged_sound.
Print Assumptions staged_family_coverage.
Print Assumptions staged_denial.
Print Assumptions chain_height_bound.
Print Assumptions same_level_closure_fails.
End GuardedHornFragments.
