(** Two precise boundaries for the next soundness invariant.  These reject
    particular proposed proof bridges, NOT all fixed-rank interpretations.
    All statements concern the original annotated syntax and typing rules. *)
From Stdlib Require Import Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Inversions DefEq Reduction SN Ranks.
From PTSrk.SelfConsistency Require Import NativeProofCodes.

Module InvariantObstructions.
Import NativeProofCodes.NativeProofCodes.

Definition implication {n} (P Q : Term nat n) : Term nat n :=
  Π P (shift Q).

Theorem implication_sorted {n} (G : Ctx nat n) P Q r s :
  @typ nat RankSorts n G P (𝓤 r) ->
  @typ nat RankSorts n G Q (𝓤 s) ->
  @typ nat RankSorts n G (implication P Q) (𝓤 (Nat.max (S r) s)).
Proof.
  intros HP HQ. unfold implication.
  eapply typ_Π with (ℓₜ := r) (ℓᵤ := s).
  - exact HP.
  - exact (weakening RankSorts Q (𝓤 s) P HQ).
  - reflexivity.
Qed.

Lemma sort_unique {n} (G : Ctx nat n) P r s :
  @typ nat RankSorts n G P (𝓤 r) ->
  @typ nat RankSorts n G P (𝓤 s) -> r = s.
Proof.
  intros Hr Hs. apply (@equiv_𝓤_inversion nat n r s).
  eapply uniqueness_of_typing; eassumption.
Qed.

Theorem implication_not_below_domain {n} (G : Ctx nat n) P Q r s k :
  @typ nat RankSorts n G P (𝓤 r) ->
  @typ nat RankSorts n G Q (𝓤 s) -> k <= r ->
  ~ @typ nat RankSorts n G (implication P Q) (𝓤 k).
Proof.
  intros HP HQ Hk Hbad.
  pose proof (sort_unique G _ _ _
    (implication_sorted G P Q r s HP HQ) Hbad) as E.
  pose proof (Nat.le_max_l (S r) s). lia.
Qed.

Theorem implication_not_same_rank {n} (G : Ctx nat n) P r :
  @typ nat RankSorts n G P (𝓤 r) ->
  ~ @typ nat RankSorts n G (implication P P) (𝓤 r).
Proof.
  intro HP. eapply implication_not_below_domain;
    [exact HP | exact HP | reflexivity].
Qed.

(** Opening the output Church algebra does not suffice when the newly
    generalized environment assumption still has the motive's own rank.
    A callback E -> P fits U_r exactly when E has strictly smaller rank. *)
Theorem implication_fits_motive_iff {n} (G : Ctx nat n) E P e r :
  @typ nat RankSorts n G E (𝓤 e) ->
  @typ nat RankSorts n G P (𝓤 r) ->
  (@typ nat RankSorts n G (implication E P) (𝓤 r) <-> e < r).
Proof.
  intros HE HP. split.
  - intro H. pose proof (sort_unique G _ _ _
      (implication_sorted G E P e r HE HP) H) as Er.
    pose proof (Nat.le_max_l (S e) r). lia.
  - intro Her. pose proof (implication_sorted G E P e r HE HP) as H.
    replace (Nat.max (S e) r) with r in H by lia. exact H.
Qed.

(** If a Church graph's proof type is above its motive, a motive that
    quantifies over one such graph proof cannot be recovered by merely
    raising every chosen index together.  This arithmetic is the literal
    product-rank calculation proved above, not an encoding impossibility. *)
Theorem graph_premise_motive_cycle motive_rank graph_rank output_rank :
  motive_rank < graph_rank ->
  motive_rank < Nat.max (S graph_rank) output_rank.
Proof. pose proof (Nat.le_max_l (S graph_rank) output_rank). lia. Qed.

(** Raw equality certificates may pass through an untyped beta-loop even
    when both endpoints are the same well-typed sort.  Do not impose strong
    normalization of every intermediate on the independent checker. *)
Definition delta : Term nat 0 :=
  lam (𝓤 0) (app (var fzero) (var fzero)).
Definition omega : Term nat 0 := app delta delta.
Definition detour_step : StepCode 0 := Contract (𝓤 0) (𝓤 0) omega.
Definition detour : EqualityCode 0 :=
  Transitivity (Symmetry (Reduce detour_step)) (Reduce detour_step).
Definition detour_middle : Term nat 0 := step_source detour_step.
Definition detour_certificate : Certificate 0 :=
  ConversionRule (𝓤 1) (𝓤 0) (𝓤 0) 0
    (SortRule 1) (SortRule 0) detour.

Theorem detour_equality_accepted :
  equality_check detour = true /\
  equality_source detour = 𝓤 0 /\ equality_target detour = 𝓤 0.
Proof. repeat split; reflexivity. Qed.

Theorem detour_typing_accepted : check ε detour_certificate = true.
Proof. reflexivity. Qed.

Theorem omega_beta_loop : step nat 0 omega omega.
Proof.
  change (step nat 0 (app (lam (𝓤 0) (app (var fzero) (var fzero))) delta)
    (subst (app (var fzero) (var fzero)) delta)).
  apply step_beta.
Qed.

Theorem detour_middle_beta_loop : step nat 0 detour_middle detour_middle.
Proof. apply step_app_right. exact omega_beta_loop. Qed.

Theorem detour_middle_reduces_to_sort : step nat 0 detour_middle (𝓤 0).
Proof. apply step_beta. Qed.

Lemma accessible_irreflexive {A} (R : A -> A -> Prop) x :
  SN.Acc R x -> ~ R x x.
Proof.
  intro H. induction H as [x Hnext IH].
  intro Hloop. exact (IH x Hloop Hloop).
Qed.

Theorem detour_middle_not_strongly_normalizing : ~ sn detour_middle.
Proof.
  intro H. exact (accessible_irreflexive _ _ H detour_middle_beta_loop).
Qed.

Theorem detour_middle_untypable (A : Term nat 0) :
  ~ @typ nat RankSorts 0 ε detour_middle A.
Proof.
  intro H. apply detour_middle_not_strongly_normalizing.
  eapply strong_normalization; [constructor | exact H].
Qed.

End InvariantObstructions.
