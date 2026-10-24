From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import AbstractRewriting Reduction DefEq.
From PTSrk.NormalizationComplexity Require Import Rank Bounds.
From PTSrk.Combinatory Require Import FiniteNormalForms HilbertFiniteModels.
Import ListNotations RankEstimate.

(** Decidable finite beta graphs for the ORIGINAL annotated syntax.
    All path states, including annotations and conversion witnesses, must
    occur in the selected finite list. No typing or normalization premise
    occurs in the evaluator or its independently generated path relation. *)
Module GuardedBetaGraphs.
Module FNF := FiniteNormalForms.FiniteNormalForms.

Definition root_successors {n} (f x : Term nat n) : list (Term nat n) :=
  match f with lam _ b => [subst b x] | _ => [] end.

Fixpoint successors {n} (t : Term nat n) : list (Term nat n) :=
  match t with
  | 𝓤 _ | var _ => []
  | Π A B => map (fun A' => Π A' B) (successors A) ++
             map (fun B' => Π A B') (successors B)
  | lam A b => map (fun A' => lam A' b) (successors A) ++
               map (fun b' => lam A b') (successors b)
  | app f x => root_successors f x ++
               map (fun f' => app f' x) (successors f) ++
               map (fun x' => app f x') (successors x)
  end.

Lemma root_successors_sound n (f x u : Term nat n) :
  In u (root_successors f x) -> step nat n (app f x) u.
Proof.
  destruct f; cbn [root_successors]; try contradiction.
  intros [<-|H]; [constructor|contradiction].
Qed.

Theorem successors_sound n (t u : Term nat n) :
  In u (successors t) -> step nat n t u.
Proof.
  revert u; induction t; intros u H; cbn [successors] in H; try contradiction.
  - apply in_app_iff in H as [H|H]; apply in_map_iff in H;
      destruct H as [v [<- HV]]; constructor; auto.
  - apply in_app_iff in H as [H|H]; apply in_map_iff in H;
      destruct H as [v [<- HV]]; constructor; auto.
  - apply in_app_iff in H as [H|H]; [now apply root_successors_sound|].
    apply in_app_iff in H as [H|H]; apply in_map_iff in H;
      destruct H as [v [<- HV]]; constructor; auto.
Qed.

Theorem successors_complete n (t u : Term nat n) :
  step nat n t u -> In u (successors t).
Proof.
  intro H; induction H; cbn [successors].
  - apply in_or_app; left; apply in_map_iff; exists T'; auto.
  - apply in_or_app; right; apply in_map_iff; exists U'; auto.
  - apply in_or_app; left; apply in_map_iff; exists T'; auto.
  - apply in_or_app; right; apply in_map_iff; exists t'; auto.
  - apply in_or_app; right; apply in_or_app; left; apply in_map_iff; exists f'; auto.
  - apply in_or_app; right; apply in_or_app; right; apply in_map_iff; exists t'; auto.
  - apply in_or_app; left; left; reflexivity.
Qed.

Theorem successors_exact n (t u : Term nat n) :
  In u (successors t) <-> step nat n t u.
Proof. split; [apply successors_sound|apply successors_complete]. Qed.

Definition member {n} (t : Term nat n) xs : bool :=
  if in_dec HilbertFiniteModels.term_eq_dec t xs then true else false.
Definition equal {n} (t u : Term nat n) : bool :=
  if HilbertFiniteModels.term_eq_dec t u then true else false.
Definition edge {n} (t u : Term nat n) := member u (successors t).

Lemma member_exact n (t : Term nat n) xs : member t xs = true <-> In t xs.
Proof. unfold member; destruct (in_dec _ _ _); split; auto; discriminate. Qed.
Lemma equal_exact n (t u : Term nat n) : equal t u = true <-> t = u.
Proof. unfold equal; destruct (HilbertFiniteModels.term_eq_dec t u); split; auto; discriminate. Qed.
Theorem edge_exact n (t u : Term nat n) : edge t u = true <-> step nat n t u.
Proof. unfold edge; rewrite member_exact; apply successors_exact. Qed.

Section Paths.
Context {n : nat}.

Inductive Reach (xs : list (Term nat n)) : nat -> Term nat n -> Term nat n -> Prop :=
| reach_refl k t : In t xs -> Reach xs k t t
| reach_step k t u v : In t xs -> step nat n t u -> Reach xs k u v ->
    Reach xs (S k) t v.

Fixpoint reaches (xs : list (Term nat n)) k t u : bool :=
  member t xs && (equal t u ||
    match k with
    | 0 => false
    | S k' => existsb (fun v => edge t v && reaches xs k' v u) xs
    end).

Lemma reach_source xs k t u : Reach xs k t u -> In t xs.
Proof. intro H; inversion H; assumption. Qed.

Lemma reach_target xs k t u : Reach xs k t u -> In u xs.
Proof. intro H; induction H; assumption. Qed.

Theorem reaches_sound xs k t u : reaches xs k t u = true -> Reach xs k t u.
Proof.
  revert t u; induction k as [|k IH]; intros t u H; cbn [reaches] in H;
    apply andb_true_iff in H as [HT H]; apply member_exact in HT;
    apply orb_true_iff in H as [H|H].
  - apply equal_exact in H; subst u; constructor; exact HT.
  - discriminate.
  - apply equal_exact in H; subst u; constructor; exact HT.
  - apply existsb_exists in H as [v [HV H]]; apply andb_true_iff in H as [HE HP].
    eapply reach_step; [exact HT|apply edge_exact, HE|apply IH, HP].
Qed.

Theorem reaches_complete xs k t u : Reach xs k t u -> reaches xs k t u = true.
Proof.
  intro H; induction H.
  - destruct k; cbn [reaches]; apply andb_true_iff; split;
      try (now apply member_exact).
    all: apply orb_true_iff; left; apply equal_exact; reflexivity.
  - cbn [reaches]; apply andb_true_iff; split; [apply member_exact, H|].
    apply orb_true_iff; right; apply existsb_exists; exists u; split.
    + eapply reach_source; exact H1.
    + apply andb_true_iff; split; [apply edge_exact, H0|exact IHReach].
Qed.

Theorem reaches_exact xs k t u : reaches xs k t u = true <-> Reach xs k t u.
Proof. split; [apply reaches_sound|apply reaches_complete]. Qed.

Theorem reach_sound xs k t u : Reach xs k t u -> reduces_to nat n t u.
Proof.
  intro H; induction H; [constructor|]. eapply rtc_step; eassumption.
Qed.

Theorem reaches_native_sound xs k t u :
  reaches xs k t u = true -> reduces_to nat n t u.
Proof. intro H; apply reach_sound with (xs := xs) (k := k), reaches_sound, H. Qed.

Theorem reach_mono xs k t u : Reach xs k t u ->
  forall ys l, (forall x, In x xs -> In x ys) -> k <= l -> Reach ys l t u.
Proof.
  intro H; induction H; intros ys l Hxy Hkl.
  - constructor; auto.
  - destruct l; [lia|]. eapply reach_step; [auto|eassumption|apply IHReach; auto; lia].
Qed.

Theorem reach_compose xs k l t u v :
  Reach xs k t u -> Reach xs l u v -> Reach xs (k + l) t v.
Proof.
  intros H; induction H; intro Q.
  - eapply reach_mono; [exact Q|auto|lia].
  - cbn; eapply reach_step; [exact H|exact H0|apply IHReach, Q].
Qed.

Theorem reaches_monotone xs ys k l t u :
  (forall x, In x xs -> In x ys) -> k <= l ->
  reaches xs k t u = true -> reaches ys l t u = true.
Proof.
  intros HI HK HP; apply reaches_complete.
  eapply reach_mono; [apply reaches_sound, HP|exact HI|exact HK].
Qed.

Theorem reaches_compose xs k l t u v :
  reaches xs k t u = true -> reaches xs l u v = true ->
  reaches xs (k + l) t v = true.
Proof.
  intros HP HQ; apply reaches_complete; eapply reach_compose;
    apply reaches_sound; eassumption.
Qed.

Theorem reduction_finite_support t u : reduces_to nat n t u ->
  exists k xs, Reach xs k t u.
Proof.
  intro H; induction H as [t|t v u HE HP IH].
  - exists 0, [t]; constructor; left; reflexivity.
  - destruct IH as [k [xs HQ]]; exists (S k), (t :: xs).
    eapply reach_step; [left; reflexivity|exact HE|].
    eapply reach_mono; [exact HQ|intros x HX; right; exact HX|lia].
Qed.

Definition joins xs k l t u :=
  existsb (fun v => reaches xs k t v && reaches xs l u v) xs.

Theorem joins_exact xs k l t u : joins xs k l t u = true <->
  exists v, Reach xs k t v /\ Reach xs l u v.
Proof.
  unfold joins; rewrite existsb_exists; split.
  - intros [v [HV H]]; apply andb_true_iff in H as [HT HU].
    exists v; split; apply reaches_exact; assumption.
  - intros [v [HT HU]]; exists v; split; [eapply reach_target; exact HT|].
    apply andb_true_iff; split; apply reaches_exact; assumption.
Qed.

Theorem joins_sound xs k l t u : joins xs k l t u = true -> def_equiv nat n t u.
Proof.
  intro H; apply joins_exact in H as [v [HT HU]]; apply def_equiv_prop.
  exists v; split; eapply reach_sound; eassumption.
Qed.

Theorem joins_monotone xs ys k l k' l' t u :
  (forall x, In x xs -> In x ys) -> k <= k' -> l <= l' ->
  joins xs k l t u = true -> joins ys k' l' t u = true.
Proof.
  intros HI HK HL HP; apply joins_exact in HP as [v [HT HU]].
  apply joins_exact; exists v; split; eapply reach_mono; eauto.
Qed.

Theorem conversion_finite_support t u : def_equiv nat n t u ->
  exists k l xs, joins xs k l t u = true.
Proof.
  intro H; apply def_equiv_prop in H as [v [HT HU]].
  apply reduction_finite_support in HT as [k [xs HT]].
  apply reduction_finite_support in HU as [l [ys HU]].
  exists k, l, (xs ++ ys); apply joins_exact; exists v; split.
  - eapply reach_mono; [exact HT|intros x HX; apply in_or_app; left; exact HX|lia].
  - eapply reach_mono; [exact HU|intros x HX; apply in_or_app; right; exact HX|lia].
Qed.

End Paths.

(** Computed numeric envelopes include every intermediate, and independently
    bound universe labels.  [d] here is syntactic depth/label magnitude, not
    the rank of a PTS type.  No beta-reduction closure of a fixed envelope is
    asserted: an escaping edge is absent from its finite graph. *)
Definition maximum {X : Type} (weight : X -> nat) (xs : list X) :=
  fold_right Nat.max 0 (map weight xs).

Lemma maximum_covers X weight (xs : list X) x :
  In x xs -> weight x <= maximum weight xs.
Proof.
  unfold maximum; induction xs as [|y xs IH]; cbn; [contradiction|].
  intros [<-|H]; [apply Nat.le_max_l|specialize (IH H); lia].
Qed.

Definition label_bound {n} (t : Term nat n) := maximum (fun i => i) (FNF.labels t).
Definition size_envelope {n} (xs : list (Term nat n)) := maximum nodes xs.
Definition depth_envelope {n} (xs : list (Term nat n)) :=
  Nat.max (maximum FNF.depth xs) (maximum label_bound xs).

Definition syntax_states n N d : list (Term nat n) :=
  filter (fun t => Nat.leb (nodes t) N) (FNF.terms d n (seq 0 (S d))).

Theorem syntax_states_exact n N d t : In t (syntax_states n N d) <->
  nodes t <= N /\ FNF.depth t <= d /\ (forall i, In i (FNF.labels t) -> i <= d).
Proof.
  unfold syntax_states; rewrite filter_In, Nat.leb_le, FNF.terms_iff.
  unfold FNF.Uses; split.
  - intros [[HD HL] HN]; repeat split; auto.
    intros i HI; specialize (HL i HI); apply in_seq in HL; lia.
  - intros [HN [HD HL]]; repeat split; auto.
    intros i HI; apply in_seq; specialize (HL i HI); lia.
Qed.

Theorem syntax_envelope_covers n (xs : list (Term nat n)) t :
  In t xs -> In t (syntax_states n (size_envelope xs) (depth_envelope xs)).
Proof.
  intro HT; apply syntax_states_exact; unfold size_envelope, depth_envelope.
  split; [apply maximum_covers, HT|]; split.
  - pose proof (maximum_covers _ FNF.depth xs t HT); lia.
  - intros i HI; pose proof (maximum_covers _ label_bound xs t HT).
    pose proof (maximum_covers _ (fun i => i) (FNF.labels t) i HI).
    unfold label_bound in *; lia.
Qed.

Theorem syntax_states_finite_bound n N d :
  length (syntax_states n N d) <= tower 2 (4 * d + n + 5).
Proof.
  unfold syntax_states; eapply Nat.le_trans; [apply filter_length_le|].
  pose proof (FNF.terms_length_bound d n (seq 0 (S d))) as H.
  rewrite length_seq in H; replace (3 * d + n + S d + 4) with (4 * d + n + 5) in H by lia.
  exact H.
Qed.

Theorem reduction_numeric_coverage n (t u : Term nat n) :
  reduces_to nat n t u -> exists k N d, reaches (syntax_states n N d) k t u = true.
Proof.
  intro H; apply reduction_finite_support in H as [k [xs HP]].
  exists k, (size_envelope xs), (depth_envelope xs); apply reaches_complete.
  eapply reach_mono; [exact HP|apply syntax_envelope_covers|lia].
Qed.

Theorem reduction_numeric_exact n (t u : Term nat n) :
  reduces_to nat n t u <-> exists k N d, reaches (syntax_states n N d) k t u = true.
Proof.
  split; [apply reduction_numeric_coverage|].
  intros (k & N & d & H); eapply reaches_native_sound; exact H.
Qed.

Theorem conversion_numeric_coverage n (t u : Term nat n) :
  def_equiv nat n t u -> exists k l N d, joins (syntax_states n N d) k l t u = true.
Proof.
  intro H; apply conversion_finite_support in H as (k & l & xs & HP).
  exists k, l, (size_envelope xs), (depth_envelope xs).
  eapply joins_monotone with (xs := xs) (k := k) (l := l);
    [apply syntax_envelope_covers|lia|lia|exact HP].
Qed.

Theorem conversion_numeric_exact n (t u : Term nat n) :
  def_equiv nat n t u <-> exists k l N d, joins (syntax_states n N d) k l t u = true.
Proof.
  split; [apply conversion_numeric_coverage|].
  intros (k & l & N & d & H); eapply joins_sound; exact H.
Qed.

(** Small executable regressions use explicit state lists, not the much
    larger exhaustive syntax enumeration. *)
Definition test_identity : Term nat 0 := lam (𝓤 0) (var fzero).
Definition test_redex : Term nat 0 := app test_identity (𝓤 0).
Definition test_states : list (Term nat 0) := [test_redex; 𝓤 0].

Example one_step_regression : reaches test_states 1 test_redex (𝓤 0) = true.
Proof. reflexivity. Qed.

Example zero_step_regression : reaches test_states 0 test_redex (𝓤 0) = false.
Proof. reflexivity. Qed.

Example missing_state_regression :
  reaches [test_redex] 1 test_redex (𝓤 0) = false /\
  reaches [] 0 (@𝓤 nat 0 0) (𝓤 0) = false.
Proof. split; reflexivity. Qed.

Example common_reduct_regression :
  joins test_states 1 0 test_redex (𝓤 0) = true /\
  joins test_states 0 1 (𝓤 0) test_redex = true.
Proof. split; reflexivity. Qed.

Example annotation_reduction_regression :
  edge (lam test_redex (var fzero)) test_identity = true.
Proof. reflexivity. Qed.

Print Assumptions root_successors_sound.
Print Assumptions successors_sound.
Print Assumptions successors_complete.
Print Assumptions successors_exact.
Print Assumptions member_exact.
Print Assumptions equal_exact.
Print Assumptions edge_exact.
Print Assumptions reach_source.
Print Assumptions reach_target.
Print Assumptions reaches_sound.
Print Assumptions reaches_complete.
Print Assumptions reaches_exact.
Print Assumptions reach_sound.
Print Assumptions reaches_native_sound.
Print Assumptions reach_mono.
Print Assumptions reach_compose.
Print Assumptions reaches_monotone.
Print Assumptions reaches_compose.
Print Assumptions reduction_finite_support.
Print Assumptions joins_exact.
Print Assumptions joins_sound.
Print Assumptions joins_monotone.
Print Assumptions conversion_finite_support.
Print Assumptions maximum_covers.
Print Assumptions syntax_states_exact.
Print Assumptions syntax_envelope_covers.
Print Assumptions syntax_states_finite_bound.
Print Assumptions reduction_numeric_coverage.
Print Assumptions reduction_numeric_exact.
Print Assumptions conversion_numeric_coverage.
Print Assumptions conversion_numeric_exact.
Print Assumptions one_step_regression.
Print Assumptions zero_step_regression.
Print Assumptions missing_state_regression.
Print Assumptions common_reduct_regression.
Print Assumptions annotation_reduction_regression.
End GuardedBetaGraphs.
