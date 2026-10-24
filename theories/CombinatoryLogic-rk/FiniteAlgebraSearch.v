From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat.
Import ListNotations.

(** Exhaustive search for TOTAL operations on a FIXED finite domain.
    A key is an operation symbol together with its semantic argument tuple.
    This file does not assume an accepted candidate interpretation.  It
    enumerates all tables and proves completeness for any pointwise-extensional
    executable checker.  Successful search constructs a total interpretation;
    failure proves nonexistence on this particular fixed domain, not on every
    finite domain.  No functional extensionality is used. *)
Module FiniteAlgebraSearch.

Section Tables.
Context {Key Value : Type}.
Variable key_eq_dec : forall x y : Key, {x = y} + {x <> y}.
Variable keys : list Key.
Variable values : list Value.
Variable default : Value.

Definition Table := list (Key * Value).

Fixpoint enumerate (ks : list Key) : list Table :=
  match ks with
  | [] => [[]]
  | k :: rest =>
      flat_map (fun v => map (cons (k, v)) (enumerate rest)) values
  end.

Definition tables : list Table := enumerate keys.

Fixpoint interpret (table : Table) (k : Key) : Value :=
  match table with
  | [] => default
  | (j, v) :: rest => if key_eq_dec k j then v else interpret rest k
  end.

Lemma enumerate_length ks : length (enumerate ks) = length values ^ length ks.
Proof.
  induction ks as [|k ks IH]; simpl; [reflexivity |].
  rewrite flat_map_constant_length with (c := length (enumerate ks)).
  - now rewrite IH.
  - intros v Hv; apply length_map.
Qed.

Theorem tables_length : length tables = length values ^ length keys.
Proof. apply enumerate_length. Qed.

Lemma enumerate_shape ks table :
  In table (enumerate ks) -> map fst table = ks.
Proof.
  revert table; induction ks as [|k ks IH]; intros table H; simpl in H.
  - destruct H as [<- | []]; reflexivity.
  - apply in_flat_map in H; destruct H as [v [_ H]].
    apply in_map_iff in H; destruct H as [rest [<- H]].
    simpl; f_equal; now apply IH.
Qed.

Theorem table_length table : In table tables -> length table = length keys.
Proof.
  intro H; pose proof (enumerate_shape keys table H) as E.
  apply (f_equal (@length Key)) in E; now rewrite length_map in E.
Qed.

Lemma enumerate_values ks table :
  In table (enumerate ks) -> forall k v, In (k, v) table -> In v values.
Proof.
  revert table; induction ks as [|j ks IH]; intros table H k v Hv; simpl in H.
  - destruct H as [<- | []]; contradiction.
  - apply in_flat_map in H; destruct H as [w [Hw H]].
    apply in_map_iff in H; destruct H as [rest [<- Hr]].
    simpl in Hv; destruct Hv as [E | Hv].
    + inversion E; subst; exact Hw.
    + eapply IH; eassumption.
Qed.

Lemma canonical_enumerated (f : Key -> Value) ks :
  (forall k, In k ks -> In (f k) values) ->
  In (map (fun k => (k, f k)) ks) (enumerate ks).
Proof.
  intro H; induction ks as [|k ks IH]; simpl; [now left |].
  apply in_flat_map; exists (f k); split.
  - apply H; now left.
  - apply in_map; apply IH; intros j Hj; apply H; now right.
Qed.

Lemma interpret_canonical (f : Key -> Value) ks k :
  In k ks -> interpret (map (fun j => (j, f j)) ks) k = f k.
Proof.
  induction ks as [|j ks IH]; simpl; intro H; [contradiction |].
  destruct (key_eq_dec k j) as [-> | Hneq]; [reflexivity |].
  apply IH; destruct H as [H | H]; [congruence | exact H].
Qed.

Hypothesis key_complete : forall k : Key, In k keys.
Hypothesis value_complete : forall v : Value, In v values.

(** The default makes lookup syntactically total.  On every enumerated
    table every semantic key is present, so no lookup uses that fallback. *)
Theorem interpreted_value_present table k :
  In table tables -> In (k, interpret table k) table.
Proof.
  intro Htable.
  assert (Hkey : In k (map fst table)).
  { rewrite (enumerate_shape keys table Htable); apply key_complete. }
  clear Htable; induction table as [|[j v] rest IH]; simpl in *.
  - contradiction.
  - destruct (key_eq_dec k j) as [-> | Hneq]; [now left |].
    right; apply IH; destruct Hkey as [H | H]; [congruence | exact H].
Qed.

Theorem interpreted_value_allowed table k :
  In table tables -> In (interpret table k) values.
Proof.
  intro H; eapply enumerate_values; [exact H |].
  now apply interpreted_value_present.
Qed.

Theorem tables_complete (f : Key -> Value) :
  exists table, In table tables /\ forall k, interpret table k = f k.
Proof.
  exists (map (fun k => (k, f k)) keys); split.
  - apply canonical_enumerated; intros; apply value_complete.
  - intro k; apply interpret_canonical, key_complete.
Qed.

Definition Checker := (Key -> Value) -> bool.
Definition Extensional (check : Checker) :=
  forall f g, (forall k, f k = g k) -> check f = check g.

Definition search (check : Checker) : option Table :=
  find (fun table => check (interpret table)) tables.

Theorem search_sound check table :
  search check = Some table ->
  In table tables /\ check (interpret table) = true.
Proof. apply find_some. Qed.

Theorem search_complete check :
  Extensional check -> forall f, check f = true ->
  exists table, search check = Some table.
Proof.
  intros HE f Hf.
  destruct (tables_complete f) as [table [Ht Hagree]].
  assert (Hcheck : check (interpret table) = true).
  { rewrite (HE (interpret table) f Hagree); exact Hf. }
  destruct (search check) as [found |] eqn:Hsearch; [now exists found |].
  unfold search in Hsearch; apply find_none with (x := table) in Hsearch;
    [congruence | exact Ht].
Qed.

Theorem search_exists_iff check :
  Extensional check ->
  (exists table, search check = Some table) <->
  exists f : Key -> Value, check f = true.
Proof.
  intro HE; split.
  - intros [table H]; exists (interpret table); now apply search_sound in H.
  - intros [f H]; eapply search_complete; eassumption.
Qed.

Theorem search_none_iff check :
  Extensional check ->
  (search check = None <-> forall f : Key -> Value, check f = false).
Proof.
  intro HE; split.
  - intros Hnone f; destruct (check f) eqn:Hf; [|reflexivity].
    destruct (search_complete check HE f Hf) as [table H]; congruence.
  - intro H; destruct (search check) as [table |] eqn:E; [|reflexivity].
    apply search_sound in E; specialize (H (interpret table)); intuition congruence.
Qed.

Section ExactModel.
Variable check : Checker.
Hypothesis check_extensional : Extensional check.
Variable Model : (Key -> Value) -> Prop.
Hypothesis check_exact : forall f, check f = true <-> Model f.

Theorem returned_model table : search check = Some table -> Model (interpret table).
Proof. intro H; apply check_exact; now apply search_sound in H. Qed.

Theorem fixed_domain_model_decision :
  (exists table, search check = Some table) <-> exists f, Model f.
Proof.
  rewrite (search_exists_iff check check_extensional).
  split; intros [f H]; exists f; now apply check_exact.
Qed.

Theorem fixed_domain_no_model :
  search check = None <-> ~ exists f, Model f.
Proof.
  split.
  - intros Hnone [f Hf]; apply check_exact in Hf.
    pose proof (proj1 (search_none_iff check check_extensional) Hnone f) as Hfalse.
    congruence.
  - intro Hnone; destruct (search check) as [table |] eqn:H; [|reflexivity].
    exfalso; apply Hnone; exists (interpret table); now apply returned_model.
Qed.
End ExactModel.

End Tables.

Section Regressions.
(** This non-PTS test searches for a unary operation satisfying the universal
    sentence f(x) <> x on the complete Boolean domain.  Both semantic values
    are checked.  The returned operation is Boolean negation, not a supplied
    candidate.  Requiring a fixed point as well is rejected. *)
Definition boolean_domain : list bool := [false; true].
Definition no_fixed_points (f : bool -> bool) : bool :=
  forallb (fun x => negb (Bool.eqb (f x) x)) boolean_domain.

Lemma no_fixed_points_extensional : Extensional no_fixed_points.
Proof.
  intros f g H; unfold no_fixed_points; simpl.
  now rewrite (H false), (H true).
Qed.

Example search_finds_negation :
  search Bool.bool_dec boolean_domain boolean_domain false no_fixed_points =
  Some [(false, true); (true, false)].
Proof. reflexivity. Qed.

Example returned_operation_satisfies_every_valuation :
  exists table,
    search Bool.bool_dec boolean_domain boolean_domain false no_fixed_points = Some table /\
    forall x, interpret Bool.bool_dec false table x <> x.
Proof.
  exists [(false, true); (true, false)]; split; [reflexivity |].
  intros []; discriminate.
Qed.

Example impossible_fixed_domain_constraints_rejected :
  search Bool.bool_dec boolean_domain boolean_domain false
    (fun f => andb (no_fixed_points f) (Bool.eqb (f false) false)) = None.
Proof. reflexivity. Qed.
End Regressions.

Print Assumptions tables_length.
Print Assumptions table_length.
Print Assumptions interpreted_value_present.
Print Assumptions interpreted_value_allowed.
Print Assumptions tables_complete.
Print Assumptions search_sound.
Print Assumptions search_complete.
Print Assumptions search_exists_iff.
Print Assumptions search_none_iff.
Print Assumptions returned_model.
Print Assumptions fixed_domain_model_decision.
Print Assumptions fixed_domain_no_model.
Print Assumptions no_fixed_points_extensional.
Print Assumptions search_finds_negation.
Print Assumptions returned_operation_satisfies_every_valuation.
Print Assumptions impossible_fixed_domain_constraints_rejected.
End FiniteAlgebraSearch.
