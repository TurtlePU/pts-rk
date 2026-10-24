From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat Logic.Eqdep_dec.
From Stdlib Require Vectors.Vector.
From PTSrk.Combinatory Require Import FiniteUniversalHorn FiniteAlgebraSearch.
Import ListNotations.

(** Finite total interpretations of an arity-indexed operation signature.
    Each operation accepts EVERY tuple over the SAME fixed semantic domain.
    Enumeration is complete for all total operations, not just chosen native
    terms or reachable bounded states.  The exact-model theorem is an interface
    for a separately verified syntactic checker, not a PTS model-existence
    assumption.  No functional extensionality is used. *)
Module FiniteOperationAlgebras.
Section Signature.
Context {Op D : Type}.
Variable arity : Op -> nat.

Definition Key := {o : Op & Vector.t D (arity o)}.
Definition Algebra := forall o : Op, Vector.t D (arity o) -> D.

Definition expand (f : Key -> D) : Algebra :=
  fun o args => f (existT _ o args).
Definition flatten (algebra : Algebra) (key : Key) : D :=
  algebra (projT1 key) (projT2 key).

Lemma expand_flatten algebra o args : expand (flatten algebra) o args = algebra o args.
Proof. reflexivity. Qed.

Lemma flatten_expand f key : flatten (expand f) key = f key.
Proof. destruct key; reflexivity. Qed.

Variable op_eq_dec : forall x y : Op, {x = y} + {x <> y}.
Variable value_eq_dec : forall x y : D, {x = y} + {x <> y}.

Definition value_eqb x y : bool := if value_eq_dec x y then true else false.

Lemma value_eqb_exact x y : value_eqb x y = true <-> x = y.
Proof. unfold value_eqb; destruct (value_eq_dec x y); intuition discriminate. Qed.

Definition vector_eq_dec n : forall x y : Vector.t D n, {x = y} + {x <> y} :=
  Vector.eq_dec D value_eqb value_eqb_exact n.

Definition key_eq_dec (x y : Key) : {x = y} + {x <> y}.
Proof.
  destruct x as [o xs], y as [p ys].
  destruct (op_eq_dec o p) as [E | E].
  - subst p; destruct (vector_eq_dec (arity o) xs ys) as [H | H].
    + subst ys; left; reflexivity.
    + right; intro Heq; apply H.
      exact (inj_pair2_eq_dec Op op_eq_dec (fun o => Vector.t D (arity o)) o xs ys Heq).
  - right; intro Heq; apply E; now apply (f_equal (@projT1 Op (fun o => Vector.t D (arity o)))) in Heq.
Defined.

Variable operations : list Op.
Variable values : list D.
Variable default : D.

Definition operation_keys : list Key :=
  flat_map (fun o => map (fun args => existT (fun o => Vector.t D (arity o)) o args)
    (FiniteUniversalHorn.valuations values (arity o))) operations.

Theorem operation_keys_length :
  length operation_keys = list_sum (map (fun o => length values ^ arity o) operations).
Proof.
  unfold operation_keys; rewrite length_flat_map.
  f_equal; apply map_ext; intro o; rewrite length_map.
  apply FiniteUniversalHorn.valuations_length.
Qed.

Definition tables := FiniteAlgebraSearch.tables operation_keys values.
Definition interpret (table : @FiniteAlgebraSearch.Table Key D) : Algebra :=
  expand (FiniteAlgebraSearch.interpret key_eq_dec default table).

Theorem tables_length :
  length tables = length values ^
    list_sum (map (fun o => length values ^ arity o) operations).
Proof.
  unfold tables; rewrite FiniteAlgebraSearch.tables_length, operation_keys_length.
  reflexivity.
Qed.

Definition Checker := Algebra -> bool.
Definition Extensional (check : Checker) :=
  forall a b, (forall o args, a o args = b o args) -> check a = check b.

Definition flat_check (check : Checker) (f : Key -> D) : bool := check (expand f).

Lemma flat_check_extensional check :
  Extensional check -> FiniteAlgebraSearch.Extensional (flat_check check).
Proof.
  intros H f g Hagree; apply H; intros o args; apply Hagree.
Qed.

Definition search (check : Checker) : option (@FiniteAlgebraSearch.Table Key D) :=
  FiniteAlgebraSearch.search key_eq_dec operation_keys values default (flat_check check).

Theorem search_sound check table :
  search check = Some table -> In table tables /\ check (interpret table) = true.
Proof.
  exact (FiniteAlgebraSearch.search_sound key_eq_dec operation_keys values default
    (flat_check check) table).
Qed.

Hypothesis operations_complete : forall o : Op, In o operations.
Hypothesis values_complete : forall x : D, In x values.

Theorem operation_keys_complete : forall key : Key, In key operation_keys.
Proof.
  intros [o args]; apply in_flat_map; exists o; split; [apply operations_complete |].
  apply in_map; now apply FiniteUniversalHorn.valuations_complete.
Qed.

Theorem tables_complete (algebra : Algebra) :
  exists table, In table tables /\ forall o args, interpret table o args = algebra o args.
Proof.
  destruct (FiniteAlgebraSearch.tables_complete key_eq_dec operation_keys values default
    operation_keys_complete values_complete (flatten algebra)) as [table [Ht H]].
  exists table; split; [exact Ht | intros o args; exact (H (existT _ o args))].
Qed.

Theorem interpreted_operation_present table o args :
  In table tables -> In (existT _ o args, interpret table o args) table.
Proof.
  apply FiniteAlgebraSearch.interpreted_value_present, operation_keys_complete.
Qed.

Theorem search_complete check :
  Extensional check -> forall algebra, check algebra = true ->
  exists table, search check = Some table.
Proof.
  intros HE algebra HC.
  apply (FiniteAlgebraSearch.search_complete key_eq_dec operation_keys values default
    operation_keys_complete values_complete (flat_check check)
    (flat_check_extensional check HE) (flatten algebra)).
  unfold flat_check; rewrite (HE (expand (flatten algebra)) algebra).
  - exact HC.
  - intros; reflexivity.
Qed.

Theorem search_exists_iff check :
  Extensional check ->
  (exists table, search check = Some table) <-> exists algebra, check algebra = true.
Proof.
  intro HE; split.
  - intros [table H]; exists (interpret table); now apply search_sound in H.
  - intros [algebra H]; now apply (search_complete check HE algebra).
Qed.

Theorem search_none_iff check :
  Extensional check ->
  (search check = None <-> forall algebra, check algebra = false).
Proof.
  intro HE; split.
  - intros Hnone algebra; destruct (check algebra) eqn:HC; [|reflexivity].
    destruct (search_complete check HE algebra HC) as [table H]; congruence.
  - intro H; destruct (search check) as [table |] eqn:HS; [|reflexivity].
    apply search_sound in HS; specialize (H (interpret table)); intuition congruence.
Qed.

Section ExactModel.
Variable check : Checker.
Hypothesis check_extensional : Extensional check.
Variable Model : Algebra -> Prop.
Hypothesis check_exact : forall algebra, check algebra = true <-> Model algebra.

Theorem returned_model table : search check = Some table -> Model (interpret table).
Proof. intro H; apply check_exact; now apply search_sound in H. Qed.

Theorem fixed_domain_model_decision :
  (exists table, search check = Some table) <-> exists algebra, Model algebra.
Proof.
  rewrite (search_exists_iff check check_extensional).
  split; intros [algebra H]; exists algebra; now apply check_exact.
Qed.

Theorem fixed_domain_no_model :
  search check = None <-> ~ exists algebra, Model algebra.
Proof.
  split.
  - intros Hnone [algebra H]; apply check_exact in H.
    pose proof (proj1 (search_none_iff check check_extensional) Hnone algebra) as Hfalse.
    congruence.
  - intro Hnone; destruct (search check) as [table |] eqn:HS; [|reflexivity].
    exfalso; apply Hnone; exists (interpret table); now apply returned_model.
Qed.
End ExactModel.
End Signature.

Print Assumptions key_eq_dec.
Print Assumptions operation_keys_length.
Print Assumptions tables_length.
Print Assumptions flat_check_extensional.
Print Assumptions search_sound.
Print Assumptions operation_keys_complete.
Print Assumptions tables_complete.
Print Assumptions interpreted_operation_present.
Print Assumptions search_complete.
Print Assumptions search_exists_iff.
Print Assumptions search_none_iff.
Print Assumptions returned_model.
Print Assumptions fixed_domain_model_decision.
Print Assumptions fixed_domain_no_model.
End FiniteOperationAlgebras.
