From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat.
From Stdlib Require Vectors.Vector.
From PTSrk.Combinatory Require Import FiniteHorn FiniteUniversalHorn.
Import ListNotations.

(** Literal first-order constructor/predicate signature of the adjacent MM0
    specification.  NAT, TM and TEL are separate sorts, interpreted here on
    separate copies of one supplied finite carrier D.  Constructor operations
    are total on EVERY appropriately sorted tuple.  This equicardinal
    specialization does not claim completeness for unequal sort cardinalities.

    These Rocq trees are an explicit transcription interface, not a verified
    parser for MM0 text.  Every variable valuation is semantic, not restricted
    to denotations of selected ground syntax. *)
Module MM0FiniteSignature.

Inductive Sort := NAT | TM | TEL.
Definition sort_eq_dec (x y : Sort) : {x = y} + {x <> y}.
Proof. decide equality. Defined.
Definition sort_eqb x y := if sort_eq_dec x y then true else false.

Inductive Expr :=
| EVar : nat -> Expr
| EZ : Expr
| ES : Expr -> Expr
| EU : Expr -> Expr
| EV : Expr -> Expr
| EApp : Expr -> Expr -> Expr
| EPi : Expr -> Expr -> Expr
| ELam : Expr -> Expr -> Expr
| ENil : Expr
| ECons : Expr -> Expr -> Expr -> Expr.

Inductive Predicate :=
| PLe | PLt | PMax | PLift | PSub | PRed | PStel | PPrefix | PForm | PAx | PH.
Definition predicate_eq_dec (x y : Predicate) : {x = y} + {x <> y}.
Proof. decide equality. Defined.
Definition Atom := (Predicate * list Expr)%type.

Record PositiveRule := mkPositiveRule {
  variables : list Sort;
  premises : list Atom;
  conclusion : Atom
}.
Record NegativeRule := mkNegativeRule {
  nvariables : list Sort;
  npremises : list Atom
}.

Inductive Op := OZ | OS | OU | OV | OApp | OPi | OLam | ONil | OCons.
Definition arity o :=
  match o with OZ | ONil => 0 | OS | OU | OV => 1
  | OApp | OPi | OLam => 2 | OCons => 3 end.
Definition operation_inputs o :=
  match o with
  | OZ | ONil => []
  | OS | OU | OV => [NAT]
  | OApp | OPi | OLam => [TM; TM]
  | OCons => [TM; NAT; TEL]
  end.
Definition operation_output o :=
  match o with OZ | OS => NAT | ONil | OCons => TEL | _ => TM end.
Definition operations := [OZ; OS; OU; OV; OApp; OPi; OLam; ONil; OCons].
Definition op_eq_dec (x y : Op) : {x = y} + {x <> y}.
Proof. decide equality. Defined.
Theorem operations_complete o : In o operations.
Proof. destruct o; cbn; tauto. Qed.
Lemma arity_inputs o : length (operation_inputs o) = arity o.
Proof. destruct o; reflexivity. Qed.

Definition expected_sort (actual : option Sort) (expected : Sort) : bool :=
  match actual with Some s => sort_eqb s expected | None => false end.
Fixpoint infer_sort (env : list Sort) e : option Sort :=
  match e with
  | EVar i => nth_error env i
  | EZ => Some NAT
  | ES x => if expected_sort (infer_sort env x) NAT then Some NAT else None
  | EU x | EV x => if expected_sort (infer_sort env x) NAT then Some TM else None
  | EApp x y | EPi x y | ELam x y =>
      if expected_sort (infer_sort env x) TM && expected_sort (infer_sort env y) TM
      then Some TM else None
  | ENil => Some TEL
  | ECons x a l =>
      if expected_sort (infer_sort env x) TM && expected_sort (infer_sort env a) NAT
        && expected_sort (infer_sort env l) TEL then Some TEL else None
  end.
Definition predicate_inputs p :=
  match p with
  | PLe | PLt => [NAT; NAT]
  | PMax => [NAT; NAT; NAT]
  | PLift => [NAT; TM; TM]
  | PSub => [NAT; TM; TM; TM]
  | PRed | PAx | PH => [TM; TM]
  | PStel => [NAT; NAT; NAT; TEL]
  | PPrefix => [NAT; TEL; TEL]
  | PForm => [NAT; TEL; TM; TM; TM; TM]
  end.
Fixpoint arguments_sorted env args sorts :=
  match args, sorts with
  | [], [] => true
  | e :: es, s :: ss => expected_sort (infer_sort env e) s && arguments_sorted env es ss
  | _, _ => false
  end.
Definition atom_sorted env (a : Atom) := arguments_sorted env (snd a) (predicate_inputs (fst a)).
Definition positive_sorted r :=
  forallb (atom_sorted (variables r)) (premises r) && atom_sorted (variables r) (conclusion r).
Definition negative_sorted r := forallb (atom_sorted (nvariables r)) (npremises r).

(** Independent many-sorted formation judgment.  These are first-order
    signature sorts, not a replacement PTS typing judgment. *)
Inductive SortedExpr (env : list Sort) : Expr -> Sort -> Prop :=
| sorted_var i s : nth_error env i = Some s -> SortedExpr env (EVar i) s
| sorted_zero : SortedExpr env EZ NAT
| sorted_succ x : SortedExpr env x NAT -> SortedExpr env (ES x) NAT
| sorted_universe x : SortedExpr env x NAT -> SortedExpr env (EU x) TM
| sorted_variable x : SortedExpr env x NAT -> SortedExpr env (EV x) TM
| sorted_app x y : SortedExpr env x TM -> SortedExpr env y TM -> SortedExpr env (EApp x y) TM
| sorted_pi x y : SortedExpr env x TM -> SortedExpr env y TM -> SortedExpr env (EPi x y) TM
| sorted_lam x y : SortedExpr env x TM -> SortedExpr env y TM -> SortedExpr env (ELam x y) TM
| sorted_nil : SortedExpr env ENil TEL
| sorted_cons x a l : SortedExpr env x TM -> SortedExpr env a NAT ->
    SortedExpr env l TEL -> SortedExpr env (ECons x a l) TEL.

Lemma expected_sort_exact actual expected :
  expected_sort actual expected = true <-> actual = Some expected.
Proof.
  destruct actual as [s |]; unfold expected_sort, sort_eqb;
    [destruct (sort_eq_dec s expected) |]; intuition congruence.
Qed.
Theorem infer_sort_exact env e s : infer_sort env e = Some s <-> SortedExpr env e s.
Proof.
  split.
  - revert s; induction e; intros s H; cbn [infer_sort] in H.
    + now constructor.
    + inversion H; constructor.
    + destruct (expected_sort (infer_sort env e) NAT) eqn:He; [|discriminate].
      inversion H; subst; constructor; apply IHe, expected_sort_exact, He.
    + destruct (expected_sort (infer_sort env e) NAT) eqn:He; [|discriminate].
      inversion H; subst; constructor; apply IHe, expected_sort_exact, He.
    + destruct (expected_sort (infer_sort env e) NAT) eqn:He; [|discriminate].
      inversion H; subst; constructor; apply IHe, expected_sort_exact, He.
    + destruct (expected_sort (infer_sort env e1) TM && expected_sort (infer_sort env e2) TM)
        eqn:He; [|discriminate].
      apply andb_true_iff in He; destruct He as [H1 H2]; inversion H; subst; constructor;
        [apply IHe1 | apply IHe2]; now apply expected_sort_exact.
    + destruct (expected_sort (infer_sort env e1) TM && expected_sort (infer_sort env e2) TM)
        eqn:He; [|discriminate].
      apply andb_true_iff in He; destruct He as [H1 H2]; inversion H; subst; constructor;
        [apply IHe1 | apply IHe2]; now apply expected_sort_exact.
    + destruct (expected_sort (infer_sort env e1) TM && expected_sort (infer_sort env e2) TM)
        eqn:He; [|discriminate].
      apply andb_true_iff in He; destruct He as [H1 H2]; inversion H; subst; constructor;
        [apply IHe1 | apply IHe2]; now apply expected_sort_exact.
    + inversion H; constructor.
    + destruct (expected_sort (infer_sort env e1) TM && expected_sort (infer_sort env e2) NAT
        && expected_sort (infer_sort env e3) TEL) eqn:He; [|discriminate].
      apply andb_true_iff in He; destruct He as [H12 H3].
      apply andb_true_iff in H12; destruct H12 as [H1 H2].
      inversion H; subst; constructor; [apply IHe1 | apply IHe2 | apply IHe3];
        now apply expected_sort_exact.
  - intro H; induction H; cbn [infer_sort]; rewrite ?IHSortedExpr, ?IHSortedExpr1,
      ?IHSortedExpr2, ?IHSortedExpr3; try reflexivity; assumption.
Qed.
Theorem arguments_sorted_exact env args sorts :
  arguments_sorted env args sorts = true <-> Forall2 (SortedExpr env) args sorts.
Proof.
  revert sorts; induction args as [|e es IH]; intros [|s ss]; cbn [arguments_sorted].
  - split; intros; constructor.
  - split; [discriminate |intro H; inversion H].
  - split; [discriminate |intro H; inversion H].
  - rewrite andb_true_iff, expected_sort_exact, infer_sort_exact, IH.
    split; [intros [H1 H2]; now constructor |intro H; inversion H; auto].
Qed.
Theorem atom_sorted_exact env x :
  atom_sorted env x = true <-> Forall2 (SortedExpr env) (snd x) (predicate_inputs (fst x)).
Proof. apply arguments_sorted_exact. Qed.

Fixpoint Scoped (k : nat) e : Prop :=
  match e with
  | EVar i => i < k
  | EZ | ENil => True
  | ES x | EU x | EV x => Scoped k x
  | EApp x y | EPi x y | ELam x y => Scoped k x /\ Scoped k y
  | ECons x a l => Scoped k x /\ Scoped k a /\ Scoped k l
  end.
Theorem sorted_scoped env e s : SortedExpr env e s -> Scoped (length env) e.
Proof.
  intro H; induction H; cbn [Scoped]; intuition.
  apply nth_error_Some; rewrite H; discriminate.
Qed.

Definition Algebra (D : Type) := forall o : Op, Vector.t D (arity o) -> D.
Definition GroundAtom (D : Type) := (Predicate * list D)%type.
Definition ground_atom_eq_dec {D} (value_eq_dec : forall x y : D, {x = y} + {x <> y})
  (x y : GroundAtom D) : {x = y} + {x <> y}.
Proof.
  destruct x as [p xs], y as [q ys].
  destruct (predicate_eq_dec p q) as [Hp | Hp]; [subst q | right; congruence].
  destruct (list_eq_dec value_eq_dec xs ys) as [Hs | Hs]; [subst ys; left; reflexivity | right; congruence].
Defined.

Section Semantics.
Context {D : Type}.
Variable default : D.
Variable algebra : Algebra D.

Fixpoint evaluate (env : list D) e : D :=
  match e with
  | EVar i => nth i env default
  | EZ => algebra OZ (Vector.nil D)
  | ES x => algebra OS (Vector.cons D (evaluate env x) 0 (Vector.nil D))
  | EU x => algebra OU (Vector.cons D (evaluate env x) 0 (Vector.nil D))
  | EV x => algebra OV (Vector.cons D (evaluate env x) 0 (Vector.nil D))
  | EApp x y => algebra OApp (Vector.cons D (evaluate env x) 1
      (Vector.cons D (evaluate env y) 0 (Vector.nil D)))
  | EPi x y => algebra OPi (Vector.cons D (evaluate env x) 1
      (Vector.cons D (evaluate env y) 0 (Vector.nil D)))
  | ELam x y => algebra OLam (Vector.cons D (evaluate env x) 1
      (Vector.cons D (evaluate env y) 0 (Vector.nil D)))
  | ENil => algebra ONil (Vector.nil D)
  | ECons x a l => algebra OCons (Vector.cons D (evaluate env x) 2
      (Vector.cons D (evaluate env a) 1 (Vector.cons D (evaluate env l) 0 (Vector.nil D))))
  end.
Definition evaluate_atom env (a : Atom) : GroundAtom D :=
  (fst a, map (evaluate env) (snd a)).
Definition positive_schema (r : PositiveRule) : @FiniteUniversalHorn.PositiveSchema D (GroundAtom D) :=
  existT _ (length (variables r)) (fun env =>
    (map (evaluate_atom (Vector.to_list env)) (premises r),
      evaluate_atom (Vector.to_list env) (conclusion r))).
Definition negative_schema (r : NegativeRule) : @FiniteUniversalHorn.NegativeSchema D (GroundAtom D) :=
  existT _ (length (nvariables r)) (fun env =>
    map (evaluate_atom (Vector.to_list env)) (npremises r)).
Definition positive_schemata rules := map positive_schema rules.
Definition negative_schemata rules := map negative_schema rules.

Definition PositiveSatisfaction rules (truth : GroundAtom D -> Prop) :=
  forall r, In r rules -> forall env : Vector.t D (length (variables r)),
    Forall (fun a => truth (evaluate_atom (Vector.to_list env) a)) (premises r) ->
    truth (evaluate_atom (Vector.to_list env) (conclusion r)).
Definition NegativeSatisfaction rules (truth : GroundAtom D -> Prop) :=
  forall r, In r rules -> forall env : Vector.t D (length (nvariables r)),
    ~ Forall (fun a => truth (evaluate_atom (Vector.to_list env) a)) (npremises r).
Definition Model positive negative truth :=
  PositiveSatisfaction positive truth /\ NegativeSatisfaction negative truth.

Theorem positive_schema_exact rules truth :
  PositiveSatisfaction rules truth <->
  FiniteUniversalHorn.PositiveSatisfaction (positive_schemata rules) truth.
Proof.
  split.
  - intros H s Hs; apply in_map_iff in Hs; destruct Hs as [r [<- Hr]].
    intro env; cbn; intro HP; apply H with (r := r); [exact Hr |].
    now rewrite Forall_map in HP.
  - intros H r Hr env HP.
    assert (Hs : In (positive_schema r) (positive_schemata rules)) by now apply in_map.
    specialize (H _ Hs env); cbn in H; rewrite Forall_map in H; exact (H HP).
Qed.
Theorem negative_schema_exact rules truth :
  NegativeSatisfaction rules truth <->
  FiniteUniversalHorn.NegativeSatisfaction (negative_schemata rules) truth.
Proof.
  split.
  - intros H s Hs; apply in_map_iff in Hs; destruct Hs as [r [<- Hr]].
    intros env HP; apply (H r Hr env); cbn in HP; now rewrite Forall_map in HP.
  - intros H r Hr env HP.
    assert (Hs : In (negative_schema r) (negative_schemata rules)) by now apply in_map.
    specialize (H _ Hs env); cbn in H; rewrite Forall_map in H; exact (H HP).
Qed.
Theorem schema_correspondence positive negative truth :
  Model positive negative truth <->
  FiniteUniversalHorn.UniversalModel (positive_schemata positive) (negative_schemata negative) truth.
Proof. unfold Model, FiniteUniversalHorn.UniversalModel.
  rewrite positive_schema_exact, negative_schema_exact; reflexivity. Qed.

Variable elements : list D.
Variable value_eq_dec : forall x y : D, {x = y} + {x <> y}.
Definition compile_positive rules :=
  FiniteUniversalHorn.compile_positive elements (positive_schemata rules).
Definition compile_negative rules :=
  FiniteUniversalHorn.compile_negative elements (negative_schemata rules).
Definition check_candidate positive negative :=
  FiniteUniversalHorn.check_candidate elements (ground_atom_eq_dec value_eq_dec)
    (positive_schemata positive) (negative_schemata negative).

Theorem candidate_exact (complete : forall x, In x elements) positive negative :
  check_candidate positive negative = true <-> exists truth, Model positive negative truth.
Proof.
  unfold check_candidate; rewrite (FiniteUniversalHorn.candidate_satisfiable_iff
    elements complete (ground_atom_eq_dec value_eq_dec)).
  split; intros [truth H]; exists truth; now apply schema_correspondence.
Qed.
Theorem ground_compilation_exact (complete : forall x, In x elements) positive negative truth :
  Model positive negative truth <->
  FiniteHorn.ConsistentModel (compile_positive positive) (compile_negative negative) truth.
Proof.
  rewrite schema_correspondence; apply FiniteUniversalHorn.universal_grounding_exact, complete.
Qed.
End Semantics.

Section Extensionality.
Context {D : Type}.
Variable default : D.
Variables a b : Algebra D.
Hypothesis agree : forall o args, a o args = b o args.

Theorem evaluate_extensional env e : evaluate default a env e = evaluate default b env e.
Proof.
  induction e; cbn [evaluate]; try reflexivity;
    rewrite ?IHe, ?IHe1, ?IHe2, ?IHe3; apply agree.
Qed.
Theorem evaluate_atom_extensional env x :
  evaluate_atom default a env x = evaluate_atom default b env x.
Proof.
  destruct x as [p xs]; unfold evaluate_atom; cbn; f_equal.
  apply map_ext; apply evaluate_extensional.
Qed.
Theorem compile_positive_extensional elements rules :
  compile_positive default a elements rules = compile_positive default b elements rules.
Proof.
  unfold compile_positive, positive_schemata, FiniteUniversalHorn.compile_positive.
  induction rules as [|r rest IH]; cbn [map flat_map]; [reflexivity |].
  f_equal; [|exact IH].
  unfold FiniteUniversalHorn.positive_instances, positive_schema; cbn.
  apply map_ext; intro env; f_equal.
  - apply map_ext; apply evaluate_atom_extensional.
  - apply evaluate_atom_extensional.
Qed.
Theorem compile_negative_extensional elements rules :
  compile_negative default a elements rules = compile_negative default b elements rules.
Proof.
  unfold compile_negative, negative_schemata, FiniteUniversalHorn.compile_negative.
  induction rules as [|r rest IH]; cbn [map flat_map]; [reflexivity |].
  f_equal; [|exact IH].
  unfold FiniteUniversalHorn.negative_instances, negative_schema; cbn.
  apply map_ext; intro env; apply map_ext; apply evaluate_atom_extensional.
Qed.
Theorem checker_extensional elements value_eq_dec positive negative :
  check_candidate default a elements value_eq_dec positive negative =
  check_candidate default b elements value_eq_dec positive negative.
Proof.
  change (FiniteHorn.check_denials (ground_atom_eq_dec value_eq_dec)
    (compile_positive default a elements positive) (compile_negative default a elements negative) =
    FiniteHorn.check_denials (ground_atom_eq_dec value_eq_dec)
    (compile_positive default b elements positive) (compile_negative default b elements negative)).
  now rewrite compile_positive_extensional, compile_negative_extensional.
Qed.
End Extensionality.

Section FallbackIndependence.
Context {D : Type}.
Variables first_default second_default : D.
Variable algebra : Algebra D.
Theorem evaluate_default_independent env e : Scoped (length env) e ->
  evaluate first_default algebra env e = evaluate second_default algebra env e.
Proof.
  induction e; cbn [Scoped evaluate]; intros H; try reflexivity;
    try (now rewrite IHe).
  - apply nth_indep, H.
  - destruct H; now rewrite IHe1, IHe2.
  - destruct H; now rewrite IHe1, IHe2.
  - destruct H; now rewrite IHe1, IHe2.
  - destruct H as [H1 [H2 H3]]; now rewrite IHe1, IHe2, IHe3.
Qed.
Lemma vector_list_length n (v : Vector.t D n) : length (Vector.to_list v) = n.
Proof. apply Vector.length_to_list. Qed.
Theorem sorted_evaluation_ignores_default env e s (v : Vector.t D (length env)) :
  infer_sort env e = Some s ->
  evaluate first_default algebra (Vector.to_list v) e =
  evaluate second_default algebra (Vector.to_list v) e.
Proof.
  intro H; apply evaluate_default_independent; rewrite vector_list_length.
  apply sorted_scoped with (s := s), infer_sort_exact, H.
Qed.
End FallbackIndependence.

Print Assumptions operations_complete.
Print Assumptions arity_inputs.
Print Assumptions infer_sort_exact.
Print Assumptions arguments_sorted_exact.
Print Assumptions atom_sorted_exact.
Print Assumptions sorted_scoped.
Print Assumptions positive_schema_exact.
Print Assumptions negative_schema_exact.
Print Assumptions schema_correspondence.
Print Assumptions candidate_exact.
Print Assumptions ground_compilation_exact.
Print Assumptions evaluate_extensional.
Print Assumptions evaluate_atom_extensional.
Print Assumptions compile_positive_extensional.
Print Assumptions compile_negative_extensional.
Print Assumptions checker_extensional.
Print Assumptions evaluate_default_independent.
Print Assumptions sorted_evaluation_ignores_default.
End MM0FiniteSignature.
