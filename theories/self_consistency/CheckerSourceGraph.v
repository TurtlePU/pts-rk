(** Independent NATIVE source-to-operation graphs.  Their clauses retain
    operand provenance and the original conjunction topology, but contain
    neither acceptance nor evaluator/checker agreement as a premise.

    This is not yet an original-PTS internal relation: decoding, Context.index,
    original substitution and quotation below remain native operations.
    Functional agreement with the unchanged external compiler is PROVED. *)
From Stdlib Require Import Bool.Bool.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context.
From PTSrk.SelfConsistency Require Import NativeProofCodes StructuralCodes
  CertificateSerialization CheckerComparisons.

Module CheckerSourceGraph.
Module NC := NativeProofCodes.NativeProofCodes.
Module CC := CheckerComparisons.CheckerComparisons.

(** Local endpoint provenance.  In particular application records the literal
    capture-avoiding substitution in the original annotated syntax. *)
Inductive SourceFields : forall n, NC.Certificate n -> Term nat n -> Term nat n -> Prop :=
| FieldsSort {n} r : SourceFields n (NC.SortRule r) (𝓤 r) (𝓤 0)
| FieldsVariable {n} i A : SourceFields n (NC.VariableRule i A) (var i) A
| FieldsProduct {n} A B a b p q :
    SourceFields n (NC.ProductRule A B a b p q) (Π A B) (𝓤 (Nat.max (S a) b))
| FieldsAbstraction {n} A t B r p q :
    SourceFields n (NC.AbstractionRule A t B r p q) (lam A t) (Π A B)
| FieldsApplication {n} f u A B p q :
    SourceFields n (NC.ApplicationRule f u A B p q) (app f u) (subst B u)
| FieldsConversion {n} t A B r p q e :
    SourceFields n (NC.ConversionRule t A B r p q e) t B.
Arguments SourceFields {n} _ _ _.

Theorem source_fields_agreement {n} (p : NC.Certificate n) t A :
  SourceFields p t A -> t = NC.subject p /\ A = NC.type p.
Proof. intro H; destruct H; split; reflexivity. Qed.
Theorem source_fields_coverage {n} (p : NC.Certificate n) :
  SourceFields p (NC.subject p) (NC.type p).
Proof. destruct p; constructor. Qed.
Theorem source_fields_unique {n} (p : NC.Certificate n) t A u B :
  SourceFields p t A -> SourceFields p u B -> t = u /\ A = B.
Proof.
  intros H K; apply source_fields_agreement in H, K.
  destruct H, K; subst; split; reflexivity.
Qed.

Inductive StepFields : forall n, NC.StepCode n -> Term nat n -> Term nat n -> Prop :=
| StepContract {n} A b u :
    StepFields n (NC.Contract A b u) (app (lam A b) u) (subst b u)
| StepPiLeft {n} p A A' B : StepFields n p A A' ->
    StepFields n (NC.PiLeft p B) (Π A B) (Π A' B)
| StepPiRight {n} A p B B' : StepFields (S n) p B B' ->
    StepFields n (NC.PiRight A p) (Π A B) (Π A B')
| StepLamLeft {n} p A A' b : StepFields n p A A' ->
    StepFields n (NC.LamLeft p b) (lam A b) (lam A' b)
| StepLamRight {n} A p b b' : StepFields (S n) p b b' ->
    StepFields n (NC.LamRight A p) (lam A b) (lam A b')
| StepAppLeft {n} p f f' u : StepFields n p f f' ->
    StepFields n (NC.AppLeft p u) (app f u) (app f' u)
| StepAppRight {n} f p u u' : StepFields n p u u' ->
    StepFields n (NC.AppRight f p) (app f u) (app f u').
Arguments StepFields {n} _ _ _.

Theorem step_fields_agreement {n} (p : NC.StepCode n) t u :
  StepFields p t u -> t = NC.step_source p /\ u = NC.step_target p.
Proof.
  intro H; induction H; cbn [NC.step_source NC.step_target];
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    subst; split; reflexivity.
Qed.
Theorem step_fields_coverage {n} (p : NC.StepCode n) :
  StepFields p (NC.step_source p) (NC.step_target p).
Proof. induction p; constructor; assumption. Qed.
Theorem step_fields_unique {n} (p : NC.StepCode n) t u v w :
  StepFields p t u -> StepFields p v w -> t = v /\ u = w.
Proof.
  intros H K; apply step_fields_agreement in H, K.
  destruct H, K; subst; split; reflexivity.
Qed.

Inductive EqualityFields : forall n, NC.EqualityCode n -> Term nat n -> Term nat n -> Prop :=
| EqualityRefl {n} t : EqualityFields n (NC.Refl t) t t
| EqualityReduce {n} p t u : StepFields p t u ->
    EqualityFields n (NC.Reduce p) t u
| EqualitySymmetry {n} p t u : EqualityFields n p t u ->
    EqualityFields n (NC.Symmetry p) u t
| EqualityTransitivity {n} p q t u v w :
    EqualityFields n p t u -> EqualityFields n q v w ->
    EqualityFields n (NC.Transitivity p q) t w.
Arguments EqualityFields {n} _ _ _.

Theorem equality_fields_agreement {n} (p : NC.EqualityCode n) t u :
  EqualityFields p t u -> t = NC.equality_source p /\ u = NC.equality_target p.
Proof.
  intro H; induction H; cbn [NC.equality_source NC.equality_target].
  - split; reflexivity.
  - now apply step_fields_agreement.
  - destruct IHEqualityFields; subst; split; reflexivity.
  - destruct IHEqualityFields1, IHEqualityFields2; subst; split; reflexivity.
Qed.
Theorem equality_fields_coverage {n} (p : NC.EqualityCode n) :
  EqualityFields p (NC.equality_source p) (NC.equality_target p).
Proof.
  induction p; cbn [NC.equality_source NC.equality_target];
    econstructor; eauto using step_fields_coverage.
Qed.
Theorem equality_fields_unique {n} (p : NC.EqualityCode n) t u v w :
  EqualityFields p t u -> EqualityFields p v w -> t = v /\ u = w.
Proof.
  intros H K; apply equality_fields_agreement in H, K.
  destruct H, K; subst; split; reflexivity.
Qed.

(** Context.index is explicitly an EXTERNAL boundary, not an internal lookup
    theorem.  A later represented graph must replace this primitive clause. *)
Inductive Lookup {n} (G : Ctx nat n) (i : Fin n) : Term nat n -> Prop :=
| LookupIndex : Lookup G i (G !! i).
Theorem lookup_agreement {n} (G : Ctx nat n) i A :
  Lookup G i A -> A = G !! i.
Proof. intros []; reflexivity. Qed.
Theorem lookup_coverage {n} (G : Ctx nat n) i : Lookup G i (G !! i).
Proof. constructor. Qed.

Inductive Matches {n} (p : NC.Certificate n) (t A : Term nat n) : CC.Expr -> Prop :=
| MatchFields s B : SourceFields p s B ->
    Matches p t A (CC.Both (CC.Compare (encode_term s) (encode_term t))
      (CC.Compare (encode_term B) (encode_term A))).
Theorem matches_agreement {n} (p : NC.Certificate n) t A e :
  Matches p t A e -> e = CC.matches_expression p t A.
Proof.
  intros [s B H]; apply source_fields_agreement in H as [-> ->]; reflexivity.
Qed.
Theorem matches_coverage {n} (p : NC.Certificate n) t A :
  Matches p t A (CC.matches_expression p t A).
Proof. constructor; apply source_fields_coverage. Qed.

Inductive EqualityGraph : forall n, NC.EqualityCode n -> CC.Expr -> Prop :=
| GraphRefl {n} t : EqualityGraph n (NC.Refl t) (CC.Truth true)
| GraphReduce {n} p : EqualityGraph n (NC.Reduce p) (CC.Truth true)
| GraphSymmetry {n} p e : EqualityGraph n p e ->
    EqualityGraph n (NC.Symmetry p) e
| GraphTransitivity {n} p q ep eq t u v w :
    EqualityGraph n p ep -> EqualityGraph n q eq ->
    EqualityFields p t u -> EqualityFields q v w ->
    EqualityGraph n (NC.Transitivity p q)
      (CC.Both (CC.Both ep eq) (CC.Compare (encode_term u) (encode_term v))).
Arguments EqualityGraph {n} _ _.

Theorem equality_graph_agreement {n} (p : NC.EqualityCode n) e :
  EqualityGraph p e -> e = CC.equality_expression p.
Proof.
  intro H; induction H; cbn [CC.equality_expression]; try assumption; try reflexivity.
  apply equality_fields_agreement in H1 as [_ ->].
  apply equality_fields_agreement in H2 as [-> _].
  now rewrite IHEqualityGraph1, IHEqualityGraph2.
Qed.
Theorem equality_graph_coverage {n} (p : NC.EqualityCode n) :
  EqualityGraph p (CC.equality_expression p).
Proof.
  induction p; cbn [CC.equality_expression]; econstructor;
    eauto using equality_fields_coverage.
Qed.
Theorem equality_graph_unique {n} (p : NC.EqualityCode n) e f :
  EqualityGraph p e -> EqualityGraph p f -> e = f.
Proof. intros H K; rewrite (equality_graph_agreement _ _ H), (equality_graph_agreement _ _ K); reflexivity. Qed.
Theorem equality_graph_output {n} (p : NC.EqualityCode n) e b :
  EqualityGraph p e -> (CC.eval e = b <-> NC.equality_check p = b).
Proof.
  intro H; rewrite (equality_graph_agreement _ _ H), CC.eval_equality_expression; reflexivity.
Qed.

Inductive CheckGraph : forall n, Ctx nat n -> NC.Certificate n -> CC.Expr -> Prop :=
| GraphSort {n} G r : CheckGraph n G (NC.SortRule r) (CC.Truth true)
| GraphVariable {n} G i A B : Lookup G i B ->
    CheckGraph n G (NC.VariableRule i A) (CC.Compare (encode_term B) (encode_term A))
| GraphProduct {n} G A B a b p q ep eq mp mq :
    CheckGraph n G p ep -> CheckGraph (S n) (G & A) q eq ->
    Matches p A (𝓤 a) mp -> Matches q B (𝓤 b) mq ->
    CheckGraph n G (NC.ProductRule A B a b p q)
      (CC.Both (CC.Both (CC.Both ep eq) mp) mq)
| GraphAbstraction {n} G A t B r p q ep eq mp mq :
    CheckGraph n G p ep -> CheckGraph (S n) (G & A) q eq ->
    Matches p A (𝓤 r) mp -> Matches q t B mq ->
    CheckGraph n G (NC.AbstractionRule A t B r p q)
      (CC.Both (CC.Both (CC.Both ep eq) mp) mq)
| GraphApplication {n} G f u A B p q ep eq mp mq :
    CheckGraph n G p ep -> CheckGraph n G q eq ->
    Matches p f (Π A B) mp -> Matches q u A mq ->
    CheckGraph n G (NC.ApplicationRule f u A B p q)
      (CC.Both (CC.Both (CC.Both ep eq) mp) mq)
| GraphConversion {n} G t A B r p q c ep eq mp mq ec s T :
    CheckGraph n G p ep -> CheckGraph n G q eq ->
    Matches p t A mp -> Matches q B (𝓤 r) mq ->
    EqualityGraph c ec -> EqualityFields c s T ->
    CheckGraph n G (NC.ConversionRule t A B r p q c)
      (CC.Both (CC.Both (CC.Both (CC.Both (CC.Both (CC.Both ep eq) mp) mq) ec)
        (CC.Compare (encode_term s) (encode_term A)))
        (CC.Compare (encode_term T) (encode_term B))).
Arguments CheckGraph {n} _ _ _.

Theorem check_graph_agreement {n} (G : Ctx nat n) p e :
  CheckGraph G p e -> e = CC.check_expression G p.
Proof.
  intro H; induction H; cbn [CC.check_expression]; try reflexivity.
  - apply lookup_agreement in H; now subst.
  - rewrite IHCheckGraph1, IHCheckGraph2, (matches_agreement _ _ _ _ H1),
      (matches_agreement _ _ _ _ H2); reflexivity.
  - rewrite IHCheckGraph1, IHCheckGraph2, (matches_agreement _ _ _ _ H1),
      (matches_agreement _ _ _ _ H2); reflexivity.
  - rewrite IHCheckGraph1, IHCheckGraph2, (matches_agreement _ _ _ _ H1),
      (matches_agreement _ _ _ _ H2); reflexivity.
  - apply equality_fields_agreement in H4 as [-> ->].
    rewrite IHCheckGraph1, IHCheckGraph2, (matches_agreement _ _ _ _ H1),
      (matches_agreement _ _ _ _ H2), (equality_graph_agreement _ _ H3); reflexivity.
Qed.
Theorem check_graph_coverage {n} (G : Ctx nat n) p :
  CheckGraph G p (CC.check_expression G p).
Proof.
  revert G; induction p; intro G; cbn [CC.check_expression]; econstructor;
    eauto using lookup_coverage, matches_coverage, equality_graph_coverage,
      equality_fields_coverage.
Qed.
Theorem check_graph_unique {n} (G : Ctx nat n) p e f :
  CheckGraph G p e -> CheckGraph G p f -> e = f.
Proof. intros H K; rewrite (check_graph_agreement _ _ _ H), (check_graph_agreement _ _ _ K); reflexivity. Qed.
Theorem check_graph_output {n} (G : Ctx nat n) p e b :
  CheckGraph G p e -> (CC.eval e = b <-> NC.check G p = b).
Proof.
  intro H; rewrite (check_graph_agreement _ _ _ H), CC.eval_check_expression; reflexivity.
Qed.

Inductive ContextGraph : forall n, NC.ContextCode n -> CC.Expr -> Prop :=
| GraphEmpty : ContextGraph 0 NC.EmptyContext (CC.Truth true)
| GraphExtend {n} c r p ec ep t A :
    ContextGraph n c ec -> CheckGraph (NC.context c) p ep -> SourceFields p t A ->
    ContextGraph (S n) (NC.ExtendContext c r p)
      (CC.Both (CC.Both ec ep) (CC.Compare (encode_term A) (encode_term (@𝓤 nat n r)))).
Arguments ContextGraph {n} _ _.

Theorem context_graph_agreement {n} (c : NC.ContextCode n) e :
  ContextGraph c e -> e = CC.context_expression c.
Proof.
  intro H; induction H; cbn [CC.context_expression]; [reflexivity|].
  apply source_fields_agreement in H1 as [_ ->].
  now rewrite IHContextGraph, (check_graph_agreement _ _ _ H0).
Qed.
Theorem context_graph_coverage {n} (c : NC.ContextCode n) :
  ContextGraph c (CC.context_expression c).
Proof.
  induction c; cbn [CC.context_expression]; econstructor;
    eauto using check_graph_coverage, source_fields_coverage.
Qed.
Theorem context_graph_unique {n} (c : NC.ContextCode n) e f :
  ContextGraph c e -> ContextGraph c f -> e = f.
Proof. intros H K; rewrite (context_graph_agreement _ _ H), (context_graph_agreement _ _ K); reflexivity. Qed.
Theorem context_graph_output {n} (c : NC.ContextCode n) e b :
  ContextGraph c e -> (CC.eval e = b <-> NC.context_check c = b).
Proof.
  intro H; rewrite (context_graph_agreement _ _ H), CC.eval_context_expression; reflexivity.
Qed.

(** Decoding is likewise external.  Both malformed and fully scoped rejected
    inputs have graph coverage, without a typing or acceptance hypothesis. *)
Inductive RawGraph (q : code) : CC.Expr -> Prop :=
| GraphMalformed : decode_input q = None -> RawGraph q (CC.Truth false)
| GraphDecoded n c p ec ep :
    decode_input q = Some (existT _ n (c,p)) ->
    ContextGraph c ec -> CheckGraph (NC.context c) p ep ->
    RawGraph q (CC.Both ec ep).
Inductive BottomGraph (q : code) : CC.Expr -> Prop :=
| GraphBottomMalformed : decode_certificate q 0 = None -> BottomGraph q (CC.Truth false)
| GraphBottomDecoded p ep t A : decode_certificate q 0 = Some p ->
    CheckGraph ε p ep -> SourceFields p t A ->
    BottomGraph q (CC.Both ep (CC.Compare (encode_term A) (encode_term NC.Bottom))).

Theorem raw_graph_agreement q e : RawGraph q e -> e = CC.raw_check_expression q.
Proof.
  intros H; destruct H; unfold CC.raw_check_expression; rewrite H; [reflexivity|].
  now rewrite (context_graph_agreement _ _ H0), (check_graph_agreement _ _ _ H1).
Qed.
Theorem raw_graph_coverage q : RawGraph q (CC.raw_check_expression q).
Proof.
  unfold CC.raw_check_expression; destruct (decode_input q) as [[n [c p]]|] eqn:H.
  - econstructor; eauto using context_graph_coverage, check_graph_coverage.
  - constructor; exact H.
Qed.
Theorem raw_graph_unique q e f : RawGraph q e -> RawGraph q f -> e = f.
Proof. intros H K; rewrite (raw_graph_agreement _ _ H), (raw_graph_agreement _ _ K); reflexivity. Qed.
Theorem raw_graph_output q e b :
  RawGraph q e -> (CC.eval e = b <-> raw_check q = b).
Proof. intro H; rewrite (raw_graph_agreement _ _ H), CC.eval_raw_check_expression; reflexivity. Qed.

Theorem bottom_graph_agreement q e : BottomGraph q e -> e = CC.raw_bottom_expression q.
Proof.
  intros H; destruct H; unfold CC.raw_bottom_expression; rewrite H; [reflexivity|].
  apply source_fields_agreement in H1 as [_ ->].
  now rewrite (check_graph_agreement _ _ _ H0).
Qed.
Theorem bottom_graph_coverage q : BottomGraph q (CC.raw_bottom_expression q).
Proof.
  unfold CC.raw_bottom_expression; destruct (decode_certificate q 0) as [p|] eqn:H.
  - econstructor; eauto using check_graph_coverage, source_fields_coverage.
  - constructor; exact H.
Qed.
Theorem bottom_graph_unique q e f : BottomGraph q e -> BottomGraph q f -> e = f.
Proof. intros H K; rewrite (bottom_graph_agreement _ _ H), (bottom_graph_agreement _ _ K); reflexivity. Qed.
Theorem bottom_graph_output q e b :
  BottomGraph q e -> (CC.eval e = b <-> raw_bottom_check q = b).
Proof. intro H; rewrite (bottom_graph_agreement _ _ H), CC.eval_raw_bottom_expression; reflexivity. Qed.

(** The previous resource-only counterexample cannot carry this additional
    local source-provenance graph.  The obstruction is not built into its
    definition: it follows from derived agreement and actual Boolean outputs. *)
Theorem rejected_source_self_comparison_excluded q :
  raw_check q = false -> ~ RawGraph q (CC.Compare q q).
Proof.
  intros Reject H; pose proof (raw_graph_output q (CC.Compare q q) true H) as E.
  assert (T : CC.eval (CC.Compare q q) = true).
  { apply CC.code_eqb_reflexive. }
  apply E in T; rewrite Reject in T; discriminate.
Qed.
Example scoped_counterexample_excluded :
  let q := encode_input NC.EmptyContext CC.bad_application in
  ~ RawGraph q (CC.Compare q q).
Proof. cbn zeta; apply rejected_source_self_comparison_excluded; reflexivity. Qed.

End CheckerSourceGraph.
