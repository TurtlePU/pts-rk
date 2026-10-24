From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat Lia.
From Stdlib Require Vectors.Vector.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From PTSrk.Combinatory Require Import GuardedFiniteCarriers
  MM0FiniteSignature MM0FiniteAxioms MM0SyntaxSoundness
  MM0GuardedQuantification FiniteModelRealization FiniteModelSoundness.
Import ListNotations.

(** Fixed finite interpretations of the LITERAL MM0 constructor signature.
    Admission is closed first-order sorting and numeric syntax size/depth,
    never PTS typing, derivability or consistency. All nine operations are
    total, including on overflow and ill-sorted tuples. The relation-model
    existence problem is deliberately separate from this constructor model. *)
Module MM0GuardedSyntaxAlgebra.
Import MM0FiniteSignature MM0FiniteAxioms MM0SyntaxSoundness
  MM0GuardedQuantification.
Module C := GuardedFiniteCarriers.
Module G := MM0GuardedQuantification.
Module R := FiniteModelRealization.
Module FMS := FiniteModelSoundness.

Definition expr_eq_dec (x y : Expr) : {x = y} + {x <> y}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Definition pairs (f : Expr -> Expr -> Expr) (xs ys : list Expr) :=
  flat_map (fun x => map (f x) ys) xs.
Definition triples (f : Expr -> Expr -> Expr -> Expr) (xs ys zs : list Expr) :=
  flat_map (fun x => flat_map (fun y => map (f x y) zs) ys) xs.

Lemma pairs_exact f xs ys e :
  In e (pairs f xs ys) <-> exists x y, In x xs /\ In y ys /\ e = f x y.
Proof.
  unfold pairs; rewrite in_flat_map; split.
  - intros [x [HX HE]]; apply in_map_iff in HE as [y [<- HY]]; eauto.
  - intros [x [y [HX [HY ->]]]]; exists x; split; [exact HX | now apply in_map].
Qed.
Lemma triples_exact f xs ys zs e :
  In e (triples f xs ys zs) <->
  exists x y z, In x xs /\ In y ys /\ In z zs /\ e = f x y z.
Proof.
  unfold triples; rewrite in_flat_map; split.
  - intros [x [HX HE]]; apply in_flat_map in HE as [y [HY HE]].
    apply in_map_iff in HE as [z [<- HZ]]; eauto 8.
  - intros [x [y [z [HX [HY [HZ ->]]]]]]; exists x; split; [exact HX |].
    apply in_flat_map; exists y; split; [exact HY | now apply in_map].
Qed.

Fixpoint trees (d : nat) (s : Sort) : list Expr :=
  match d with
  | 0 => []
  | S k =>
    match s with
    | NAT => EZ :: map ES (trees k NAT)
    | TM => map EU (trees k NAT) ++ map EV (trees k NAT) ++
        pairs EApp (trees k TM) (trees k TM) ++
        pairs EPi (trees k TM) (trees k TM) ++
        pairs ELam (trees k TM) (trees k TM)
    | TEL => ENil :: triples ECons (trees k TM) (trees k NAT) (trees k TEL)
    end
  end.

Theorem trees_sound d s e : In e (trees d s) ->
  SortedExpr [] e s /\ expr_depth e <= d.
Proof.
  revert s e; induction d as [|d IH]; intros s e H; [contradiction |].
  destruct s; cbn [trees] in H.
  - destruct H as [<- | H]; [split; [constructor | cbn; lia] |].
    apply in_map_iff in H as [x [<- HX]]; apply IH in HX as [HS HD].
    split; [now constructor | cbn; lia].
  - repeat rewrite in_app_iff in H.
    destruct H as [H | [H | [H | [H | H]]]].
    all: try (apply in_map_iff in H as [x [<- HX]];
      apply IH in HX as [HS HD]; split; [now constructor | cbn; lia]).
    all: apply pairs_exact in H as [x [y [HX [HY ->]]]];
      apply IH in HX as [HS HD]; apply IH in HY as [HT HE];
      split; [now constructor | cbn; lia].
  - destruct H as [<- | H]; [split; [constructor | cbn; lia] |].
    apply triples_exact in H as [x [y [z [HX [HY [HZ ->]]]]]].
    apply IH in HX as [HS HD]; apply IH in HY as [HT HE];
      apply IH in HZ as [HU HF]; split; [now constructor | cbn; lia].
Qed.

Theorem trees_complete s e : SortedExpr [] e s ->
  forall d, expr_depth e <= d -> In e (trees d s).
Proof.
  intro H; remember (@nil Sort) as vars eqn:HV.
  induction H; subst vars; intros [|d] HD; cbn [expr_depth] in HD; try lia.
  - destruct i; discriminate.
  - cbn; auto.
  - cbn [trees]; right; apply in_map, IHSortedExpr; auto; lia.
  - cbn [trees]; apply in_app_iff; left; apply in_map, IHSortedExpr; auto; lia.
  - cbn [trees]; apply in_app_iff; right; apply in_app_iff; left.
    apply in_map, IHSortedExpr; auto; lia.
  - cbn [trees]; apply in_app_iff; right; apply in_app_iff; right.
    apply in_app_iff; left; apply pairs_exact; exists x,y; repeat split;
      [apply IHSortedExpr1 | apply IHSortedExpr2]; auto; lia.
  - cbn [trees]; apply in_app_iff; right; apply in_app_iff; right.
    apply in_app_iff; right; apply in_app_iff; left.
    apply pairs_exact; exists x,y; repeat split;
      [apply IHSortedExpr1 | apply IHSortedExpr2]; auto; lia.
  - cbn [trees]; apply in_app_iff; right; apply in_app_iff; right.
    apply in_app_iff; right; apply in_app_iff; right.
    apply pairs_exact; exists x,y; repeat split;
      [apply IHSortedExpr1 | apply IHSortedExpr2]; auto; lia.
  - cbn; auto.
  - cbn [trees]; right; apply triples_exact; exists x,a,l; repeat split;
      [apply IHSortedExpr1 | apply IHSortedExpr2 | apply IHSortedExpr3]; auto; lia.
Qed.

Definition syntax_list N d :=
  filter (fun e => expr_size e <=? N) (trees d NAT ++ trees d TM ++ trees d TEL).
Definition FitsSyntax N d e :=
  (exists s, SortedExpr [] e s) /\ expr_size e <= N /\ expr_depth e <= d.

Theorem syntax_list_exact N d e : In e (syntax_list N d) <-> FitsSyntax N d e.
Proof.
  unfold syntax_list, FitsSyntax; rewrite filter_In, Nat.leb_le.
  repeat rewrite in_app_iff; split.
  - intros [[H | [H | H]] HN]; apply trees_sound in H as [HS HD]; eauto.
  - intros [[s HS] [HN HD]]; split; [destruct s; auto using trees_complete | exact HN].
Qed.

Definition Domain N d := C.Carrier (syntax_list N d).
Definition values N d := C.elements (syntax_list N d).
Definition value_eq_dec N d := C.carrier_eq_dec Expr (syntax_list N d).
Definition decode N d := C.decode (syntax_list N d).
Definition quote N d := C.encode expr_eq_dec (syntax_list N d).
Definition raw N d (a : Domain N d) := match decode N d a with Some e => e | None => EZ end.
Definition active N d (a : Domain N d) := match a with Some _ => true | None => false end.

Theorem values_complete N d x : In x (values N d).
Proof. apply C.elements_complete. Qed.
Theorem values_length N d : length (values N d) = S (length (syntax_list N d)).
Proof. apply C.elements_length. Qed.
Theorem quote_decode_exact N d e : decode N d (quote N d e) = Some e <-> FitsSyntax N d e.
Proof. unfold decode, quote; rewrite C.decode_encode_exact; apply syntax_list_exact. Qed.
Theorem decode_admitted N d a e : decode N d a = Some e -> FitsSyntax N d e.
Proof. intro H; apply syntax_list_exact; eapply C.decode_member; exact H. Qed.
Theorem active_decode N d a : active N d a = true <-> decode N d a = Some (raw N d a).
Proof. destruct a; unfold active, raw, decode, C.decode; cbn; split; congruence. Qed.
Theorem quote_injective N d e f : FitsSyntax N d e -> FitsSyntax N d f ->
  quote N d e = quote N d f -> e = f.
Proof. intros HE HF; apply C.encode_injective; now apply syntax_list_exact. Qed.

Definition unary N d (f : Expr -> Expr) :=
  C.lift1 expr_eq_dec (syntax_list N d) (syntax_list N d) f.
Definition binary N d (f : Expr -> Expr -> Expr) :=
  C.lift2 expr_eq_dec (syntax_list N d) (syntax_list N d) (syntax_list N d) f.
Definition ternary N d (f : Expr -> Expr -> Expr -> Expr) :=
  C.lift3 expr_eq_dec (syntax_list N d) (syntax_list N d)
    (syntax_list N d) (syntax_list N d) f.

Definition algebra N d : Algebra (Domain N d) :=
  fun o => match o as op return Vector.t (Domain N d) (arity op) -> Domain N d with
  | OZ => fun _ => quote N d EZ
  | OS => fun xs => unary N d ES (Vector.hd xs)
  | OU => fun xs => unary N d EU (Vector.hd xs)
  | OV => fun xs => unary N d EV (Vector.hd xs)
  | OApp => fun xs => binary N d EApp (Vector.hd xs) (Vector.hd (Vector.tl xs))
  | OPi => fun xs => binary N d EPi (Vector.hd xs) (Vector.hd (Vector.tl xs))
  | OLam => fun xs => binary N d ELam (Vector.hd xs) (Vector.hd (Vector.tl xs))
  | ONil => fun _ => quote N d ENil
  | OCons => fun xs => ternary N d ECons (Vector.hd xs)
      (Vector.hd (Vector.tl xs)) (Vector.hd (Vector.tl (Vector.tl xs)))
  end.

Lemma unary_decodes N d f a x :
  decode N d a = Some x -> FitsSyntax N d (f x) ->
  decode N d (unary N d f a) = Some (f x).
Proof.
  intros HA HF; apply C.lift1_exact; exists x; repeat split; auto.
  now apply syntax_list_exact.
Qed.
Lemma binary_decodes N d f a b x y :
  decode N d a = Some x -> decode N d b = Some y -> FitsSyntax N d (f x y) ->
  decode N d (binary N d f a b) = Some (f x y).
Proof.
  intros HA HB HF; apply C.lift2_exact; exists x,y; repeat split; auto.
  now apply syntax_list_exact.
Qed.
Lemma ternary_decodes N d f a b c x y z :
  decode N d a = Some x -> decode N d b = Some y -> decode N d c = Some z ->
  FitsSyntax N d (f x y z) -> decode N d (ternary N d f a b c) = Some (f x y z).
Proof.
  intros HA HB HC HF; apply C.lift3_exact; exists x,y,z; repeat split; auto.
  now apply syntax_list_exact.
Qed.

(** The valuation is arbitrary. Exactness uses only successful variable
    decoding, source sorting and bounds on the substituted OUTPUT. *)
Theorem evaluate_decodes N d vars e s (HS : SortedExpr vars e s) :
  forall env sigma,
  (forall i, i < length vars -> decode N d (nth i env None) = Some (sigma i)) ->
  ClosedSubstitution vars sigma ->
  expr_size (substitute sigma e) <= N -> expr_depth (substitute sigma e) <= d ->
  decode N d (evaluate None (algebra N d) env e) = Some (substitute sigma e).
Proof.
  induction HS; intros env sigma HV HC HN HD;
    cbn [evaluate algebra Vector.hd Vector.tl substitute] in *.
  - apply HV; apply nth_error_Some; rewrite H; discriminate.
  - apply quote_decode_exact; split; [exists NAT; constructor | cbn; auto].
  - apply unary_decodes.
    + apply IHHS; auto; cbn [expr_size expr_depth] in *; lia.
    + split; [exists NAT; constructor; eapply substitution_preserves_sort; eassumption | auto].
  - apply unary_decodes.
    + apply IHHS; auto; cbn [expr_size expr_depth] in *; lia.
    + split; [exists TM; constructor; eapply substitution_preserves_sort; eassumption | auto].
  - apply unary_decodes.
    + apply IHHS; auto; cbn [expr_size expr_depth] in *; lia.
    + split; [exists TM; constructor; eapply substitution_preserves_sort; eassumption | auto].
  - apply binary_decodes.
    + apply IHHS1; auto; cbn [expr_size expr_depth] in *; lia.
    + apply IHHS2; auto; cbn [expr_size expr_depth] in *; lia.
    + split; [exists TM; constructor; eapply substitution_preserves_sort; eassumption | auto].
  - apply binary_decodes.
    + apply IHHS1; auto; cbn [expr_size expr_depth] in *; lia.
    + apply IHHS2; auto; cbn [expr_size expr_depth] in *; lia.
    + split; [exists TM; constructor; eapply substitution_preserves_sort; eassumption | auto].
  - apply binary_decodes.
    + apply IHHS1; auto; cbn [expr_size expr_depth] in *; lia.
    + apply IHHS2; auto; cbn [expr_size expr_depth] in *; lia.
    + split; [exists TM; constructor; eapply substitution_preserves_sort; eassumption | auto].
  - apply quote_decode_exact; split; [exists TEL; constructor | cbn; auto].
  - apply ternary_decodes.
    + apply IHHS1; auto; cbn [expr_size expr_depth] in *; lia.
    + apply IHHS2; auto; cbn [expr_size expr_depth] in *; lia.
    + apply IHHS3; auto; cbn [expr_size expr_depth] in *; lia.
    + split; [exists TEL; constructor; eapply substitution_preserves_sort; eassumption | auto].
Qed.

Lemma closed_substitute e : Scoped 0 e -> substitute (fun _ => EZ) e = e.
Proof.
  induction e; cbn [Scoped substitute]; intros H; try reflexivity; try (now rewrite IHe).
  - lia.
  - destruct H; now rewrite IHe1, IHe2.
  - destruct H; now rewrite IHe1, IHe2.
  - destruct H; now rewrite IHe1, IHe2.
  - destruct H as [H1 [H2 H3]]; now rewrite IHe1, IHe2, IHe3.
Qed.

Theorem closed_evaluate_decodes N d e : FitsSyntax N d e ->
  decode N d (evaluate None (algebra N d) [] e) = Some e.
Proof.
  intros [[s HS] [HN HD]].
  pose proof (closed_substitute e (sorted_scoped [] e s HS)) as HE.
  replace (Some e) with (Some (substitute (fun _ => EZ) e)) by now rewrite HE.
  apply (evaluate_decodes N d [] e s HS [] (fun _ => EZ));
    [intros; cbn in *; lia | intros [|i] t H; discriminate | now rewrite HE | now rewrite HE].
Qed.

Definition decoded_substitution N d (env : list (Domain N d)) i :=
  nth i (map (raw N d) env) EZ.
Definition guard N d r (env : Vector.t (Domain N d) (length (variables r))) :=
  structural_guard (raw N d) (active N d) N d r env &&
  arguments_sorted [] (map (raw N d) (Vector.to_list env)) (variables r).

Theorem guard_exact N d r env : guard N d r env = true <->
  Forall (fun x => active N d x = true) (Vector.to_list env) /\
  Bounds N d (instance_expressions r (decoded_substitution N d (Vector.to_list env))) /\
  Forall2 (SortedExpr []) (map (raw N d) (Vector.to_list env)) (variables r).
Proof.
  unfold guard, decoded_substitution; rewrite andb_true_iff,
    structural_guard_exact, arguments_sorted_exact; tauto.
Qed.

Lemma sorted_nth vals vars : Forall2 (SortedExpr []) vals vars ->
  forall i s, nth_error vars i = Some s -> SortedExpr [] (nth i vals EZ) s.
Proof.
  intro H; induction H; intros [|i] s HE; cbn in HE |- *; try discriminate.
  - injection HE as <-; assumption.
  - now apply IHForall2.
Qed.

Lemma sorted_from_nth vals vars : length vals = length vars ->
  (forall i s, nth_error vars i = Some s -> SortedExpr [] (nth i vals EZ) s) ->
  Forall2 (SortedExpr []) vals vars.
Proof.
  revert vars; induction vals as [|x xs IH]; intros [|s ss] HL HA; cbn in HL;
    try discriminate; [constructor |].
  constructor.
  - exact (HA 0 s eq_refl).
  - apply IH; [lia | intros i t HE; exact (HA (S i) t HE)].
Qed.

Lemma instance_variable_bound N d r sigma i :
  Bounds N d (instance_expressions r sigma) -> i < length (variables r) ->
  expr_size (sigma i) <= N /\ expr_depth (sigma i) <= d.
Proof.
  intros HB Hi; unfold Bounds in HB; rewrite Forall_forall in HB; apply HB.
  unfold instance_expressions; apply in_or_app; left.
  apply in_map; apply in_seq; lia.
Qed.

Lemma instance_argument_bound N d r sigma a e :
  Bounds N d (instance_expressions r sigma) ->
  In a (conclusion r :: premises r) -> In e (snd a) ->
  expr_size (substitute sigma e) <= N /\ expr_depth (substitute sigma e) <= d.
Proof.
  intros HB HA HE; unfold Bounds in HB; rewrite Forall_forall in HB; apply HB.
  unfold instance_expressions; apply in_or_app; right.
  apply in_flat_map; exists (substitute_atom sigma a); split.
  - now apply in_map.
  - unfold substitute_atom; cbn; now apply in_map.
Qed.

Theorem guard_valuation_decodes N d r env : guard N d r env = true ->
  forall i, i < length (variables r) ->
  decode N d (nth i (Vector.to_list env) None) =
    Some (decoded_substitution N d (Vector.to_list env) i).
Proof.
  intros HG i Hi; apply guard_exact in HG as [HA _].
  unfold decoded_substitution.
  change EZ with (raw N d None); rewrite map_nth.
  apply active_decode; rewrite Forall_forall in HA; apply HA.
  apply nth_In; now rewrite Vector.length_to_list.
Qed.

Theorem guard_closed_substitution N d r env : guard N d r env = true ->
  ClosedSubstitution (variables r) (decoded_substitution N d (Vector.to_list env)).
Proof.
  intros HG i s HI; apply guard_exact in HG as [_ [_ HS]].
  now apply (sorted_nth _ _ HS i s).
Qed.

(** Every argument of every active literal rule instance decodes to its
    exact first-order substitution, for EVERY semantic valuation, not only
    valuations selected by source proofs. *)
Theorem guarded_arguments_decode N d name env a e :
  guard N d (axiom_rule name) env = true ->
  In a (conclusion (axiom_rule name) :: premises (axiom_rule name)) ->
  In e (snd a) ->
  decode N d (evaluate None (algebra N d) (Vector.to_list env) e) =
    Some (substitute (decoded_substitution N d (Vector.to_list env)) e).
Proof.
  intros HG HA HE.
  assert (HS : atom_sorted (variables (axiom_rule name)) a = true).
  { destruct HA as [<- | HA]; [apply rule_conclusion_sorted | now apply rule_premise_sorted]. }
  apply atom_sorted_exact in HS.
  assert (HX : exists s, SortedExpr (variables (axiom_rule name)) e s).
  { clear HG; induction HS; cbn in HE; [contradiction |].
    destruct HE as [<- | HE]; [eauto | now apply IHHS]. }
  destruct HX as [s HX].
  apply (evaluate_decodes N d _ e s HX).
  - now apply guard_valuation_decodes.
  - now apply guard_closed_substitution.
  - apply guard_exact in HG as [_ [HB _]].
    exact (proj1 (instance_argument_bound N d _ _ a e HB HA HE)).
  - apply guard_exact in HG as [_ [HB _]].
    exact (proj2 (instance_argument_bound N d _ _ a e HB HA HE)).
Qed.

Theorem guarded_atom_decode N d name env a :
  guard N d (axiom_rule name) env = true ->
  In a (conclusion (axiom_rule name) :: premises (axiom_rule name)) ->
  map (decode N d) (snd (evaluate_atom None (algebra N d) (Vector.to_list env) a)) =
  map Some (snd (substitute_atom (decoded_substitution N d (Vector.to_list env)) a)).
Proof.
  intros HG HA; unfold evaluate_atom, substitute_atom; cbn; rewrite !map_map.
  apply map_ext_in; intros e HE; now apply guarded_arguments_decode with (a := a).
Qed.

Lemma source_values_exact N d name sigma :
  ClosedSubstitution (variables (axiom_rule name)) sigma ->
  Bounds N d (instance_expressions (axiom_rule name) sigma) ->
  forall i, i < length (variables (axiom_rule name)) ->
  active N d (evaluate None (algebra N d) [] (sigma i)) = true /\
  raw N d (evaluate None (algebra N d) [] (sigma i)) = sigma i.
Proof.
  intros HS HB i Hi.
  assert (HE : decode N d (evaluate None (algebra N d) [] (sigma i)) = Some (sigma i)).
  { apply closed_evaluate_decodes; split.
    - destruct (nth_error (variables (axiom_rule name)) i) as [s|] eqn:HV.
      + exists s; now apply (HS i).
      + apply nth_error_None in HV; lia.
    - now apply instance_variable_bound with (r := axiom_rule name). }
  assert (HR : raw N d (evaluate None (algebra N d) [] (sigma i)) = sigma i).
  { unfold raw; now rewrite HE. }
  split; [apply active_decode; now rewrite HR | exact HR].
Qed.

Theorem guard_representation N d name sigma :
  ClosedSubstitution (variables (axiom_rule name)) sigma ->
  Bounds N d (instance_expressions (axiom_rule name) sigma) ->
  guard N d (axiom_rule name)
    (substitution_valuation None (algebra N d) (length (variables (axiom_rule name))) sigma) = true.
Proof.
  intros HS HB; unfold guard; apply andb_true_iff; split.
  - apply structural_guard_representation; [exact HB | now apply source_values_exact].
  - apply arguments_sorted_exact, sorted_from_nth.
    + rewrite length_map, Vector.length_to_list; reflexivity.
    + intros i s HI.
      assert (HN : i < length (variables (axiom_rule name))).
      { apply nth_error_Some; rewrite HI; discriminate. }
      change EZ with (raw N d None); rewrite map_nth, substitution_valuation_lookup by exact HN.
      exact (eq_ind_r (fun e => SortedExpr [] e s) (HS i s HI)
        (proj2 (source_values_exact N d name sigma HS HB i HN))).
Qed.

(** No representation hypothesis remains in these source translations.
    Relational satisfaction/acceptance remains an independent obligation;
    these declarations do NOT assert a full55 guarded model. *)
Definition clauses N d names := G.guarded_clauses None (algebra N d)
  (guard N d) (values N d) (selected_rules names).

Definition source_proof N d names a h (p : GuardedDerivation names N d h a) :
  FMS.Proof (clauses N d names) (evaluate_atom None (algebra N d) [] a) :=
  G.ground_guarded_proof None (algebra N d) (guard N d) (values N d)
    (values_complete N d) names N d
    (fun name sigma _ HS HB => guard_representation N d name sigma HS HB)
    a (proj1_sig p) (proj1 (proj2_sig p)).

Definition source_term N d names a h (p : GuardedDerivation names N d h a) :=
  G.compile_guarded_source None (algebra N d) (guard N d) (values N d)
    (values_complete N d) (value_eq_dec N d) names N d
    (fun name sigma _ HS HB => guard_representation N d name sigma HS HB) a h p.

Theorem source_term_typed N d names a h (p : GuardedDerivation names N d h a) :
  @typ nat RankSorts 0 ε (source_term N d names a h p)
    (R.truth_type (FMS.finite_truth (ground_atom_eq_dec (value_eq_dec N d))
      (clauses N d names) (evaluate_atom None (algebra N d) [] a))).
Proof. apply G.compile_guarded_source_typed. Qed.

Theorem source_sound N d names a h (p : GuardedDerivation names N d h a) truth :
  G.GuardedPositiveSatisfaction None (algebra N d) (guard N d) (selected_rules names) truth ->
  truth (evaluate_atom None (algebra N d) [] a).
Proof.
  exact (G.guarded_source_sound None (algebra N d) (guard N d) (values N d)
    (values_complete N d) names N d
    (fun name sigma _ HS HB => guard_representation N d name sigma HS HB) a h p truth).
Qed.

Definition checker N d names := G.guarded_checker None (algebra N d)
  (guard N d) (values N d) (value_eq_dec N d) (selected_rules names) [void_denial].
Definition certificate N d names := G.guarded_certificate None (algebra N d)
  (guard N d) (values N d) (value_eq_dec N d) (selected_rules names) [void_denial].
Definition certificate_type N d names := G.guarded_certificate_type None (algebra N d)
  (guard N d) (values N d) (value_eq_dec N d) (selected_rules names) [void_denial].
Definition certificate_rank N d names := G.guarded_certificate_rank None (algebra N d)
  (guard N d) (values N d) (value_eq_dec N d) (selected_rules names) [void_denial].

Theorem checker_exact N d names : checker N d names = true <-> exists truth,
  G.GuardedModel None (algebra N d) (guard N d) (selected_rules names) [void_denial] truth.
Proof. apply G.guarded_checker_exact, values_complete. Qed.
Theorem certificate_type_sorted N d names :
  @typ nat RankSorts 0 ε (certificate_type N d names) (𝓤 (certificate_rank N d names)).
Proof. apply G.guarded_certificate_type_sorted. Qed.
Theorem certificate_rank_bound N d names : certificate_rank N d names <= 4.
Proof. apply G.guarded_certificate_rank_bound. Qed.
Theorem checked_certificate N d names : checker N d names = true ->
  @typ nat RankSorts 0 ε (certificate N d names) (certificate_type N d names).
Proof. apply G.checked_guarded_certificate. Qed.
Theorem certificate_exact N d names :
  (exists t, @typ nat RankSorts 0 ε t (certificate_type N d names)) <-> exists truth,
  G.GuardedModel None (algebra N d) (guard N d) (selected_rules names) [void_denial] truth.
Proof. apply G.guarded_certificate_exact, values_complete. Qed.
Theorem universal_void_empty N d names truth :
  G.GuardedModel None (algebra N d) (guard N d) (selected_rules names) [void_denial] truth ->
  forall subject, ~ truth (PH, [subject; void_value None (algebra N d)]).
Proof. apply G.guarded_void_empty. Qed.

Theorem void_is_represented N d : 5 <= N -> 3 <= d ->
  decode N d (void_value None (algebra N d)) = Some (EPi (EU EZ) (EV EZ)).
Proof.
  intros HN HD; apply closed_evaluate_decodes; split.
  - exists TM; repeat constructor.
  - cbn; auto.
Qed.

Theorem source_arguments_represented N d names a h
  (p : GuardedDerivation names N d h a) e : In e (snd a) ->
  decode N d (evaluate None (algebra N d) [] e) = Some e.
Proof.
  intros HE; destruct p as [p [HB HH]].
  destruct p as [name sigma Hname HS ps]; cbn in HB; apply Forall_app in HB as [HB HP].
  unfold substitute_atom in HE; cbn in HE; apply in_map_iff in HE as [x [<- HX]].
  apply closed_evaluate_decodes; split.
  - pose proof (rule_conclusion_sorted name) as HA; apply atom_sorted_exact in HA.
    assert (HXS : exists s, SortedExpr (variables (axiom_rule name)) x s).
    { clear HB HP; induction HA; cbn in HX; [contradiction |].
      destruct HX as [<- | HX]; [eauto | now apply IHHA]. }
    destruct HXS as [s HXS]; exists s; now apply substitution_preserves_sort with (vars := variables (axiom_rule name)).
  - exact (instance_argument_bound N d _ _ _ x HB (or_introl eq_refl) HX).
Qed.

Definition every_source_has_fragment names a (p : Derivation names a) :
  FMS.Proof (clauses (source_size_budget names a p) (source_depth_budget names a p) names)
    (evaluate_atom None (algebra (source_size_budget names a p) (source_depth_budget names a p)) [] a) :=
  source_proof _ _ _ _ _ (every_source_derivation_covered names a p).

(** Regression tests distinguish sorting, overflow and bounded outputs.
    These tests concern the algebra/guard; they are not model-existence tests. *)
Example zero_roundtrip : decode 2 2 (quote 2 2 EZ) = Some EZ.
Proof. reflexivity. Qed.
Example wrong_sort_rejected :
  guard 2 2 (axiom_rule A_h_universe)
    (Vector.cons _ (quote 2 2 ENil) 0 (Vector.nil _)) = false.
Proof. reflexivity. Qed.
Example overflow_valuation_rejected :
  guard 2 2 (axiom_rule A_h_universe)
    (Vector.cons _ None 0 (Vector.nil _)) = false.
Proof. reflexivity. Qed.
Example universe_instance_active :
  guard 2 2 (axiom_rule A_h_universe)
    (Vector.cons _ (quote 2 2 EZ) 0 (Vector.nil _)) = true.
Proof. reflexivity. Qed.
Example output_bound_checked :
  guard 1 2 (axiom_rule A_h_universe)
    (Vector.cons _ (quote 1 2 EZ) 0 (Vector.nil _)) = false.
Proof. reflexivity. Qed.
Example ill_sorted_operation_overflows :
  algebra 2 2 OU (Vector.cons _ (quote 2 2 ENil) 0 (Vector.nil _)) = None.
Proof. reflexivity. Qed.

Print Assumptions trees_sound.
Print Assumptions trees_complete.
Print Assumptions syntax_list_exact.
Print Assumptions values_complete.
Print Assumptions values_length.
Print Assumptions quote_decode_exact.
Print Assumptions decode_admitted.
Print Assumptions active_decode.
Print Assumptions quote_injective.
Print Assumptions unary_decodes.
Print Assumptions binary_decodes.
Print Assumptions ternary_decodes.
Print Assumptions evaluate_decodes.
Print Assumptions closed_evaluate_decodes.
Print Assumptions guard_exact.
Print Assumptions guard_valuation_decodes.
Print Assumptions guard_closed_substitution.
Print Assumptions guarded_arguments_decode.
Print Assumptions guarded_atom_decode.
Print Assumptions source_values_exact.
Print Assumptions guard_representation.
Print Assumptions source_proof.
Print Assumptions source_term_typed.
Print Assumptions source_sound.
Print Assumptions checker_exact.
Print Assumptions certificate_type_sorted.
Print Assumptions certificate_rank_bound.
Print Assumptions checked_certificate.
Print Assumptions certificate_exact.
Print Assumptions universal_void_empty.
Print Assumptions void_is_represented.
Print Assumptions source_arguments_represented.
Print Assumptions every_source_has_fragment.
Print Assumptions zero_roundtrip.
Print Assumptions wrong_sort_rejected.
Print Assumptions overflow_valuation_rejected.
Print Assumptions universe_instance_active.
Print Assumptions output_bound_checked.
Print Assumptions ill_sorted_operation_overflows.
End MM0GuardedSyntaxAlgebra.
