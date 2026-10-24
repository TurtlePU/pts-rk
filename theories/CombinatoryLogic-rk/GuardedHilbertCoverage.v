From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Ranks Reduction DefEq.
From PTSrk.Combinatory Require Import GroundHorn GroundHornConsistency
  FiniteHorn HilbertGrounding CatalogueEconomy GuardedFiniteCarriers
  GuardedBetaGraphs GuardedHilbertTables.
Import ListNotations.

(** Every independent Hilbert proof has an executable guarded model. Bounds
    cover displayed syntax, every beta witness state and the finite set of
    concrete catalogue labels. This does not assert original-PTS completeness. *)
Module GuardedHilbertCoverage.
Module T := GuardedHilbertTables.
Module B := GuardedBetaGraphs.
Module C := GuardedFiniteCarriers.
Module H := HilbertGrounding.
Module HC := GroundHornConsistency.
Module F := FiniteHorn.

Record Budget := budget { size : nat; depth : nat; steps : nat;
  labels : list CatalogueEconomy.Label }.
Definition Below b c := size b <= size c /\ depth b <= depth c /\
  steps b <= steps c /\ incl (labels b) (labels c).
Definition join b c := budget (Nat.max (size b) (size c))
  (Nat.max (depth b) (depth c)) (Nat.max (steps b) (steps c)) (labels b ++ labels c).
Definition clauses b := T.clauses (size b) (depth b) (steps b) (labels b).
Definition truth b := T.truth (size b) (depth b) (steps b) (labels b).

Lemma below_left b c : Below b (join b c).
Proof. unfold Below, join; cbn; repeat split; try lia; intros x HX; apply in_or_app; auto. Qed.
Lemma below_right b c : Below c (join b c).
Proof. unfold Below, join; cbn; repeat split; try lia; intros x HX; apply in_or_app; auto. Qed.

Theorem syntax_monotone n N d N' d' : N <= N' -> d <= d' ->
  incl (C.native_terms N d n (seq 0 (S d))) (C.native_terms N' d' n (seq 0 (S d'))).
Proof.
  intros HN HD t HT; change (In t (B.syntax_states n N d)) in HT.
  change (In t (B.syntax_states n N' d')); apply B.syntax_states_exact in HT.
  apply B.syntax_states_exact; destruct HT as [HS [HD' HL]]; repeat split; try lia.
  intros i HI; specialize (HL i HI); lia.
Qed.

Lemma terms_monotone b c : Below b c -> incl (T.terms (size b) (depth b)) (T.terms (size c) (depth c)).
Proof. intros [HN [HD _]]; apply syntax_monotone; assumption. Qed.
Lemma bodies_monotone b c : Below b c -> incl (T.bodies (size b) (depth b)) (T.bodies (size c) (depth c)).
Proof. intros [HN [HD _]]; apply syntax_monotone; assumption. Qed.
Lemma alphabet_monotone b c : Below b c -> incl (T.alphabet (depth b)) (T.alphabet (depth c)).
Proof. intros [_ [HD _]] i HI; apply in_seq in HI; apply in_seq; lia. Qed.

Theorem parameters_monotone b c i : Below b c ->
  T.parameters (size b) (depth b) (labels b) i -> T.parameters (size c) (depth c) (labels c) i.
Proof.
  intros HB HP; pose proof (terms_monotone b c HB) as HT;
    pose proof (bodies_monotone b c HB) as HH;
    pose proof (alphabet_monotone b c HB) as HA.
  destruct HB as [_ [_ [_ HL]]]; destruct i; cbn [T.parameters] in *; intuition auto.
Qed.

Theorem clause_guard_monotone b c clause : Below b c ->
  T.clause_guard (size b) (depth b) clause = true ->
  T.clause_guard (size c) (depth c) clause = true.
Proof.
  intros HB HG; apply T.clause_guard_exact in HG; apply T.clause_guard_exact.
  eapply Forall_impl; [|exact HG]; intros a [HM HA]; split; eapply terms_monotone; eassumption.
Qed.

Theorem witness_monotone b c i : Below b c ->
  T.witness_guard (size b) (depth b) (steps b) i = true ->
  T.witness_guard (size c) (depth c) (steps c) i = true.
Proof.
  intros HB HW; pose proof (terms_monotone b c HB) as HT.
  destruct HB as [_ [_ [HK _]]]; destruct i; cbn [T.witness_guard] in *; try reflexivity.
  - eapply B.joins_monotone; eassumption.
  - eapply B.reaches_monotone; eassumption.
  - eapply B.reaches_monotone; eassumption.
Qed.

Theorem enabled_monotone b c i : Below b c ->
  T.enabled (size b) (depth b) (steps b) i = true ->
  T.enabled (size c) (depth c) (steps c) i = true.
Proof.
  intros HB; unfold T.enabled; rewrite !andb_true_iff; intros [HC HW]; split.
  - eapply clause_guard_monotone; eassumption.
  - eapply witness_monotone; eassumption.
Qed.

Theorem clauses_monotone b c : Below b c -> incl (clauses b) (clauses c).
Proof.
  intros HB clause HC; apply T.clause_enumeration_exact in HC as [i [HP [HE ->]]].
  apply T.clause_enumeration_exact; exists i; split.
  - eapply parameters_monotone; eassumption.
  - split; [eapply enabled_monotone; eassumption|reflexivity].
Qed.

Theorem query_monotone b c a : Below b c -> truth b a -> truth c a.
Proof.
  intros HB HT; apply T.query_exact in HT; apply T.query_exact.
  eapply HC.derives_mono; [|exact HT].
  intros ps raw HR; apply (clauses_monotone b c HB); exact HR.
Qed.

Definition closed_parameters i : list (Term nat 0) :=
  match i with
  | T.application_instance f x A _ => [f;x;A]
  | T.conversion_instance M A B _ => [M;A;B]
  | T.subject_instance M M' A => [M;M';A]
  | T.type_instance M A A' => [M;A;A']
  | _ => []
  end.
Definition closed_support i :=
  flat_map (fun a => [fst a;snd a]) (snd (T.clause_of i) :: fst (T.clause_of i)) ++ closed_parameters i.
Definition body_support i : list (Term nat 1) :=
  match i with T.application_instance _ _ _ body => [body] | _ => [] end.
Definition index_support i : list nat :=
  match i with T.universe_instance r | T.conversion_instance _ _ _ r => [r] | _ => [] end.
Definition label_support i :=
  match i with T.catalogue_instance l => [l] | _ => [] end.

Definition syntax_budget i := budget
  (Nat.max (B.size_envelope (closed_support i)) (B.size_envelope (body_support i)))
  (Nat.max (B.depth_envelope (closed_support i))
    (Nat.max (B.depth_envelope (body_support i)) (B.maximum (fun n => n) (index_support i))))
  0 (label_support i).

Lemma closed_support_covered i t : In t (closed_support i) ->
  In t (T.terms (size (syntax_budget i)) (depth (syntax_budget i))).
Proof.
  intro HT; pose proof (B.syntax_envelope_covers 0 (closed_support i) t HT) as HC.
  eapply syntax_monotone; [| |exact HC]; unfold syntax_budget; cbn; lia.
Qed.
Lemma body_support_covered i t : In t (body_support i) ->
  In t (T.bodies (size (syntax_budget i)) (depth (syntax_budget i))).
Proof.
  intro HT; pose proof (B.syntax_envelope_covers 1 (body_support i) t HT) as HC.
  eapply syntax_monotone; [| |exact HC]; unfold syntax_budget; cbn; lia.
Qed.
Lemma index_support_covered i r : In r (index_support i) ->
  In r (T.alphabet (depth (syntax_budget i))).
Proof.
  intro HR; pose proof (B.maximum_covers _ (fun n => n) (index_support i) r HR).
  apply in_seq; unfold syntax_budget; cbn; lia.
Qed.

Theorem syntax_parameters_covered i :
  T.parameters (size (syntax_budget i)) (depth (syntax_budget i)) (labels (syntax_budget i)) i.
Proof.
  assert (HC : forall t, In t (closed_parameters i) ->
    In t (T.terms (size (syntax_budget i)) (depth (syntax_budget i)))).
  { intros t HT; apply closed_support_covered; unfold closed_support; apply in_or_app; right; exact HT. }
  pose proof (body_support_covered i) as HB; pose proof (index_support_covered i) as HI.
  destruct i; cbn [T.parameters closed_parameters body_support index_support] in *;
    repeat split; try (apply HC; cbn; auto); try (apply HB; cbn; auto); try (apply HI; cbn; auto).
  unfold syntax_budget; cbn [labels label_support]; left; reflexivity.
Qed.

Theorem syntax_clause_covered i :
  T.clause_guard (size (syntax_budget i)) (depth (syntax_budget i)) (T.clause_of i) = true.
Proof.
  apply T.clause_guard_exact, Forall_forall; intros a HA; split; apply closed_support_covered;
    unfold closed_support; apply in_or_app; left; apply in_flat_map;
    exists a; split; [exact HA|cbn; auto|exact HA|cbn; auto].
Qed.

Definition NativeWitness i :=
  match i with
  | T.conversion_instance _ A B _ => def_equiv nat 0 A B
  | T.subject_instance M M' _ => reduces_to nat 0 M M'
  | T.type_instance _ A A' => reduces_to nat 0 A A'
  | _ => True
  end.

Theorem native_clause_instance ps a : H.Rules ps a ->
  exists i, T.clause_of i = (ps,a) /\ NativeWitness i.
Proof.
  intro HR; destruct HR.
  - exists (T.universe_instance i); split; [reflexivity|exact I].
  - exists (T.catalogue_instance l); split; [reflexivity|exact I].
  - exists (T.application_instance f x A B); split; [reflexivity|exact I].
  - exists (T.conversion_instance M A B r); split; [reflexivity|assumption].
  - exists (T.subject_instance M N A); split; [reflexivity|assumption].
  - exists (T.type_instance M A B); split; [reflexivity|assumption].
Qed.

Theorem native_witness_covered i : NativeWitness i -> exists b,
  T.witness_guard (size b) (depth b) (steps b) i = true.
Proof.
  destruct i; cbn [NativeWitness]; intro HW.
  - exists (budget 0 0 0 []); reflexivity.
  - exists (budget 0 0 0 []); reflexivity.
  - exists (budget 0 0 0 []); reflexivity.
  - apply B.conversion_numeric_coverage in HW as [k [l [N [d HW]]]].
    exists (budget N d (Nat.max k l) []); cbn [size depth steps T.witness_guard].
    eapply B.joins_monotone; [intros t HT; exact HT|apply Nat.le_max_l|apply Nat.le_max_r|exact HW].
  - apply B.reduction_numeric_coverage in HW as [k [N [d HW]]].
    exists (budget N d k []); exact HW.
  - apply B.reduction_numeric_coverage in HW as [k [N [d HW]]].
    exists (budget N d k []); exact HW.
Qed.

Theorem native_clause_covered ps a : H.Rules ps a -> exists b, In (ps,a) (clauses b).
Proof.
  intro HR; apply native_clause_instance in HR as [i [HC HW]].
  apply native_witness_covered in HW as [b HW].
  exists (join (syntax_budget i) b); apply T.clause_enumeration_exact; exists i; split.
  - eapply parameters_monotone; [apply below_left|apply syntax_parameters_covered].
  - split; [|symmetry; exact HC].
    unfold T.enabled; apply andb_true_iff; split.
    + eapply clause_guard_monotone; [apply below_left|apply syntax_clause_covered].
    + eapply witness_monotone; [apply below_right|exact HW].
Qed.

Theorem finite_clauses_covered fragment :
  (forall ps a, In (ps,a) fragment -> H.Rules ps a) -> exists b, incl fragment (clauses b).
Proof.
  induction fragment as [|[ps a] rest IH]; intro HV.
  - exists (budget 0 0 0 []); intros x H; contradiction.
  - destruct (native_clause_covered ps a (HV ps a (or_introl eq_refl))) as [b HB].
    destruct IH as [c HC]; [intros qs q HQ; apply HV; right; exact HQ|].
    exists (join b c); intros x [<-|HX].
    + apply (clauses_monotone b (join b c) (below_left b c)), HB.
    + apply (clauses_monotone c (join b c) (below_right b c)), HC, HX.
Qed.

Theorem query_hilbert_sound b M A : truth b (M,A) -> CatalogueEconomy.Derives M A.
Proof.
  intro HT; apply T.query_exact in HT; apply H.ground_to_hilbert.
  eapply HC.derives_mono; [|exact HT].
  intros ps a HR; apply T.clauses_valid in HR; exact HR.
Qed.

Theorem hilbert_query_coverage M A : CatalogueEconomy.Derives M A -> exists b, truth b (M,A).
Proof.
  intro HH; apply H.every_hilbert_proof_has_finite_support in HH as [fragment [HV HP]].
  destruct (finite_clauses_covered fragment HV) as [b HB]; exists b; apply T.query_exact.
  eapply HC.derives_mono; [|exact HP].
  intros ps a HA; apply HB; exact HA.
Qed.

Theorem executable_union_exact M A :
  CatalogueEconomy.Derives M A <-> exists b, truth b (M,A).
Proof. split; [apply hilbert_query_coverage|intros [b HB]; eapply query_hilbert_sound; exact HB]. Qed.

Theorem finite_family_common_budget atoms :
  Forall (fun a => CatalogueEconomy.Derives (fst a) (snd a)) atoms ->
  exists b, Forall (truth b) atoms.
Proof.
  intro HA; induction HA as [|[M A] rest HH HR IH].
  - exists (budget 0 0 0 []); constructor.
  - apply hilbert_query_coverage in HH as [b HB]; destruct IH as [c HC].
    exists (join b c); constructor.
    + eapply query_monotone; [apply below_left|exact HB].
    + eapply Forall_impl; [|exact HC]; intros a HA; eapply query_monotone; [apply below_right|exact HA].
Qed.

Theorem true_query_represented b M A : truth b (M,A) ->
  In M (T.terms (size b) (depth b)) /\ In A (T.terms (size b) (depth b)).
Proof.
  intro HT; apply T.query_exact in HT.
  refine (GroundHorn.derivation_sound _ _ HT
    (fun a => In (fst a) (T.terms (size b) (depth b)) /\
              In (snd a) (T.terms (size b) (depth b))) _).
  intros ps a HC HP; apply T.clause_enumeration_exact in HC as [i [_ [HG HE]]].
  unfold T.enabled in HG; apply andb_true_iff in HG as [HG _].
  apply T.clause_guard_exact in HG; rewrite <- HE in HG; exact (Forall_inv HG).
Qed.

Definition quoted_truth b M A :=
  T.semantic_truth (size b) (depth b) (steps b) (labels b)
    (T.encode (size b) (depth b) 0 M) (T.encode (size b) (depth b) 0 A) = true.

Theorem quoted_query_exact b M A : quoted_truth b M A <-> truth b (M,A).
Proof.
  split.
  - unfold quoted_truth, T.semantic_truth.
    destruct (T.decode (size b) (depth b) 0 (T.encode (size b) (depth b) 0 M)) as [m|] eqn:HM;
      [|discriminate].
    destruct (T.decode (size b) (depth b) 0 (T.encode (size b) (depth b) 0 A)) as [a|] eqn:HA;
      [|discriminate].
    unfold T.decode, T.encode in HM, HA; apply C.decode_encode_value in HM, HA.
    destruct HM as [_ ->], HA as [_ ->]; intro H; exact H.
  - intro HT; destruct (true_query_represented b M A HT) as [HM HA].
    assert (DM : T.decode (size b) (depth b) 0 (T.encode (size b) (depth b) 0 M) = Some M).
    { apply C.decode_encode; exact HM. }
    assert (DA : T.decode (size b) (depth b) 0 (T.encode (size b) (depth b) 0 A) = Some A).
    { apply C.decode_encode; exact HA. }
    unfold quoted_truth, T.semantic_truth; rewrite DM, DA; exact HT.
Qed.

Theorem executable_semantic_coverage M A :
  CatalogueEconomy.Derives M A <-> exists b, quoted_truth b M A.
Proof.
  rewrite executable_union_exact; split; intros [b HB]; exists b;
    apply quoted_query_exact; exact HB.
Qed.

Print Assumptions syntax_monotone.
Print Assumptions parameters_monotone.
Print Assumptions clause_guard_monotone.
Print Assumptions witness_monotone.
Print Assumptions enabled_monotone.
Print Assumptions clauses_monotone.
Print Assumptions query_monotone.
Print Assumptions syntax_parameters_covered.
Print Assumptions syntax_clause_covered.
Print Assumptions native_clause_instance.
Print Assumptions native_witness_covered.
Print Assumptions native_clause_covered.
Print Assumptions finite_clauses_covered.
Print Assumptions query_hilbert_sound.
Print Assumptions hilbert_query_coverage.
Print Assumptions executable_union_exact.
Print Assumptions finite_family_common_budget.
Print Assumptions true_query_represented.
Print Assumptions quoted_query_exact.
Print Assumptions executable_semantic_coverage.
End GuardedHilbertCoverage.
