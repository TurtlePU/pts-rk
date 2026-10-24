From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk.Combinatory Require Import GroundHorn FiniteHorn FiniteModelSoundness
  GuardedFiniteCarriers MM0FiniteSignature MM0FiniteAxioms
  MM0GuardedQuantification MM0GuardedSyntaxAlgebra FiniteUniversalHorn.
Import ListNotations.

(** Finite indexing of a fixed Horn fragment, including its query and every
    denial.  Admission is list membership only.  No typing or consistency
    predicate is used.  Repeated positions are permitted: encoding is
    injective on supported atoms, but arbitrary indices may be aliases.

    The finite atom alphabet does not bound proof-tree depth.  The executable
    translations below preserve arbitrary finite proof trees. *)
Module GuardedFiniteSupport.
Module C := GuardedFiniteCarriers.
Module F := FiniteModelSoundness.
Module H := FiniteHorn.
Module GH := GroundHorn.

Definition map_clause {A B : Type} (f : A -> B) (c : list A * A) :=
  (map f (fst c), f (snd c)).

Section Translation.
Context {A B : Type}.
Variable f : A -> B.
Variable clauses : list (list A * A).

Fixpoint map_proof a (p : F.Proof clauses a) :
  F.Proof (map (map_clause f) clauses) (f a)
with map_proofs ps (p : F.Proofs clauses ps) :
  F.Proofs (map (map_clause f) clauses) (map f ps).
Proof.
  - destruct p as [ps a HR subs].
    eapply F.use_clause.
    + exact (in_map (map_clause f) clauses (ps, a) HR).
    + exact (map_proofs ps subs).
  - destruct p as [|a ps p subs]; cbn.
    + constructor.
    + constructor; [exact (map_proof a p) | exact (map_proofs ps subs)].
Defined.

Theorem map_derivation a : H.Derives clauses a ->
  H.Derives (map (map_clause f) clauses) (f a).
Proof.
  intro HD; destruct (F.derivation_has_proof clauses a HD) as [p].
  exact (F.proof_derivable _ _ (map_proof a p)).
Qed.

Theorem mapped_model_exact truth :
  H.Model (map (map_clause f) clauses) truth <->
  H.Model clauses (fun a => truth (f a)).
Proof.
  split.
  - intros HM ps a HC HP; apply (HM (map f ps) (f a)).
    + exact (in_map (map_clause f) clauses (ps, a) HC).
    + now rewrite Forall_map.
  - intros HM ps a HC HP.
    apply in_map_iff in HC as [[qs b] [E HC]].
    unfold map_clause in E; cbn in E; inversion E; subst ps a.
    apply (HM qs b HC); now rewrite <- Forall_map.
Qed.
End Translation.

Theorem mapped_denials_exact {A B} (f : A -> B) denials (truth : B -> Prop) :
  H.Denials (map (map f) denials) truth <->
  H.Denials denials (fun a => truth (f a)).
Proof.
  split.
  - intros HD ps HP HT; apply (HD (map f ps)); [now apply in_map | now rewrite Forall_map].
  - intros HD ps HP HT; apply in_map_iff in HP as [qs [<- HQ]].
    apply (HD qs HQ); now rewrite <- Forall_map.
Qed.

Section Support.
Context {Atom : Type}.
Variable atom_eq_dec : forall a b : Atom, {a = b} + {a <> b}.
Variable clauses : list (list Atom * Atom).
Variable denials : list (list Atom).
Variable query : Atom.

Definition support_tail :=
  flat_map (fun c => snd c :: fst c) clauses ++ concat denials.
Definition support := query :: support_tail.
Definition cardinality := length support.
Definition Index := Fin cardinality.
Definition reify : Index -> Atom := C.lookup support.
Definition index (a : Atom) : Index :=
  match C.encode atom_eq_dec support a with Some i => i | None => fzero end.
Definition indices := FiniteNormalForms.FiniteNormalForms.variables cardinality.
Definition indexed_clauses := map (map_clause index) clauses.
Definition indexed_denials := map (map index) denials.

Theorem cardinality_positive : 0 < cardinality.
Proof. unfold cardinality, support; cbn; lia. Qed.

Theorem cardinality_exact : cardinality =
  S (list_sum (map (fun c => S (length (fst c))) clauses) +
     list_sum (map (@length Atom) denials)).
Proof.
  unfold cardinality, support, support_tail; cbn [length]; rewrite length_app.
  rewrite length_flat_map, length_concat; f_equal; f_equal; apply map_ext; intros [ps a]; reflexivity.
Qed.

Theorem indices_complete i : In i indices.
Proof. apply FiniteNormalForms.FiniteNormalForms.variables_complete. Qed.

Theorem indices_length : length indices = cardinality.
Proof. apply FiniteNormalForms.FiniteNormalForms.variables_length. Qed.

Theorem query_supported : In query support.
Proof. left; reflexivity. Qed.

Theorem clause_support ps a : In (ps, a) clauses ->
  In a support /\ Forall (fun b => In b support) ps.
Proof.
  intro HC; assert (HS : forall b, In b (a :: ps) -> In b support).
  { intros b HB; right; apply in_app_iff; left; apply in_flat_map.
    exists (ps, a); auto. }
  split; [apply HS; left; reflexivity | apply Forall_forall; intros b HB; apply HS; now right].
Qed.

Theorem denial_support ps : In ps denials -> Forall (fun a => In a support) ps.
Proof.
  intros HD; apply Forall_forall; intros a HA; right; apply in_app_iff; right.
  apply in_concat; now exists ps.
Qed.

Theorem reify_supported i : In (reify i) support.
Proof. apply C.lookup_member. Qed.

Theorem reify_index a : In a support -> reify (index a) = a.
Proof.
  intro HA; pose proof (C.decode_encode Atom atom_eq_dec support a HA) as HE.
  unfold C.decode in HE; unfold index, reify.
  destruct (C.encode atom_eq_dec support a) as [i|]; cbn [option_map] in HE; congruence.
Qed.

Theorem index_injective a b : In a support -> In b support -> index a = index b -> a = b.
Proof.
  intros HA HB E; apply (f_equal reify) in E; now rewrite !reify_index in E by assumption.
Qed.

Theorem reify_index_query : reify (index query) = query.
Proof. apply reify_index, query_supported. Qed.

Theorem reify_index_reify i : reify (index (reify i)) = reify i.
Proof. apply reify_index, reify_supported. Qed.

Lemma reify_index_list ps : Forall (fun a => In a support) ps ->
  map reify (map index ps) = ps.
Proof. intro HS; induction HS; cbn [map]; [reflexivity | now rewrite reify_index, IHHS]. Qed.

Theorem reify_indexed_clauses :
  map (map_clause reify) indexed_clauses = clauses.
Proof.
  unfold indexed_clauses; rewrite map_map.
  transitivity (map (fun c => c) clauses); [apply map_ext_in | apply map_id].
  intros [ps a] HC; destruct (clause_support ps a HC) as [HA HP].
  unfold map_clause; cbn [fst snd]; now rewrite reify_index_list, reify_index.
Qed.

Theorem reify_indexed_denials : map (map reify) indexed_denials = denials.
Proof.
  unfold indexed_denials; rewrite map_map.
  transitivity (map (fun ps => ps) denials); [apply map_ext_in | apply map_id].
  intros ps HP; apply reify_index_list, denial_support, HP.
Qed.

Definition index_proof a (p : F.Proof clauses a) : F.Proof indexed_clauses (index a) :=
  map_proof index clauses a p.

Definition reify_proof i (p : F.Proof indexed_clauses i) : F.Proof clauses (reify i).
Proof.
  rewrite <- reify_indexed_clauses; exact (map_proof reify indexed_clauses i p).
Defined.

Theorem indexed_derivation_exact a : In a support ->
  H.Derives indexed_clauses (index a) <-> H.Derives clauses a.
Proof.
  intro HA; split.
  - intro HD; pose proof (map_derivation reify indexed_clauses _ HD) as HR.
    now rewrite reify_indexed_clauses, reify_index in HR.
  - apply map_derivation.
Qed.

Theorem indexed_query_exact :
  H.Derives indexed_clauses (index query) <-> H.Derives clauses query.
Proof. apply indexed_derivation_exact, query_supported. Qed.

Theorem indexed_model_exact truth : H.Model indexed_clauses truth <->
  H.Model clauses (fun a => truth (index a)).
Proof. apply mapped_model_exact. Qed.

Theorem indexed_denials_exact truth : H.Denials indexed_denials truth <->
  H.Denials denials (fun a => truth (index a)).
Proof. apply mapped_denials_exact. Qed.

Theorem reified_model_exact truth : H.Model indexed_clauses (fun i => truth (reify i)) <->
  H.Model clauses truth.
Proof. rewrite <- mapped_model_exact, reify_indexed_clauses; reflexivity. Qed.

Theorem reified_denials_exact truth : H.Denials indexed_denials (fun i => truth (reify i)) <->
  H.Denials denials truth.
Proof. rewrite <- mapped_denials_exact, reify_indexed_denials; reflexivity. Qed.

Theorem indexed_consistency_exact :
  (exists truth, H.ConsistentModel indexed_clauses indexed_denials truth) <->
  (exists truth, H.ConsistentModel clauses denials truth).
Proof.
  split; intros [truth [HM HD]].
  - exists (fun a => truth (index a)); split;
      [now apply indexed_model_exact | now apply indexed_denials_exact].
  - exists (fun i => truth (reify i)); split;
      [now apply reified_model_exact | now apply reified_denials_exact].
Qed.

Theorem indexed_query_value :
  F.finite_truth C.fin_eq_dec indexed_clauses (index query) =
  F.finite_truth atom_eq_dec clauses query.
Proof.
  assert (HE : F.finite_truth C.fin_eq_dec indexed_clauses (index query) = true <->
    F.finite_truth atom_eq_dec clauses query = true).
  { unfold F.finite_truth; rewrite !H.member_spec, !H.saturation_exact.
    apply indexed_query_exact. }
  destruct (F.finite_truth C.fin_eq_dec indexed_clauses (index query)),
    (F.finite_truth atom_eq_dec clauses query); intuition congruence.
Qed.

Theorem indexed_checker_value :
  H.check_denials C.fin_eq_dec indexed_clauses indexed_denials =
  H.check_denials atom_eq_dec clauses denials.
Proof.
  assert (HE : H.check_denials C.fin_eq_dec indexed_clauses indexed_denials = true <->
    H.check_denials atom_eq_dec clauses denials = true).
  { rewrite !H.denial_model_exists_iff; apply indexed_consistency_exact. }
  destruct (H.check_denials C.fin_eq_dec indexed_clauses indexed_denials),
    (H.check_denials atom_eq_dec clauses denials); intuition congruence.
Qed.
End Support.

(** Concrete specialization includes ALL grounded clauses, including inactive
    tautologies, and ALL semantic instances of the unguarded Void denial. *)
Module A := MM0GuardedSyntaxAlgebra.
Module G := MM0GuardedQuantification.
Module U := FiniteUniversalHorn.
Import MM0FiniteSignature MM0FiniteAxioms.

Definition guarded_denials N d := MM0FiniteSignature.compile_negative
  None (A.algebra N d) (A.values N d) [void_denial].
Definition guarded_support N d names q := support (A.clauses N d names) (guarded_denials N d) q.
Definition guarded_index N d names q := index (ground_atom_eq_dec (A.value_eq_dec N d))
  (A.clauses N d names) (guarded_denials N d) q.
Definition guarded_indexed_clauses N d names q :=
  indexed_clauses (ground_atom_eq_dec (A.value_eq_dec N d))
    (A.clauses N d names) (guarded_denials N d) q.

Theorem guarded_clause_supported N d names q ps a :
  In (ps, a) (A.clauses N d names) ->
  In a (guarded_support N d names q) /\
  Forall (fun b => In b (guarded_support N d names q)) ps.
Proof. apply clause_support. Qed.

Theorem guarded_denial_supported N d names q ps : In ps (guarded_denials N d) ->
  Forall (fun a => In a (guarded_support N d names q)) ps.
Proof. apply denial_support. Qed.

Theorem guarded_indexed_query_exact N d names q :
  H.Derives (guarded_indexed_clauses N d names q) (guarded_index N d names q q) <->
  H.Derives (A.clauses N d names) q.
Proof. apply indexed_query_exact. Qed.

Theorem guarded_semantic_instance_present N d names name env : In name names ->
  In (projT2 (G.guarded_schema None (A.algebra N d) (A.guard N d) (axiom_rule name)) env)
    (A.clauses N d names).
Proof.
  intro Hname; apply U.positive_instance_in; [apply A.values_complete |].
  apply in_map, in_map, Hname.
Qed.

Theorem guarded_semantic_instance_supported N d names q name env : In name names ->
  let c := projT2 (G.guarded_schema None (A.algebra N d) (A.guard N d) (axiom_rule name)) env in
  In (snd c) (guarded_support N d names q) /\
    Forall (fun a => In a (guarded_support N d names q)) (fst c).
Proof.
  intro Hname; apply guarded_clause_supported; rewrite <- surjective_pairing.
  now apply guarded_semantic_instance_present.
Qed.

Theorem every_void_atom_supported N d names q x :
  In (PH, [x; void_value None (A.algebra N d)]) (guarded_support N d names q).
Proof.
  assert (HD : In [(PH, [x; void_value None (A.algebra N d)])] (guarded_denials N d)).
  { exact (U.negative_instance_in (A.values N d) (A.values_complete N d)
      (negative_schemata None (A.algebra N d) [void_denial])
      (negative_schema None (A.algebra N d) void_denial)
      (Vector.cons _ x 0 (Vector.nil _)) (or_introl eq_refl)). }
  pose proof (guarded_denial_supported N d names q _ HD) as HS; now inversion HS.
Qed.

Print Assumptions map_proof.
Print Assumptions map_proofs.
Print Assumptions map_derivation.
Print Assumptions mapped_model_exact.
Print Assumptions mapped_denials_exact.
Print Assumptions cardinality_positive.
Print Assumptions cardinality_exact.
Print Assumptions indices_complete.
Print Assumptions indices_length.
Print Assumptions query_supported.
Print Assumptions clause_support.
Print Assumptions denial_support.
Print Assumptions reify_supported.
Print Assumptions reify_index.
Print Assumptions index_injective.
Print Assumptions reify_index_query.
Print Assumptions reify_index_reify.
Print Assumptions reify_indexed_clauses.
Print Assumptions reify_indexed_denials.
Print Assumptions index_proof.
Print Assumptions reify_proof.
Print Assumptions indexed_derivation_exact.
Print Assumptions indexed_query_exact.
Print Assumptions indexed_model_exact.
Print Assumptions indexed_denials_exact.
Print Assumptions reified_model_exact.
Print Assumptions reified_denials_exact.
Print Assumptions indexed_consistency_exact.
Print Assumptions indexed_query_value.
Print Assumptions indexed_checker_value.
Print Assumptions guarded_clause_supported.
Print Assumptions guarded_denial_supported.
Print Assumptions guarded_indexed_query_exact.
Print Assumptions guarded_semantic_instance_present.
Print Assumptions guarded_semantic_instance_supported.
Print Assumptions every_void_atom_supported.
End GuardedFiniteSupport.
