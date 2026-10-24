From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks Reduction AbstractRewriting Congruence.
From PTSrk.Combinatory Require Import FiniteHorn FiniteModelRealization
  FiniteModelSoundness ChurchFinite NativeCanonicity MM0FiniteSignature
  MM0FiniteAxioms MM0SyntaxSoundness MM0GuardedSyntaxAlgebra MM0GuardedReflection
  MM0HilbertAdequacy GuardedFiniteSupport MM0GuardedInternalReflection
  MM0GuardProvenance HornProofRealization IndexedHornEncoding IndexedHornRealization
  IndexedHornSoundness FiniteTypeDispatch.
Import ListNotations.

(** One original-PTS soundness function per fixed guarded fragment/support.
    The query and its proof are INTERNAL arguments. The support seed fixes
    one finite domain once; it is not regenerated for each queried atom.
    Canonical indexing, not arbitrary duplicate positions, reflects source
    derivability. Budgets and the finite clause list remain external. *)
Module MM0IndexedReflection.
Import MM0FiniteSignature MM0FiniteAxioms.
Module A := MM0GuardedSyntaxAlgebra.MM0GuardedSyntaxAlgebra.
Module R := MM0GuardedReflection.MM0GuardedReflection.
Module F := GuardedFiniteSupport.GuardedFiniteSupport.
Module Old := MM0GuardedInternalReflection.MM0GuardedInternalReflection.
Module I := IndexedHornEncoding.IndexedHornEncoding.
Module IR := IndexedHornRealization.IndexedHornRealization.
Module S := IndexedHornSoundness.IndexedHornSoundness.
Module CF := ChurchFinite.ChurchFinite.
Module M := FiniteModelRealization.FiniteModelRealization.
Module FMS := FiniteModelSoundness.FiniteModelSoundness.
Module P := MM0GuardProvenance.MM0GuardProvenance.
Module D := FiniteTypeDispatch.FiniteTypeDispatch.

Definition code_type {n} N d names seed : Term nat n :=
  I.code_type (Old.atom_count N d names seed).
Definition proof_type {n} N d names seed (q : Term nat n) :=
  I.proof_type (Old.clauses N d names seed) q.
Definition query_code {n} N d names seed a : Term nat n :=
  CF.selector 0 (Old.atom_count N d names seed) (F.guarded_index N d names seed a).
Definition truth_predicate {n} N d names seed : Term nat n :=
  S.truth_predicate (Old.truth N d names seed).
Definition reflect {n} N d names seed : Term nat n :=
  S.uniform_reflect (Old.clauses N d names seed) (Old.truth N d names seed).
Definition reflection_type {n} N d names seed : Term nat n :=
  S.uniform_reflection_type (Old.clauses N d names seed) (Old.truth N d names seed).

Theorem query_roundtrip N d names seed a :
  In a (F.guarded_support N d names seed) ->
  Old.truth N d names seed (F.guarded_index N d names seed a) = R.query N d names a.
Proof.
  intro HA; unfold Old.truth, Old.reify, F.guarded_index.
  now rewrite F.reify_index.
Qed.
Theorem code_type_sorted {n} (ctx : Ctx nat n) N d names seed :
  @typ nat RankSorts n ctx (code_type N d names seed) (𝓤 1).
Proof. apply I.code_type_sorted. Qed.
Theorem query_code_typed {n} (ctx : Ctx nat n) N d names seed a :
  @typ nat RankSorts n ctx (query_code N d names seed a) (code_type N d names seed).
Proof. apply CF.selector_typed. Qed.
Theorem proof_type_sorted {n} (ctx : Ctx nat n) N d names seed q :
  @typ nat RankSorts n ctx q (code_type N d names seed) ->
  @typ nat RankSorts n ctx (proof_type N d names seed q) (𝓤 3).
Proof. apply I.proof_type_sorted. Qed.
Theorem reflect_typed {n} (ctx : Ctx nat n) N d names seed :
  @typ nat RankSorts n ctx (reflect N d names seed) (reflection_type N d names seed).
Proof. apply S.uniform_reflect_typed, Old.indexed_truth_model. Qed.
Theorem reflection_type_sorted {n} (ctx : Ctx nat n) N d names seed :
  @typ nat RankSorts n ctx (reflection_type N d names seed) (𝓤 4).
Proof. apply S.uniform_reflection_type_sorted. Qed.

Theorem arbitrary_query_sound {n} (ctx : Ctx nat n) N d names seed q p :
  @typ nat RankSorts n ctx q (code_type N d names seed) ->
  @typ nat RankSorts n ctx p (proof_type N d names seed q) ->
  @typ nat RankSorts n ctx (app (app (reflect N d names seed) q) p)
    (app (truth_predicate N d names seed) q).
Proof. intros HQ HP; apply S.arbitrary_query_sound;
  [apply Old.indexed_truth_model | exact HQ | exact HP]. Qed.

Theorem canonical_reflection_typed {n} (ctx : Ctx nat n) N d names seed a :
  In a (F.guarded_support N d names seed) ->
  @typ nat RankSorts n ctx (app (reflect N d names seed) (query_code N d names seed a))
    (Π (proof_type N d names seed (query_code N d names seed a))
      (M.truth_type (R.query N d names a))).
Proof.
  intro HA; eapply typ_conv.
  - apply S.uniform_query_typed; [apply Old.indexed_truth_model | apply query_code_typed].
  - eapply typ_Π; [apply proof_type_sorted, query_code_typed |
      apply M.truth_type_sorted | reflexivity].
  - apply D.reduction_equiv; unfold S.reflection_at_type.
    apply (@Π_cong_r nat (reduces_to nat) _); unfold query_code, shift.
    rewrite CF.selector_rename.
    rewrite <- (query_roundtrip N d names seed a HA); apply S.truth_selector_beta.
Qed.

Theorem canonical_query_sound {n} (ctx : Ctx nat n) N d names seed a p :
  In a (F.guarded_support N d names seed) ->
  @typ nat RankSorts n ctx p (proof_type N d names seed (query_code N d names seed a)) ->
  @typ nat RankSorts n ctx
    (app (app (reflect N d names seed) (query_code N d names seed a)) p)
    (M.truth_type (R.query N d names a)).
Proof.
  intros HA HP; pose proof (S.canonical_query_sound ctx
    (Old.atom_count N d names seed) (Old.clauses N d names seed)
    (Old.truth N d names seed) (F.guarded_index N d names seed a) p
    (Old.indexed_truth_model N d names seed) HP) as HT.
  now rewrite query_roundtrip in HT.
Qed.

Theorem canonical_proof_exact N d names seed a :
  In a (F.guarded_support N d names seed) ->
  (exists p, @typ nat RankSorts 0 ε p
    (proof_type N d names seed (query_code N d names seed a))) <->
  FiniteHorn.Derives (A.clauses N d names) a.
Proof.
  intro HA; unfold proof_type, query_code; rewrite IR.proof_inhabited_exact.
  now apply F.indexed_derivation_exact.
Qed.
Theorem canonical_query_exact N d names seed a :
  In a (F.guarded_support N d names seed) ->
  (exists p, @typ nat RankSorts 0 ε p
    (proof_type N d names seed (query_code N d names seed a))) <->
  R.query N d names a = true.
Proof.
  intro HA; rewrite canonical_proof_exact by exact HA.
  unfold R.query, FMS.finite_truth; rewrite FiniteHorn.member_spec,
    FiniteHorn.saturation_exact; reflexivity.
Qed.
Theorem canonical_closed_proof_reflects N d names seed a p :
  In a (F.guarded_support N d names seed) ->
  @typ nat RankSorts 0 ε p (proof_type N d names seed (query_code N d names seed a)) ->
  R.SourceTruth N d names a.
Proof.
  intros HA HP; apply R.finite_derivation_reflects.
  apply (proj1 (canonical_proof_exact N d names seed a HA)); now exists p.
Qed.

Definition encode N d names seed a (p : FMS.Proof (A.clauses N d names) a) : Term nat 0 :=
  IR.encode (Old.clauses N d names seed)
    (F.index_proof (ground_atom_eq_dec (A.value_eq_dec N d))
      (A.clauses N d names) (F.guarded_denials N d) seed a p).
Theorem encode_typed N d names seed a (p : FMS.Proof (A.clauses N d names) a) :
  @typ nat RankSorts 0 ε (encode N d names seed a p)
    (proof_type N d names seed (query_code N d names seed a)).
Proof. apply IR.encode_typed. Qed.

Theorem void_internal_refuter {n} (ctx : Ctx nat n) N d names seed x :
  5 <= N -> 3 <= d ->
  let a := (PH, [x; void_value None (A.algebra N d)]) in
  @typ nat RankSorts n ctx (app (reflect N d names seed) (query_code N d names seed a))
    (Π (proof_type N d names seed (query_code N d names seed a)) (M.truth_type false)).
Proof.
  intros HN HD; cbn zeta.
  pose proof (canonical_reflection_typed ctx N d names seed
    (PH, [x; void_value None (A.algebra N d)])
    (F.every_void_atom_supported N d names seed x)) as HT.
  now rewrite MM0HilbertAdequacy.guarded_every_void_query_false in HT by assumption.
Qed.
Theorem void_encoded_uninhabited N d names seed x : 5 <= N -> 3 <= d ->
  ~ exists p, @typ nat RankSorts 0 ε p
    (proof_type N d names seed
      (query_code N d names seed (PH, [x; void_value None (A.algebra N d)]))).
Proof.
  intros HN HD HP; apply (proj1 (canonical_query_exact N d names seed _
    (F.every_void_atom_supported N d names seed x))) in HP.
  rewrite MM0HilbertAdequacy.guarded_every_void_query_false in HP by assumption; discriminate.
Qed.

(** A second fixed finite presentation retains literal raw source-instance
    provenance. Its overflow marker is never identified with the numeral0.
    The reflected proof may be ANY native inhabitant of its indexed type. *)
Definition observation_eq_dec (x y : P.Observation) : {x = y} + {x <> y}.
Proof. decide equality; apply A.expr_eq_dec. Defined.
Definition raw_eq_dec := ground_atom_eq_dec observation_eq_dec.
Definition raw_indexed_clauses N d names a :=
  F.indexed_clauses raw_eq_dec (P.raw_clauses N d names) [] a.
Definition raw_proof_type {n} N d names a : Term nat n :=
  I.proof_type (raw_indexed_clauses N d names a)
    (CF.selector 0 (F.cardinality (P.raw_clauses N d names) [] a)
      (F.index raw_eq_dec (P.raw_clauses N d names) [] a a)).
Theorem raw_proof_type_sorted {n} (ctx : Ctx nat n) N d names a :
  @typ nat RankSorts n ctx (raw_proof_type N d names a) (𝓤 3).
Proof. apply I.proof_type_sorted, CF.selector_typed. Qed.
Theorem raw_proof_exact N d names a :
  (exists p, @typ nat RankSorts 0 ε p (raw_proof_type N d names a)) <->
  FiniteHorn.Derives (P.raw_clauses N d names) a.
Proof. unfold raw_proof_type; rewrite IR.proof_inhabited_exact; apply F.indexed_query_exact. Qed.
Definition raw_encode N d names a (p : FMS.Proof (P.raw_clauses N d names) a) : Term nat 0 :=
  IR.encode (raw_indexed_clauses N d names a)
    (F.index_proof raw_eq_dec (P.raw_clauses N d names) [] a a p).
Theorem raw_encode_typed N d names a (p : FMS.Proof (P.raw_clauses N d names) a) :
  @typ nat RankSorts 0 ε (raw_encode N d names a p) (raw_proof_type N d names a).
Proof. apply IR.encode_typed. Qed.
Theorem raw_closed_proof_reflects N d names a p :
  @typ nat RankSorts 0 ε p (raw_proof_type N d names a) -> P.SourceConclusion names a.
Proof.
  intro HP; apply (P.raw_derivation_reflects N d names), raw_proof_exact; now exists p.
Qed.
Theorem raw_closed_proof_no_overflow N d names pred xs p :
  @typ nat RankSorts 0 ε p (raw_proof_type N d names (pred, xs)) -> ~ In None xs.
Proof.
  intro HP; apply P.raw_derivation_no_overflow with (N := N) (d := d) (names := names)
    (p := pred); apply raw_proof_exact; now exists p.
Qed.
Theorem raw_source_union_exact names a :
  inhabited (MM0SyntaxSoundness.Derivation names a) <->
  exists N d p, @typ nat RankSorts 0 ε p (raw_proof_type N d names (P.quote_atom a)).
Proof.
  rewrite P.raw_source_union_exact; split.
  - intros [N [d HD]]; apply raw_proof_exact in HD as [p HP]; now exists N, d, p.
  - intros [N [d [p HP]]]; exists N, d; apply raw_proof_exact; now exists p.
Qed.
Theorem raw_void_uninhabited N d names e :
  ~ exists p, @typ nat RankSorts 0 ε p
    (raw_proof_type N d names (P.quote_atom (PH, [e; EPi (EU EZ) (EV EZ)]))).
Proof.
  intros [p HP]; apply raw_closed_proof_reflects in HP as [source [HE HS]].
  apply P.quote_atom_injective in HE; subst source.
  exact (MM0HilbertAdequacy.source_void_excluded names e HS).
Qed.

(** Duplicate support positions are aliases, not extra inference rules.
    The second position decodes to true but has no indexed derivation. *)
Example duplicate_alias_boundary :
  let cs := [([], true)] in
  let indexed := F.indexed_clauses Bool.bool_dec cs [] true in
  F.reify cs [] true fzero = F.reify cs [] true (fsucc fzero) /\
  FMS.finite_truth HornProofRealization.index_eq_dec indexed fzero = true /\
  FMS.finite_truth HornProofRealization.index_eq_dec indexed (fsucc fzero) = false.
Proof. repeat split; reflexivity. Qed.

Print Assumptions query_roundtrip.
Print Assumptions code_type_sorted.
Print Assumptions query_code_typed.
Print Assumptions proof_type_sorted.
Print Assumptions reflect_typed.
Print Assumptions reflection_type_sorted.
Print Assumptions arbitrary_query_sound.
Print Assumptions canonical_reflection_typed.
Print Assumptions canonical_query_sound.
Print Assumptions canonical_proof_exact.
Print Assumptions canonical_query_exact.
Print Assumptions canonical_closed_proof_reflects.
Print Assumptions encode_typed.
Print Assumptions void_internal_refuter.
Print Assumptions void_encoded_uninhabited.
Print Assumptions raw_proof_type_sorted.
Print Assumptions raw_proof_exact.
Print Assumptions raw_encode_typed.
Print Assumptions raw_closed_proof_reflects.
Print Assumptions raw_closed_proof_no_overflow.
Print Assumptions raw_source_union_exact.
Print Assumptions raw_void_uninhabited.
Print Assumptions duplicate_alias_boundary.
End MM0IndexedReflection.
