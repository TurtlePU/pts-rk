From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From PTSrk.Combinatory Require Import FiniteHorn FiniteModelRealization
  FiniteModelSoundness NativeCanonicity MM0FiniteSignature MM0FiniteAxioms
  MM0SyntaxSoundness MM0GuardedQuantification MM0GuardedSyntaxAlgebra
  MM0GuardedReflection MM0HilbertAdequacy GuardedFiniteCarriers
  GuardedFiniteSupport HornProofEncoding HornProofRealization HornInternalSoundness
  CatalogueEconomy MM0NativeSyntax.
Import ListNotations.

(** Fixed-fragment internal reflection for arbitrary Church proof inhabitants.
    The proof type contains the independently grounded guarded rule list,
    not a model or a semantic typing hypothesis.  Every valuation instance
    and every universal Void denial is included in its finite atom support.
    The finite theory/query are external parameters of the term generator;
    this is not one internally budget-polymorphic source reflection theorem. *)
Module MM0GuardedInternalReflection.
Import MM0FiniteSignature MM0FiniteAxioms.
Module A := MM0GuardedSyntaxAlgebra.MM0GuardedSyntaxAlgebra.
Module R := MM0GuardedReflection.MM0GuardedReflection.
Module G := MM0GuardedQuantification.MM0GuardedQuantification.
Module F := GuardedFiniteSupport.GuardedFiniteSupport.
Module E := HornProofEncoding.HornProofEncoding.
Module H := HornInternalSoundness.HornInternalSoundness.
Module M := FiniteModelRealization.FiniteModelRealization.
Module FMS := FiniteModelSoundness.FiniteModelSoundness.
Module Realize := HornProofRealization.HornProofRealization.

Definition atom_count N d names q :=
  F.cardinality (A.clauses N d names) (F.guarded_denials N d) q.
Definition reify N d names q :=
  F.reify (A.clauses N d names) (F.guarded_denials N d) q.
Definition clauses N d names q := F.guarded_indexed_clauses N d names q.
Definition query_index N d names q := F.guarded_index N d names q q.
Definition truth N d names q (i : Fin (atom_count N d names q)) :=
  R.query N d names (reify N d names q i).
Definition proof_type {n} N d names q : Term nat n :=
  E.proof_type (atom_count N d names q) (clauses N d names q) (query_index N d names q).
Definition reflect {n} N d names q : Term nat n :=
  H.reflect (atom_count N d names q) (clauses N d names q)
    (query_index N d names q) (truth N d names q).
Definition reflection_type {n} N d names q : Term nat n :=
  Π (proof_type N d names q) (M.truth_type (R.query N d names q)).

Theorem query_roundtrip N d names q :
  truth N d names q (query_index N d names q) = R.query N d names q.
Proof. unfold truth, reify, query_index, F.guarded_index; now rewrite F.reify_index_query. Qed.

Theorem indexed_truth_model N d names q :
  FiniteHorn.Model (clauses N d names q) (fun i => truth N d names q i = true).
Proof.
  unfold clauses, F.guarded_indexed_clauses, truth, reify.
  apply (proj2 (F.reified_model_exact (ground_atom_eq_dec (A.value_eq_dec N d))
    (A.clauses N d names) (F.guarded_denials N d) q
    (fun a => R.query N d names a = true))).
  apply FMS.finite_truth_model.
Qed.

Theorem proof_type_sorted {n} (ctx : Ctx nat n) N d names q :
  @typ nat RankSorts n ctx (proof_type N d names q)
    (𝓤 (E.matrix_rank (clauses N d names q))).
Proof. apply E.proof_type_sorted. Qed.
Theorem proof_type_rank_bound N d names q : E.matrix_rank (clauses N d names q) <= 3.
Proof. apply E.proof_type_rank_bound. Qed.

Theorem reflect_typed {n} (ctx : Ctx nat n) N d names q :
  @typ nat RankSorts n ctx (reflect N d names q) (reflection_type N d names q).
Proof.
  pose proof (H.reflect_typed ctx (atom_count N d names q) (clauses N d names q)
    (query_index N d names q) (truth N d names q) (indexed_truth_model N d names q)) as HT.
  unfold H.reflection_type in HT; rewrite query_roundtrip in HT; exact HT.
Qed.
Theorem reflection_type_sorted {n} (ctx : Ctx nat n) N d names q :
  @typ nat RankSorts n ctx (reflection_type N d names q)
    (𝓤 (S (E.matrix_rank (clauses N d names q)))).
Proof.
  pose proof (H.reflection_type_sorted ctx (atom_count N d names q)
    (clauses N d names q) (query_index N d names q) (truth N d names q)) as HT.
  unfold H.reflection_type in HT; rewrite query_roundtrip in HT; exact HT.
Qed.
Theorem reflection_type_rank_bound N d names q :
  S (E.matrix_rank (clauses N d names q)) <= 4.
Proof. apply H.reflection_type_rank_bound. Qed.

Theorem arbitrary_encoded_proof_sound {n} (ctx : Ctx nat n) N d names q p :
  @typ nat RankSorts n ctx p (proof_type N d names q) ->
  @typ nat RankSorts n ctx (app (reflect N d names q) p)
    (M.truth_type (R.query N d names q)).
Proof.
  intro HP; pose proof (H.arbitrary_proof_sound ctx (atom_count N d names q)
    (clauses N d names q) (query_index N d names q) (truth N d names q) p
    (indexed_truth_model N d names q) HP) as HT.
  rewrite query_roundtrip in HT; exact HT.
Qed.

Theorem arbitrary_closed_proof_reflects N d names q p :
  @typ nat RankSorts 0 ε p (proof_type N d names q) -> R.SourceTruth N d names q.
Proof.
  intro HP; apply R.accepted_query_reflects.
  pose proof (H.arbitrary_closed_proof_true (atom_count N d names q)
    (clauses N d names q) (query_index N d names q) (truth N d names q) p
    (indexed_truth_model N d names q) HP) as HT.
  now rewrite query_roundtrip in HT.
Qed.

Theorem void_internal_refuter {n} (ctx : Ctx nat n) N d names x :
  5 <= N -> 3 <= d ->
  @typ nat RankSorts n ctx
    (reflect N d names (PH, [x; void_value None (A.algebra N d)]))
    (Π (proof_type N d names (PH, [x; void_value None (A.algebra N d)]))
       (M.truth_type false)).
Proof.
  intros HN HD; pose proof (reflect_typed ctx N d names
    (PH, [x; void_value None (A.algebra N d)])) as HT.
  unfold reflection_type in HT.
  now rewrite MM0HilbertAdequacy.guarded_every_void_query_false in HT by assumption.
Qed.

Theorem void_encoded_uninhabited N d names x : 5 <= N -> 3 <= d ->
  ~ exists p, @typ nat RankSorts 0 ε p
    (proof_type N d names (PH, [x; void_value None (A.algebra N d)])).
Proof.
  intros HN HD [p HP].
  pose proof (arbitrary_encoded_proof_sound ε _ _ _ _ p HP) as HT.
  rewrite MM0HilbertAdequacy.guarded_every_void_query_false in HT by assumption.
  exact (NativeCanonicity.void_empty _ HT).
Qed.

Definition encode N d names q (p : FMS.Proof (A.clauses N d names) q) : Term nat 0 :=
  Realize.encode (clauses N d names q)
    (F.index_proof (ground_atom_eq_dec (A.value_eq_dec N d))
      (A.clauses N d names) (F.guarded_denials N d) q q p).
Theorem encode_typed N d names q (p : FMS.Proof (A.clauses N d names) q) :
  @typ nat RankSorts 0 ε (encode N d names q p) (proof_type N d names q).
Proof. apply Realize.encode_typed. Qed.

Definition encode_source N d names a h (p : G.GuardedDerivation names N d h a) :=
  encode N d names (evaluate_atom None (A.algebra N d) [] a)
    (A.source_proof N d names a h p).
Theorem encode_source_typed N d names a h (p : G.GuardedDerivation names N d h a) :
  @typ nat RankSorts 0 ε (encode_source N d names a h p)
    (proof_type N d names (evaluate_atom None (A.algebra N d) [] a)).
Proof. apply encode_typed. Qed.

Theorem encoded_proof_exact N d names q :
  (exists p, @typ nat RankSorts 0 ε p (proof_type N d names q)) <->
  FiniteHorn.Derives (A.clauses N d names) q.
Proof.
  unfold proof_type; rewrite H.proof_inhabited_exact.
  apply F.guarded_indexed_query_exact.
Qed.
Theorem encoded_query_exact N d names q :
  (exists p, @typ nat RankSorts 0 ε p (proof_type N d names q)) <->
  R.query N d names q = true.
Proof.
  rewrite encoded_proof_exact; unfold R.query, FMS.finite_truth.
  rewrite FiniteHorn.member_spec, FiniteHorn.saturation_exact; reflexivity.
Qed.

Theorem source_union_exact names a :
  inhabited (MM0SyntaxSoundness.Derivation names a) <->
  exists N d,
    (exists p, @typ nat RankSorts 0 ε p
      (proof_type N d names (evaluate_atom None (A.algebra N d) [] a))) /\
    R.decoded_atom N d (evaluate_atom None (A.algebra N d) [] a) = a.
Proof.
  rewrite R.source_union_exact; split.
  - intros [N [d [HQ HE]]]; exists N, d; split;
      [now apply encoded_query_exact | exact HE].
  - intros [N [d [HQ HE]]]; exists N, d; split;
      [now apply encoded_query_exact | exact HE].
Qed.

Theorem catalogue_consistent_code_coverage (M T : Term nat 0) :
  CatalogueEconomy.Derives M T <-> exists N d,
    5 <= N /\ 3 <= d /\ A.checker N d all_axioms = true /\
    (exists p, @typ nat RankSorts 0 ε p
      (proof_type N d all_axioms (evaluate_atom None (A.algebra N d) []
        (aH (MM0NativeSyntax.quote_term M) (MM0NativeSyntax.quote_term T))))) /\
    R.decoded_atom N d (evaluate_atom None (A.algebra N d) []
      (aH (MM0NativeSyntax.quote_term M) (MM0NativeSyntax.quote_term T))) =
      aH (MM0NativeSyntax.quote_term M) (MM0NativeSyntax.quote_term T).
Proof.
  rewrite MM0HilbertAdequacy.consistent_finite_union_exact.
  split.
  - intros [N [d [HN [HD [HC [HQ HE]]]]]]; exists N, d.
    split; [exact HN |]; split; [exact HD |]; split; [exact HC |].
    split; [now apply encoded_query_exact | exact HE].
  - intros [N [d [HN [HD [HC [HQ HE]]]]]]; exists N, d.
    split; [exact HN |]; split; [exact HD |]; split; [exact HC |].
    split; [now apply encoded_query_exact | exact HE].
Qed.

Print Assumptions query_roundtrip.
Print Assumptions indexed_truth_model.
Print Assumptions proof_type_sorted.
Print Assumptions proof_type_rank_bound.
Print Assumptions reflect_typed.
Print Assumptions reflection_type_sorted.
Print Assumptions reflection_type_rank_bound.
Print Assumptions arbitrary_encoded_proof_sound.
Print Assumptions arbitrary_closed_proof_reflects.
Print Assumptions void_internal_refuter.
Print Assumptions void_encoded_uninhabited.
Print Assumptions encode_typed.
Print Assumptions encode_source_typed.
Print Assumptions encoded_proof_exact.
Print Assumptions encoded_query_exact.
Print Assumptions source_union_exact.
Print Assumptions catalogue_consistent_code_coverage.
End MM0GuardedInternalReflection.
