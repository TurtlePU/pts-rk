From Stdlib Require Import Lists.List Arith.PeanoNat.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks Reduction.
From PTSrk.Combinatory Require Import ChurchFinite FiniteHorn FiniteModelSoundness
  MM0FiniteSignature MM0FiniteAxioms MM0SyntaxSoundness MM0GuardedSyntaxAlgebra
  MM0GuardProvenance GuardedFiniteSupport MM0GuardedInternalReflection
  MM0IndexedReflection IndexedHornEncoding IndexedHornRealization IndexedHornTransport
  IndexedHornSoundness GuardedFiniteCarriers.
Import ListNotations.

(** A fixed finite decoder from semantic atom positions to independent raw
    observations. Both supports are fixed before an internal query is given.
    Reserve lists enlarge the raw support only: they are NOT denial axioms
    and do not contribute proof constructors. Overflow remains None. *)
Module MM0InternalDecoder.
Import MM0FiniteSignature MM0FiniteAxioms.
Module A := MM0GuardedSyntaxAlgebra.MM0GuardedSyntaxAlgebra.
Module P := MM0GuardProvenance.MM0GuardProvenance.
Module F := GuardedFiniteSupport.GuardedFiniteSupport.
Module Old := MM0GuardedInternalReflection.MM0GuardedInternalReflection.
Module M := MM0IndexedReflection.MM0IndexedReflection.
Module I := IndexedHornEncoding.IndexedHornEncoding.
Module IR := IndexedHornRealization.IndexedHornRealization.
Module CF := ChurchFinite.ChurchFinite.
Module T := IndexedHornTransport.IndexedHornTransport.
Module S := IndexedHornSoundness.IndexedHornSoundness.
Module FMS := FiniteModelSoundness.FiniteModelSoundness.

Definition raw_reserve N d names seed :=
  map (fun a => [P.observe_atom N d a]) (F.guarded_support N d names seed).
Definition raw_anchor N d seed := P.observe_atom N d seed.
Definition raw_support N d names seed :=
  F.support (P.raw_clauses N d names) (raw_reserve N d names seed) (raw_anchor N d seed).
Definition raw_count N d names seed := length (raw_support N d names seed).
Definition raw_index N d names seed :=
  F.index M.raw_eq_dec (P.raw_clauses N d names) (raw_reserve N d names seed)
    (raw_anchor N d seed).
Definition raw_reify N d names seed :=
  F.reify (P.raw_clauses N d names) (raw_reserve N d names seed) (raw_anchor N d seed).
Definition raw_clauses N d names seed :=
  F.indexed_clauses M.raw_eq_dec (P.raw_clauses N d names)
    (raw_reserve N d names seed) (raw_anchor N d seed).
Definition atom_map N d names seed (i : Fin (Old.atom_count N d names seed)) :=
  raw_index N d names seed (P.observe_atom N d (Old.reify N d names seed i)).

Theorem observed_supported N d names seed a :
  In a (F.guarded_support N d names seed) ->
  In (P.observe_atom N d a) (raw_support N d names seed).
Proof.
  intro HA; unfold raw_support, F.support, F.support_tail; right.
  apply in_app_iff; right; apply in_concat.
  exists [P.observe_atom N d a]; split.
  - unfold raw_reserve; apply in_map_iff; exists a; auto.
  - now left.
Qed.

Theorem atom_map_exact N d names seed i :
  raw_reify N d names seed (atom_map N d names seed i) =
  P.observe_atom N d (Old.reify N d names seed i).
Proof.
  unfold raw_reify, atom_map, raw_index; apply F.reify_index.
  apply observed_supported, F.reify_supported.
Qed.

Theorem atom_map_canonical N d names seed a :
  In a (F.guarded_support N d names seed) ->
  atom_map N d names seed (F.guarded_index N d names seed a) =
  raw_index N d names seed (P.observe_atom N d a).
Proof.
  intro HA; unfold atom_map, Old.reify, F.guarded_index.
  now rewrite F.reify_index.
Qed.

Theorem selected_clause_mapped N d names seed ps a :
  In (ps,a) (Old.clauses N d names seed) ->
  In (map (atom_map N d names seed) ps, atom_map N d names seed a)
    (raw_clauses N d names seed).
Proof.
  unfold Old.clauses, F.guarded_indexed_clauses, F.indexed_clauses.
  intro HC; apply in_map_iff in HC as [[qs b] [HE HC]].
  unfold F.map_clause in HE; cbn in HE; injection HE as <- <-.
  destruct (F.guarded_clause_supported N d names seed qs b HC) as [HB HQ].
  change (In (map (atom_map N d names seed) (map (F.guarded_index N d names seed) qs),
    atom_map N d names seed (F.guarded_index N d names seed b))
    (raw_clauses N d names seed)).
  rewrite atom_map_canonical by exact HB.
  assert (HM : map (atom_map N d names seed) (map (F.guarded_index N d names seed) qs) =
    map (raw_index N d names seed) (map (P.observe_atom N d) qs)).
  { rewrite !map_map; apply map_ext_in; intros c HC'.
    apply atom_map_canonical; now apply (proj1 (Forall_forall _ _) HQ). }
  rewrite HM; unfold raw_clauses, F.indexed_clauses.
  apply (in_map (F.map_clause (raw_index N d names seed))
    (P.raw_clauses N d names) (P.observe_clause N d (qs,b))).
  apply P.raw_clauses_exact; exists (qs,b); auto.
Qed.

Definition decoder {n} N d names seed : Term nat n :=
  CF.map_table 0 (Old.atom_count N d names seed) (raw_count N d names seed)
    (atom_map N d names seed).
Definition decoder_type {n} N d names seed : Term nat n :=
  CF.map_type 0 (Old.atom_count N d names seed) (raw_count N d names seed).
Definition raw_code_type {n} N d names seed : Term nat n :=
  I.code_type (raw_count N d names seed).
Definition raw_query_code {n} N d names seed a : Term nat n :=
  CF.selector 0 (raw_count N d names seed) (raw_index N d names seed a).
Definition raw_proof_type {n} N d names seed (q : Term nat n) :=
  I.proof_type (raw_clauses N d names seed) q.

Theorem decoder_typed {n} (ctx : Ctx nat n) N d names seed :
  @typ nat RankSorts n ctx (decoder N d names seed) (decoder_type N d names seed).
Proof. apply CF.map_typed. Qed.
Theorem decoder_type_sorted {n} (ctx : Ctx nat n) N d names seed :
  @typ nat RankSorts n ctx (decoder_type N d names seed) (𝓤 2).
Proof. apply CF.map_type_sorted. Qed.
Theorem decoder_selector_beta {n} N d names seed i :
  reduces_to nat n
    (app (decoder N d names seed) (CF.selector 0 (Old.atom_count N d names seed) i))
    (raw_query_code N d names seed (P.observe_atom N d (Old.reify N d names seed i))).
Proof. apply CF.map_selector_beta. Qed.
Theorem decoder_canonical_beta {n} N d names seed a :
  In a (F.guarded_support N d names seed) ->
  reduces_to nat n (app (decoder N d names seed) (M.query_code N d names seed a))
    (raw_query_code N d names seed (P.observe_atom N d a)).
Proof.
  intro HA; pose proof (@decoder_selector_beta n N d names seed
    (F.guarded_index N d names seed a)) as HB.
  unfold Old.reify, F.guarded_index in HB; now rewrite F.reify_index in HB.
Qed.
Theorem raw_code_type_sorted {n} (ctx : Ctx nat n) N d names seed :
  @typ nat RankSorts n ctx (raw_code_type N d names seed) (𝓤 1).
Proof. apply I.code_type_sorted. Qed.
Theorem raw_query_code_typed {n} (ctx : Ctx nat n) N d names seed a :
  @typ nat RankSorts n ctx (raw_query_code N d names seed a) (raw_code_type N d names seed).
Proof. apply CF.selector_typed. Qed.
Theorem raw_proof_type_sorted {n} (ctx : Ctx nat n) N d names seed q :
  @typ nat RankSorts n ctx q (raw_code_type N d names seed) ->
  @typ nat RankSorts n ctx (raw_proof_type N d names seed q) (𝓤 3).
Proof. apply I.proof_type_sorted. Qed.

(** The decoder's correctness is now consumed inside the original PTS:
    the target is the independent raw proof family, not a truth proposition
    or a metatheoretically selected result certificate. *)
Definition decode_proof {n} N d names seed : Term nat n :=
  T.uniform_transport (atom_map N d names seed)
    (Old.clauses N d names seed) (raw_clauses N d names seed).
Definition decode_proof_type {n} N d names seed : Term nat n :=
  T.uniform_transport_type (atom_map N d names seed)
    (Old.clauses N d names seed) (raw_clauses N d names seed).
Theorem decode_proof_typed {n} (ctx : Ctx nat n) N d names seed :
  @typ nat RankSorts n ctx (decode_proof N d names seed) (decode_proof_type N d names seed).
Proof. apply T.uniform_transport_typed; exact (selected_clause_mapped N d names seed). Qed.
Theorem decode_proof_type_sorted {n} (ctx : Ctx nat n) N d names seed :
  @typ nat RankSorts n ctx (decode_proof_type N d names seed) (𝓤 4).
Proof. apply T.uniform_transport_type_sorted. Qed.
Theorem arbitrary_query_decode {n} (ctx : Ctx nat n) N d names seed q p :
  @typ nat RankSorts n ctx q (M.code_type N d names seed) ->
  @typ nat RankSorts n ctx p (M.proof_type N d names seed q) ->
  @typ nat RankSorts n ctx (app (app (decode_proof N d names seed) q) p)
    (raw_proof_type N d names seed (app (decoder N d names seed) q)).
Proof.
  intros HQ HP; apply T.arbitrary_query_transport;
    [exact (selected_clause_mapped N d names seed) | exact HQ | exact HP].
Qed.
Theorem canonical_query_decode {n} (ctx : Ctx nat n) N d names seed a p :
  In a (F.guarded_support N d names seed) ->
  @typ nat RankSorts n ctx p
    (M.proof_type N d names seed (M.query_code N d names seed a)) ->
  @typ nat RankSorts n ctx
    (app (app (decode_proof N d names seed) (M.query_code N d names seed a)) p)
    (raw_proof_type N d names seed (raw_query_code N d names seed (P.observe_atom N d a))).
Proof.
  intros HA HP; pose proof (T.canonical_query_transport ctx _ _ (atom_map N d names seed)
    (Old.clauses N d names seed) (raw_clauses N d names seed)
    (F.guarded_index N d names seed a) p (selected_clause_mapped N d names seed) HP) as HT.
  now rewrite atom_map_canonical in HT.
Qed.

Theorem raw_canonical_proof_exact N d names seed a :
  In a (raw_support N d names seed) ->
  (exists p, @typ nat RankSorts 0 ε p
    (raw_proof_type N d names seed (raw_query_code N d names seed a))) <->
  FiniteHorn.Derives (P.raw_clauses N d names) a.
Proof.
  intro HA; unfold raw_proof_type, raw_query_code; rewrite IR.proof_inhabited_exact.
  now apply F.indexed_derivation_exact.
Qed.

Theorem raw_canonical_source_reflection N d names seed a p :
  In a (raw_support N d names seed) ->
  @typ nat RankSorts 0 ε p
    (raw_proof_type N d names seed (raw_query_code N d names seed a)) ->
  P.SourceConclusion names a.
Proof.
  intros HA HP; apply (P.raw_derivation_reflects N d names).
  apply (proj1 (raw_canonical_proof_exact N d names seed a HA)); now exists p.
Qed.

Theorem canonical_decoded_source_reflection N d names seed a p :
  In a (F.guarded_support N d names seed) ->
  @typ nat RankSorts 0 ε p
    (M.proof_type N d names seed (M.query_code N d names seed a)) ->
  P.SourceConclusion names (P.observe_atom N d a).
Proof.
  intros HA HP; eapply raw_canonical_source_reflection.
  - apply observed_supported, HA.
  - exact (canonical_query_decode ε N d names seed a p HA HP).
Qed.

Theorem raw_canonical_no_overflow N d names seed pred xs p :
  In (pred,xs) (raw_support N d names seed) ->
  @typ nat RankSorts 0 ε p
    (raw_proof_type N d names seed (raw_query_code N d names seed (pred,xs))) ->
  ~ In None xs.
Proof.
  intros HA HP; apply (P.raw_derivation_no_overflow N d names pred xs).
  apply (proj1 (raw_canonical_proof_exact N d names seed (pred,xs) HA)); now exists p.
Qed.

(** Independent proof transport can be composed with the raw least-model
    consumer. The source proof domain is unchanged by this specialization. *)
Definition raw_truth N d names seed :=
  FMS.finite_truth GuardedFiniteCarriers.fin_eq_dec (raw_clauses N d names seed).
Definition raw_truth_predicate {n} N d names seed : Term nat n :=
  S.truth_predicate (raw_truth N d names seed).
Definition raw_reflect {n} N d names seed : Term nat n :=
  S.uniform_reflect (raw_clauses N d names seed) (raw_truth N d names seed).
Theorem raw_truth_model N d names seed :
  FiniteHorn.Model (raw_clauses N d names seed) (fun i => raw_truth N d names seed i = true).
Proof. apply FMS.finite_truth_model. Qed.

Definition decoded_soundness_body {n} N d names seed (q p : Term nat n) :=
  app (app (raw_reflect N d names seed) (app (decoder N d names seed) q))
    (app (app (decode_proof N d names seed) q) p).
Theorem decoded_soundness_body_typed {n} (ctx : Ctx nat n) N d names seed q p :
  @typ nat RankSorts n ctx q (M.code_type N d names seed) ->
  @typ nat RankSorts n ctx p (M.proof_type N d names seed q) ->
  @typ nat RankSorts n ctx (decoded_soundness_body N d names seed q p)
    (app (raw_truth_predicate N d names seed) (app (decoder N d names seed) q)).
Proof.
  intros HQ HP; apply S.arbitrary_query_sound.
  - apply raw_truth_model.
  - apply T.code_map_typed, HQ.
  - exact (arbitrary_query_decode ctx N d names seed q p HQ HP).
Qed.

Definition decoded_soundness_at {n} N d names seed (q : Term nat n) :=
  lam (M.proof_type N d names seed q)
    (decoded_soundness_body N d names seed (shift q) (var fzero)).
Definition decoded_soundness_at_type {n} N d names seed (q : Term nat n) :=
  Π (M.proof_type N d names seed q)
    (app (raw_truth_predicate N d names seed) (app (decoder N d names seed) (shift q))).
Theorem decoded_soundness_at_typed {n} (ctx : Ctx nat n) N d names seed q :
  @typ nat RankSorts n ctx q (M.code_type N d names seed) ->
  @typ nat RankSorts n ctx (decoded_soundness_at N d names seed q)
    (decoded_soundness_at_type N d names seed q).
Proof.
  intro HQ; unfold decoded_soundness_at, decoded_soundness_at_type; eapply typ_λ.
  - now apply M.proof_type_sorted.
  - apply decoded_soundness_body_typed.
    + unfold M.code_type; rewrite <- (@I.code_type_rename
        (Old.atom_count N d names seed) n (Datatypes.S n) fsucc); now apply weakening.
    + change (typ (ctx & I.proof_type (Old.clauses N d names seed) q) (var fzero)
        (I.proof_type (Old.clauses N d names seed) (rename fsucc q))).
      assert (HV : @typ nat RankSorts (Datatypes.S n)
        (ctx & I.proof_type (Old.clauses N d names seed) q) (var fzero)
        (shift (I.proof_type (Old.clauses N d names seed) q))) by constructor.
      change (typ (ctx & I.proof_type (Old.clauses N d names seed) q) (var fzero)
        (rename fsucc (I.proof_type (Old.clauses N d names seed) q))) in HV.
      rewrite I.proof_type_rename in HV; exact HV.
Qed.
Theorem decoded_soundness_at_type_sorted {n} (ctx : Ctx nat n) N d names seed q :
  @typ nat RankSorts n ctx q (M.code_type N d names seed) ->
  @typ nat RankSorts n ctx (decoded_soundness_at_type N d names seed q) (𝓤 4).
Proof.
  intro HQ; unfold decoded_soundness_at_type; eapply typ_Π with (ℓₜ := 3) (ℓᵤ := 1).
  - now apply M.proof_type_sorted.
  - apply S.truth_query_sorted, T.code_map_typed.
    unfold M.code_type; rewrite <- (@I.code_type_rename
      (Old.atom_count N d names seed) n (Datatypes.S n) fsucc); now apply weakening.
  - reflexivity.
Qed.
Definition decoded_soundness {n} N d names seed : Term nat n :=
  lam (M.code_type N d names seed) (decoded_soundness_at N d names seed (var fzero)).
Definition decoded_soundness_type {n} N d names seed : Term nat n :=
  Π (M.code_type N d names seed) (decoded_soundness_at_type N d names seed (var fzero)).
Theorem decoded_soundness_typed {n} (ctx : Ctx nat n) N d names seed :
  @typ nat RankSorts n ctx (decoded_soundness N d names seed)
    (decoded_soundness_type N d names seed).
Proof.
  unfold decoded_soundness, decoded_soundness_type; eapply typ_λ.
  - apply M.code_type_sorted.
  - apply decoded_soundness_at_typed.
    unfold M.code_type; rewrite <- (@I.code_type_rename
      (Old.atom_count N d names seed) n (Datatypes.S n) fsucc).
    change (typ (ctx & I.code_type (Old.atom_count N d names seed)) (var fzero)
      ((ctx & I.code_type (Old.atom_count N d names seed)) !! fzero)); constructor.
Qed.
Theorem decoded_soundness_type_sorted {n} (ctx : Ctx nat n) N d names seed :
  @typ nat RankSorts n ctx (decoded_soundness_type N d names seed) (𝓤 4).
Proof.
  unfold decoded_soundness_type; eapply typ_Π with (ℓₜ := 1) (ℓᵤ := 4).
  - apply M.code_type_sorted.
  - apply decoded_soundness_at_type_sorted.
    unfold M.code_type; rewrite <- (@I.code_type_rename
      (Old.atom_count N d names seed) n (Datatypes.S n) fsucc).
    change (typ (ctx & I.code_type (Old.atom_count N d names seed)) (var fzero)
      ((ctx & I.code_type (Old.atom_count N d names seed)) !! fzero)); constructor.
  - reflexivity.
Qed.

Lemma decoded_soundness_at_type_replace N d names seed m n
  (sigma : Fin m -> Term nat n) q :
  replace sigma (decoded_soundness_at_type N d names seed q) =
  decoded_soundness_at_type N d names seed (replace sigma q).
Proof.
  unfold decoded_soundness_at_type, M.proof_type, raw_truth_predicate, decoder.
  cbn [replace]; rewrite I.proof_type_replace; cbn [replace].
  now rewrite S.truth_predicate_replace, CF.map_replace, CF.replace_shift.
Qed.
Theorem arbitrary_query_decoded_soundness {n} (ctx : Ctx nat n) N d names seed q p :
  @typ nat RankSorts n ctx q (M.code_type N d names seed) ->
  @typ nat RankSorts n ctx p (M.proof_type N d names seed q) ->
  @typ nat RankSorts n ctx (app (app (decoded_soundness N d names seed) q) p)
    (app (raw_truth_predicate N d names seed) (app (decoder N d names seed) q)).
Proof.
  intros HQ HP.
  assert (HT : @typ nat RankSorts n ctx (app (decoded_soundness N d names seed) q)
    (decoded_soundness_at_type N d names seed q)).
  { replace (decoded_soundness_at_type N d names seed q) with
      (subst (decoded_soundness_at_type N d names seed (var fzero)) q).
    - eapply typ_app; [apply decoded_soundness_typed | exact HQ].
    - unfold subst; rewrite decoded_soundness_at_type_replace; reflexivity. }
  replace (app (raw_truth_predicate N d names seed) (app (decoder N d names seed) q)) with
    (subst (app (raw_truth_predicate N d names seed)
      (app (decoder N d names seed) (shift q))) p).
  - eapply typ_app; [exact HT | exact HP].
  - unfold subst, raw_truth_predicate, decoder; cbn [replace].
    rewrite S.truth_predicate_replace, CF.map_replace.
    unfold shift; rewrite replace_rename; cbn [fin_match]; now rewrite replace_var.
Qed.

Print Assumptions observed_supported.
Print Assumptions atom_map_exact.
Print Assumptions atom_map_canonical.
Print Assumptions selected_clause_mapped.
Print Assumptions decoder_typed.
Print Assumptions decoder_type_sorted.
Print Assumptions decoder_selector_beta.
Print Assumptions decoder_canonical_beta.
Print Assumptions raw_code_type_sorted.
Print Assumptions raw_query_code_typed.
Print Assumptions raw_proof_type_sorted.
Print Assumptions decode_proof_typed.
Print Assumptions decode_proof_type_sorted.
Print Assumptions arbitrary_query_decode.
Print Assumptions canonical_query_decode.
Print Assumptions raw_canonical_proof_exact.
Print Assumptions raw_canonical_source_reflection.
Print Assumptions canonical_decoded_source_reflection.
Print Assumptions raw_canonical_no_overflow.
Print Assumptions raw_truth_model.
Print Assumptions decoded_soundness_body_typed.
Print Assumptions decoded_soundness_at_typed.
Print Assumptions decoded_soundness_at_type_sorted.
Print Assumptions decoded_soundness_typed.
Print Assumptions decoded_soundness_type_sorted.
Print Assumptions decoded_soundness_at_type_replace.
Print Assumptions arbitrary_query_decoded_soundness.
End MM0InternalDecoder.
