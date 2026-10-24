From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks Reduction AbstractRewriting Congruence.
From PTSrk.Combinatory Require Import GroundHorn FiniteHorn FiniteNormalForms
  ChurchFinite FiniteHornChurch GuardedFiniteCarriers GuardedFiniteSupport
  MM0FiniteSignature MM0FiniteAxioms MM0SyntaxSoundness MM0GuardedQuantification MM0GuardProvenance
  HornProofRealization IndexedHornEncoding IndexedHornRealization
  IndexedHornTransport FiniteGeneratedCodes FiniteMapCoherence.
Import ListNotations.

(** Fixed-budget raw guard evaluation with an independent graph specification.
    Input positions carry a selected axiom and its whole raw valuation tuple.
    None is a distinguished rejected sentinel, not a source instance. The
    graph has exactly one fact per input and does not mention native typing.
    Internal graph correctness consumes independent finite-generation evidence;
    it does not assume that arbitrary bare Church terms have dependent cases. *)
Module MM0InternalGuard.
Import MM0FiniteSignature MM0FiniteAxioms.
Module P := MM0GuardProvenance.MM0GuardProvenance.
Module B := MM0GuardedQuantification.MM0GuardedQuantification.
Module C := GuardedFiniteCarriers.GuardedFiniteCarriers.
Module F := GuardedFiniteSupport.GuardedFiniteSupport.
Module V := FiniteNormalForms.FiniteNormalForms.
Module CF := ChurchFinite.ChurchFinite.
Module BoolCode := FiniteHornChurch.FiniteHornChurch.
Module H := HornProofRealization.HornProofRealization.
Module I := IndexedHornEncoding.IndexedHornEncoding.
Module IR := IndexedHornRealization.IndexedHornRealization.
Module T := IndexedHornTransport.IndexedHornTransport.
Module G := FiniteGeneratedCodes.FiniteGeneratedCodes.
Module Eq := FiniteMapCoherence.FiniteMapCoherence.

Definition entries N d names := None :: map Some (P.raw_entries N d names).
Definition count N d names := length (entries N d names).
Definition entry N d names := C.lookup (entries N d names).
Definition answer N d names (i : Fin (count N d names)) :=
  match entry N d names i with
  | None => false
  | Some (name,env) => P.raw_guard N d (axiom_rule name) env
  end.

Theorem entry_present N d names i : entry N d names i = None \/
  exists name env, entry N d names i = Some (name,env) /\
    In (name,env) (P.raw_entries N d names).
Proof.
  pose proof (C.lookup_member _ (entries N d names) i) as HE.
  change (In (entry N d names i) (entries N d names)) in HE.
  unfold entries in HE; destruct HE as [HE|HE]; [left; symmetry; exact HE|right].
  apply in_map_iff in HE as [[name env] [HE HI]].
  exists name,env; split; [symmetry; exact HE|exact HI].
Qed.
Theorem accepted_entry_provenance N d names i : answer N d names i = true ->
  exists name env, entry N d names i = Some (name,env) /\ In name names /\
    In env (P.tuples (P.observations N d) (length (variables (axiom_rule name)))) /\
    P.raw_guard N d (axiom_rule name) env = true /\
    MM0SyntaxSoundness.ClosedSubstitution (variables (axiom_rule name))
      (P.raw_substitution env) /\
    B.Bounds N d (B.instance_expressions (axiom_rule name) (P.raw_substitution env)).
Proof.
  intro HA; destruct (entry_present N d names i) as [HE|[name [env [HE HI]]]].
  - unfold answer in HA; rewrite HE in HA; discriminate.
  - unfold answer in HA; rewrite HE in HA.
    apply P.raw_entry_exact in HI as [HN HV].
    destruct (P.active_source_substitution N d name env HA) as [HS HB].
    exists name,env; repeat split; assumption.
Qed.
Theorem rejected_entry_inert N d names i : answer N d names i = false ->
  entry N d names i = None \/ exists name env,
    entry N d names i = Some (name,env) /\
    fst (P.raw_instance N d name env) = [snd (P.raw_instance N d name env)].
Proof.
  intro HA; destruct (entry_present N d names i) as [HE|[name [env [HE HI]]]]; [now left|].
  right; exists name,env; split; [exact HE|].
  unfold answer in HA; rewrite HE in HA.
  now rewrite P.inactive_instance_tautological by exact HA.
Qed.

Definition Atom N d names := (Fin (count N d names) * bool)%type.
Definition atom_eq_dec N d names (x y : Atom N d names) : {x=y}+{x<>y}.
Proof. decide equality; [apply Bool.bool_dec|apply H.index_eq_dec]. Defined.
Definition graph N d names : list (list (Atom N d names) * Atom N d names) :=
  map (fun i => ([],(i,answer N d names i))) (V.variables (count N d names)).
Definition reserve N d names :=
  map (fun i => [(i,true);(i,false)]) (V.variables (count N d names)).
Definition anchor N d names : Atom N d names := (fzero,false).
Definition graph_count N d names := F.cardinality
  (graph N d names) (reserve N d names) (anchor N d names).
Definition graph_index N d names := F.index (atom_eq_dec N d names)
  (graph N d names) (reserve N d names) (anchor N d names).
Definition graph_reify N d names := F.reify
  (graph N d names) (reserve N d names) (anchor N d names).
Definition graph_clauses N d names := F.indexed_clauses (atom_eq_dec N d names)
  (graph N d names) (reserve N d names) (anchor N d names).
Definition graph_map N d names (i : Fin (count N d names)) :=
  graph_index N d names (i,answer N d names i).
Definition input_map N d names (j : Fin (graph_count N d names)) :=
  fst (graph_reify N d names j).
Definition boolean_map N d names (j : Fin (graph_count N d names)) :=
  BoolCode.boolean_index (snd (graph_reify N d names j)).

Theorem every_graph_atom_supported N d names a :
  In a (F.support (graph N d names) (reserve N d names) (anchor N d names)).
Proof.
  destruct a as [i b]; unfold F.support,F.support_tail; right.
  apply in_app_iff; right; apply in_concat.
  exists [(i,true);(i,false)]; split.
  - apply in_map_iff; exists i; split; [reflexivity|apply V.variables_complete].
  - destruct b; cbn; auto.
Qed.
Theorem graph_map_exact N d names i :
  graph_reify N d names (graph_map N d names i) = (i,answer N d names i).
Proof. apply F.reify_index, every_graph_atom_supported. Qed.
Theorem input_map_retract N d names i : input_map N d names (graph_map N d names i) = i.
Proof. unfold input_map; now rewrite graph_map_exact. Qed.
Theorem boolean_map_exact N d names i :
  boolean_map N d names (graph_map N d names i) = BoolCode.boolean_index (answer N d names i).
Proof. unfold boolean_map; now rewrite graph_map_exact. Qed.

Theorem graph_model N d names :
  FiniteHorn.Model (graph N d names) (fun a => snd a = answer N d names (fst a)).
Proof.
  intros ps a HC _; apply in_map_iff in HC as [i [HE _]].
  injection HE as <- <-; reflexivity.
Qed.
Theorem graph_derivable_exact N d names i b :
  FiniteHorn.Derives (graph N d names) (i,b) <-> b = answer N d names i.
Proof.
  split.
  - intro HD; exact (GroundHorn.derivation_sound _ _ HD _ (graph_model N d names)).
  - intro HE; subst b; eapply GroundHorn.by_rule with (premises := []).
    + apply in_map_iff; exists i; split; [reflexivity|apply V.variables_complete].
    + constructor.
Qed.
Theorem graph_clause_mapped N d names :
  T.maps_into (graph_map N d names) (G.facts (count N d names)) (graph_clauses N d names).
Proof.
  intros ps a HC; unfold G.facts,G.facts_on in HC.
  apply in_map_iff in HC as [i [HE HI]]; injection HE as <- <-.
  unfold graph_clauses,F.indexed_clauses; cbn [map].
  apply (in_map (F.map_clause (graph_index N d names)) (graph N d names)
    ([],(i,answer N d names i))).
  apply in_map_iff; exists i; split; [reflexivity|apply V.variables_complete].
Qed.

Definition graph_program {n} N d names : Term nat n := T.code_map (graph_map N d names).
Definition graph_proof_type {n} N d names q : Term nat n := I.proof_type (graph_clauses N d names) q.
Definition graph_certificate {n} N d names : Term nat n :=
  T.uniform_transport (graph_map N d names) (G.facts (count N d names)) (graph_clauses N d names).
Definition graph_certificate_type {n} N d names : Term nat n :=
  T.uniform_transport_type (graph_map N d names) (G.facts (count N d names)) (graph_clauses N d names).

Theorem graph_program_typed {n} (ctx : Ctx nat n) N d names :
  @typ nat RankSorts n ctx (graph_program N d names)
    (CF.map_type 0 (count N d names) (graph_count N d names)).
Proof. apply CF.map_typed. Qed.
Theorem graph_program_beta {n} N d names i :
  reduces_to nat n (app (graph_program N d names) (CF.selector 0 (count N d names) i))
    (CF.selector 0 (graph_count N d names) (graph_map N d names i)).
Proof. apply CF.map_selector_beta. Qed.
Theorem graph_certificate_typed {n} (ctx : Ctx nat n) N d names :
  @typ nat RankSorts n ctx (graph_certificate N d names) (graph_certificate_type N d names).
Proof. apply T.uniform_transport_typed, graph_clause_mapped. Qed.
Theorem graph_certificate_rank {n} (ctx : Ctx nat n) N d names :
  @typ nat RankSorts n ctx (graph_certificate_type N d names) (𝓤 4).
Proof. apply T.uniform_transport_type_sorted. Qed.
Theorem arbitrary_generated_graph {n} (ctx : Ctx nat n) N d names q p :
  @typ nat RankSorts n ctx q (I.code_type (count N d names)) ->
  @typ nat RankSorts n ctx p (G.generated (count N d names) 1 q) ->
  @typ nat RankSorts n ctx (app (app (graph_certificate N d names) q) p)
    (graph_proof_type N d names (app (graph_program N d names) q)).
Proof. intros HQ HP; apply T.arbitrary_query_transport; [apply graph_clause_mapped|exact HQ|exact HP]. Qed.
Theorem canonical_graph_exact N d names i b :
  (exists p, @typ nat RankSorts 0 ε p (graph_proof_type N d names
    (CF.selector 0 (graph_count N d names) (graph_index N d names (i,b))))) <->
  b = answer N d names i.
Proof.
  unfold graph_proof_type; rewrite IR.proof_inhabited_exact.
  unfold graph_clauses,graph_index.
  rewrite (F.indexed_derivation_exact (atom_eq_dec N d names)
    (graph N d names) (reserve N d names) (anchor N d names) (i,b)
    (every_graph_atom_supported N d names (i,b))).
  apply graph_derivable_exact.
Qed.

Definition guard_program {n} N d names : Term nat n :=
  lam (I.code_type (count N d names))
    (app (T.code_map (boolean_map N d names))
      (app (graph_program N d names) (var fzero))).
Theorem guard_program_typed {n} (ctx : Ctx nat n) N d names :
  @typ nat RankSorts n ctx (guard_program N d names) (CF.map_type 0 (count N d names) 2).
Proof.
  unfold guard_program,CF.map_type; eapply typ_λ; [apply I.code_type_sorted|].
  apply T.code_map_typed, T.code_map_typed.
  rewrite <- (@I.code_type_rename (count N d names) n (S n) fsucc).
  change (typ (ctx & I.code_type (count N d names)) (var fzero)
    ((ctx & I.code_type (count N d names)) !! fzero)); constructor.
Qed.
Theorem guard_program_beta {n} N d names i :
  reduces_to nat n (app (guard_program N d names) (CF.selector 0 (count N d names) i))
    (BoolCode.boolean 0 (answer N d names i)).
Proof.
  unfold guard_program; eapply rtc_step; [apply step_beta|].
  unfold subst; cbn [replace fin_match]; unfold graph_program; rewrite !T.code_map_replace.
  eapply rtc_trans.
  - apply (@app_cong_r nat (reduces_to nat) _); apply CF.map_selector_beta.
  - unfold BoolCode.boolean; rewrite <- boolean_map_exact; apply CF.map_selector_beta.
Qed.
Theorem guard_program_output_exact {n} N d names i b :
  reduces_to nat n (app (guard_program N d names) (CF.selector 0 (count N d names) i))
    (BoolCode.boolean 0 b) <-> b = answer N d names i.
Proof.
  split.
  - intro HB; apply (@BoolCode.boolean_injective n 0).
    eapply BoolCode.normal_outputs_equal; [exact HB|apply guard_program_beta| |];
      apply BoolCode.boolean_normal.
  - intros ->; apply guard_program_beta.
Qed.

(** Graph correctness alone does not identify the first projection with an
    arbitrary input. These are separate INTERNAL Leibniz equalities. Their
    independent generation evidence eliminates into rank-three equality;
    no bare-code exhaustiveness or higher-rank cumulativity is assumed. *)
Definition input_certificate {n} N d names : Term nat n :=
  Eq.retraction (graph_map N d names) (input_map N d names).
Definition input_certificate_type {n} N d names : Term nat n :=
  Eq.uniform_coherence_type
    (Eq.compose (Eq.table (graph_map N d names)) (Eq.table (input_map N d names)))
    (Eq.identity (count N d names)).
Theorem input_certificate_typed {n} (ctx : Ctx nat n) N d names :
  @typ nat RankSorts n ctx (input_certificate N d names) (input_certificate_type N d names).
Proof. apply Eq.retraction_typed, input_map_retract. Qed.
Theorem input_certificate_rank {n} (ctx : Ctx nat n) N d names :
  @typ nat RankSorts n ctx (input_certificate_type N d names) (𝓤 5).
Proof. apply Eq.uniform_coherence_type_sorted. Qed.
Theorem arbitrary_input_preserved {n} (ctx : Ctx nat n) N d names q e :
  @typ nat RankSorts n ctx q (I.code_type (count N d names)) ->
  @typ nat RankSorts n ctx e (G.generated (count N d names) 3 q) ->
  @typ nat RankSorts n ctx (app (app (input_certificate N d names) q) e)
    (Eq.equality (count N d names)
      (app (T.code_map (input_map N d names)) (app (graph_program N d names) q)) q).
Proof. intros HQ HE; apply Eq.arbitrary_retraction; [apply input_map_retract|exact HQ|exact HE]. Qed.

Definition boolean_certificate {n} N d names : Term nat n :=
  Eq.composition (graph_map N d names) (boolean_map N d names)
    (fun i => BoolCode.boolean_index (answer N d names i)).
Definition boolean_certificate_type {n} N d names : Term nat n :=
  Eq.uniform_coherence_type
    (Eq.compose (Eq.table (graph_map N d names)) (Eq.table (boolean_map N d names)))
    (Eq.table (fun i => BoolCode.boolean_index (answer N d names i))).
Theorem boolean_certificate_typed {n} (ctx : Ctx nat n) N d names :
  @typ nat RankSorts n ctx (boolean_certificate N d names) (boolean_certificate_type N d names).
Proof. apply Eq.composition_typed, boolean_map_exact. Qed.
Theorem boolean_certificate_rank {n} (ctx : Ctx nat n) N d names :
  @typ nat RankSorts n ctx (boolean_certificate_type N d names) (𝓤 5).
Proof. apply Eq.uniform_coherence_type_sorted. Qed.
Theorem arbitrary_boolean_preserved {n} (ctx : Ctx nat n) N d names q e :
  @typ nat RankSorts n ctx q (I.code_type (count N d names)) ->
  @typ nat RankSorts n ctx e (G.generated (count N d names) 3 q) ->
  @typ nat RankSorts n ctx (app (app (boolean_certificate N d names) q) e)
    (Eq.equality 2
      (app (T.code_map (boolean_map N d names)) (app (graph_program N d names) q))
      (app (BoolCode.compile_predicate 0 (count N d names) (answer N d names)) q)).
Proof. intros HQ HE; apply Eq.arbitrary_composition; [apply boolean_map_exact|exact HQ|exact HE]. Qed.

Theorem accepted_graph_source N d names i p :
  @typ nat RankSorts 0 ε p (graph_proof_type N d names
    (CF.selector 0 (graph_count N d names) (graph_index N d names (i,true)))) ->
  exists name env, entry N d names i = Some (name,env) /\ In name names /\
    In env (P.tuples (P.observations N d) (length (variables (axiom_rule name)))) /\
    P.raw_guard N d (axiom_rule name) env = true /\
    MM0SyntaxSoundness.ClosedSubstitution (variables (axiom_rule name))
      (P.raw_substitution env) /\
    B.Bounds N d (B.instance_expressions (axiom_rule name) (P.raw_substitution env)).
Proof.
  intro HP; apply accepted_entry_provenance; symmetry.
  apply (proj1 (canonical_graph_exact N d names i true)); now exists p.
Qed.
Theorem wrong_boolean_uninhabited N d names i :
  ~ exists p, @typ nat RankSorts 0 ε p (graph_proof_type N d names
    (CF.selector 0 (graph_count N d names)
      (graph_index N d names (i,negb (answer N d names i))))).
Proof.
  intro HP; apply canonical_graph_exact in HP; destruct (answer N d names i); discriminate.
Qed.
Example sentinel_rejected N d names : answer N d names fzero = false.
Proof. reflexivity. Qed.

Print Assumptions entry_present.
Print Assumptions accepted_entry_provenance.
Print Assumptions rejected_entry_inert.
Print Assumptions every_graph_atom_supported.
Print Assumptions graph_map_exact.
Print Assumptions input_map_retract.
Print Assumptions boolean_map_exact.
Print Assumptions graph_model.
Print Assumptions graph_derivable_exact.
Print Assumptions graph_clause_mapped.
Print Assumptions graph_program_typed.
Print Assumptions graph_program_beta.
Print Assumptions graph_certificate_typed.
Print Assumptions graph_certificate_rank.
Print Assumptions arbitrary_generated_graph.
Print Assumptions canonical_graph_exact.
Print Assumptions guard_program_typed.
Print Assumptions guard_program_beta.
Print Assumptions guard_program_output_exact.
Print Assumptions input_certificate_typed.
Print Assumptions input_certificate_rank.
Print Assumptions arbitrary_input_preserved.
Print Assumptions boolean_certificate_typed.
Print Assumptions boolean_certificate_rank.
Print Assumptions arbitrary_boolean_preserved.
Print Assumptions accepted_graph_source.
Print Assumptions wrong_boolean_uninhabited.
Print Assumptions sentinel_rejected.
End MM0InternalGuard.
