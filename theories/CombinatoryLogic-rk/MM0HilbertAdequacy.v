From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks AbstractRewriting Reduction DefEq.
From PTSrk.Combinatory Require Import Hilbert CatalogueEconomy NativeCanonicity
  MM0FiniteSignature MM0FiniteAxioms MM0SyntaxSoundness MM0NativeSyntax
  MM0ComputationalAdequacy MM0NativeReduction MM0CatalogueAdequacy MM0CatalogueRealization
  MM0GuardedQuantification MM0GuardedSyntaxAlgebra MM0GuardedReflection.
Import ListNotations.

(** Literal PH derivations reconstruct closed native Hilbert derivations.
    The resulting Void exclusion uses the existing external native canonicity
    theorem. It is not an internal PTS consistency proof. *)
Module MM0HilbertAdequacy.
Import MM0FiniteSignature MM0FiniteAxioms MM0SyntaxSoundness MM0NativeSyntax
  MM0ComputationalAdequacy MM0NativeReduction MM0CatalogueAdequacy.
Module C := CatalogueEconomy.
Module G := MM0GuardedQuantification.MM0GuardedQuantification.
Module A := MM0GuardedSyntaxAlgebra.MM0GuardedSyntaxAlgebra.
Module R := MM0GuardedReflection.MM0GuardedReflection.

Definition NativeMeaning (a : Atom) : Prop :=
  match a with
  | (PH, [M;T]) => exists m t : Term nat 0,
      M = quote_term m /\ T = quote_term t /\ C.Derives m t
  | _ => True
  end.

Lemma catalogue_derivations_sound names ps (p : Derivations names ps) :
  Forall CatalogueMeaning ps.
Proof. induction p; constructor; auto; now apply (source_catalogue_sound _ _ d). Qed.

Local Ltac unfold_source :=
  cbn [axiom_rule variables premises conclusion substitute_atom substitute
    aLe aLt aMax aLift aSub aRed aStel aPrefix aForm aAx aH
    MM0FiniteAxioms.MM0FiniteAxioms.x0 MM0FiniteAxioms.MM0FiniteAxioms.x1
    MM0FiniteAxioms.MM0FiniteAxioms.x2 MM0FiniteAxioms.MM0FiniteAxioms.x3
    MM0FiniteAxioms.MM0FiniteAxioms.x4 MM0FiniteAxioms.MM0FiniteAxioms.x5
    MM0FiniteAxioms.MM0FiniteAxioms.x6 MM0FiniteAxioms.MM0FiniteAxioms.x7
    MM0FiniteAxioms.MM0FiniteAxioms.x8 MM0FiniteAxioms.MM0FiniteAxioms.x9
    NativeMeaning CatalogueMeaning Meaning map fst snd number] in *.

Lemma native_axiom_sound name sigma :
  ClosedSubstitution (variables (axiom_rule name)) sigma ->
  Forall Meaning (map (substitute_atom sigma) (premises (axiom_rule name))) ->
  Forall CatalogueMeaning (map (substitute_atom sigma) (premises (axiom_rule name))) ->
  Forall NativeMeaning (map (substitute_atom sigma) (premises (axiom_rule name))) ->
  NativeMeaning (substitute_atom sigma (conclusion (axiom_rule name))).
Proof.
  intros HS HP HC HN; destruct name; unfold_source; try exact I;
    repeat match goal with H : Forall _ (_ :: _) |- _ =>
      inversion H; subst; clear H end; unfold_source.
  - destruct (ground_nat_no_junk (sigma 0) (HS 0 NAT eq_refl)) as [r Er].
    exists (𝓤 r), (𝓤 0); split; [cbn; now rewrite Er |].
    split; [reflexivity | apply Hilbert.derive_universe].
  - match goal with H : exists row, evaluate_row row = Some _ |- _ =>
      destruct H as [row Hrow];
      destruct (row_has_native_catalogue row _ _ Hrow) as [l [EM ET]] end.
    exists (C.subject l), (C.declared_type l); repeat split; auto; apply Hilbert.derive_scheme.
  - match goal with H : exists m t, sigma 0 = _ /\ EPi _ _ = _ /\ _ |- _ =>
      destruct H as [f [FT [Ef [EFT DF]]]] end.
    destruct (quote_pi_inv 0 FT _ _ EFT) as [AT [BT [EFT' [EA EB]]]]; subst FT.
    match goal with H : exists m t, sigma 1 = _ /\ sigma 2 = _ /\ _ |- _ =>
      destruct H as [x [XT [Ex [EXT DX]]]] end.
    assert (XT = AT) by (apply quote_term_injective; congruence); subst XT.
    exists (app f x), (subst BT x); split; [cbn; now rewrite Ef, Ex |].
    split; [| eapply Hilbert.derive_apply; eassumption].
    rewrite quote_subst; congruence.
  - match goal with H : exists m t, sigma 0 = _ /\ sigma 1 = _ /\ _ |- _ =>
      destruct H as [m [AT [EM [EA DM]]]] end.
    match goal with H : exists m t, sigma 2 = _ /\ EU _ = _ /\ _ |- _ =>
      destruct H as [BT [UT [EB [EU DB]]]] end.
    destruct (ground_nat_no_junk (sigma 4) (HS 4 NAT eq_refl)) as [r Er].
    assert (UT = 𝓤 r) by (apply quote_term_injective; cbn; congruence); subst UT.
    exists m, BT; repeat split; auto.
    eapply Hilbert.derive_convert; [exact DM | exact DB |].
    apply raw_conversion_exact; exists (sigma 3); split; congruence.
  - match goal with H : exists m t, sigma 0 = _ /\ sigma 2 = _ /\ _ |- _ =>
      destruct H as [m [AT [EM [EA DM]]]] end.
    match goal with H : RawReduction (sigma 0) (sigma 1) |- _ =>
      destruct (raw_reduction_reconstruct _ _ H 0 m EM) as [m' [EN HR]] end.
    exists m', AT; repeat split; auto.
    eapply Hilbert.derive_subject_reduction; eassumption.
  - match goal with H : exists m t, sigma 0 = _ /\ sigma 1 = _ /\ _ |- _ =>
      destruct H as [m [AT [EM [EA DM]]]] end.
    match goal with H : RawReduction (sigma 1) (sigma 2) |- _ =>
      destruct (raw_reduction_reconstruct _ _ H 0 AT EA) as [BT [EB HR]] end.
    exists m, BT; repeat split; auto.
    eapply Hilbert.derive_type_reduction; eassumption.
Qed.

Theorem source_native_meaning names a (p : Derivation names a) : NativeMeaning a.
Proof.
  induction p using Derivation_ind' with (P0 := fun ps _ => Forall NativeMeaning ps).
  - apply native_axiom_sound; auto.
    + exact (computational_derivations_sound _ _ d).
    + exact (catalogue_derivations_sound _ _ d).
  - constructor.
  - constructor; assumption.
Qed.
Theorem source_hilbert_reconstruct names M T (p : Derivation names (aH M T)) :
  exists m t : Term nat 0, M = quote_term m /\ T = quote_term t /\ C.Derives m t.
Proof. exact (source_native_meaning _ _ p). Qed.
Theorem source_hilbert_sound names (M T : Term nat 0)
  (p : Derivation names (aH (quote_term M) (quote_term T))) : C.Derives M T.
Proof.
  destruct (source_hilbert_reconstruct _ _ _ p) as [m [t [EM [ET H]]]].
  apply quote_term_injective in EM, ET; now subst.
Qed.
Theorem source_original_typing names M T (p : Derivation names (aH M T)) :
  exists m t : Term nat 0, M = quote_term m /\ T = quote_term t /\
    @typ nat RankSorts 0 ε m t.
Proof.
  destruct (source_hilbert_reconstruct _ _ _ p) as [m [t [EM [ET H]]]].
  exists m, t; repeat split; auto; now apply C.derives_sound.
Qed.

Local Ltac sorted_quotes :=
  repeat first [apply quote_term_sorted | apply quote_nat_sorted | constructor].

Theorem catalogue_source_hilbert M T : C.Derives M T ->
  inhabited (Derivation all_axioms (aH (quote_term M) (quote_term T))).
Proof.
  intro H; induction H.
  - apply (source_rule A_h_universe [quote_nat i]); sorted_quotes.
  - apply (source_rule A_h_scheme [quote_term (C.subject l); quote_term (C.declared_type l)]).
    + sorted_quotes.
    + constructor; [apply MM0CatalogueRealization.catalogue_source_realization | constructor].
  - apply (source_rule A_h_apply
      [quote_term f; quote_term x; quote_term A; quote_term B; quote_term (subst B x)]).
    + sorted_quotes.
    + constructor; [exact IHDerives1 |]. constructor; [exact IHDerives2 |].
      constructor; [apply (proj2 (literal_substitution_exact _ _ _ _)); reflexivity | constructor].
  - apply def_equiv_prop in H1 as [u [HA HB]].
    apply (source_rule A_h_convert
      [quote_term M; quote_term A; quote_term B; quote_term u; quote_nat r]).
    + sorted_quotes.
    + constructor; [exact IHDerives1 |]. constructor; [exact IHDerives2 |].
      constructor; [apply (proj2 (literal_reduction_exact _ _ _)), HA |].
      constructor; [apply (proj2 (literal_reduction_exact _ _ _)), HB | constructor].
  - apply (source_rule A_h_subject [quote_term M; quote_term N; quote_term A]).
    + sorted_quotes.
    + constructor; [exact IHDerives |].
      constructor; [apply (proj2 (literal_reduction_exact _ _ _)), H0 | constructor].
  - apply (source_rule A_h_type [quote_term M; quote_term A; quote_term B]).
    + sorted_quotes.
    + constructor; [exact IHDerives |].
      constructor; [apply (proj2 (literal_reduction_exact _ _ _)), H0 | constructor].
Qed.
Theorem source_hilbert_exact (M T : Term nat 0) :
  inhabited (Derivation all_axioms (aH (quote_term M) (quote_term T))) <-> C.Derives M T.
Proof. split; [intros [p]; exact (source_hilbert_sound _ _ _ p) | apply catalogue_source_hilbert]. Qed.
Theorem literal_finite_union_exact (M T : Term nat 0) : C.Derives M T <->
  exists N d,
    R.query N d all_axioms
      (evaluate_atom None (A.algebra N d) [] (aH (quote_term M) (quote_term T))) = true /\
    R.decoded_atom N d
      (evaluate_atom None (A.algebra N d) [] (aH (quote_term M) (quote_term T))) =
      aH (quote_term M) (quote_term T).
Proof. rewrite <- source_hilbert_exact; apply R.source_union_exact. Qed.

Theorem source_void_excluded names : R.SourceVoidExcluded names.
Proof.
  intros e [p].
  destruct (source_hilbert_reconstruct _ _ _ p) as [m [t [EM [ET H]]]].
  assert (t = NativeCanonicity.Void).
  { apply quote_term_injective; symmetry; exact ET. }
  subst t; apply (NativeCanonicity.void_empty m), C.derives_sound, H.
Qed.
Theorem guarded_model_exists N d names : 5 <= N -> 3 <= d ->
  G.GuardedModel None (A.algebra N d) (A.guard N d) (selected_rules names)
    [void_denial] (R.SourceTruth N d names).
Proof. intros; apply R.source_truth_consistent_model; auto using source_void_excluded. Qed.
Theorem guarded_checker_accepts N d names : 5 <= N -> 3 <= d -> A.checker N d names = true.
Proof. intros; apply R.source_exclusion_accepts_candidate; auto using source_void_excluded. Qed.
Theorem guarded_certificate_typed N d names : 5 <= N -> 3 <= d ->
  @typ nat RankSorts 0 ε (A.certificate N d names) (A.certificate_type N d names).
Proof. intros; apply R.source_exclusion_realizes_certificate; auto using source_void_excluded. Qed.
Theorem guarded_certificate_rank N d names : A.certificate_rank N d names <= 4.
Proof. apply A.certificate_rank_bound. Qed.
Theorem guarded_every_void_query_false N d names x : 5 <= N -> 3 <= d ->
  R.query N d names (PH, [x; void_value None (A.algebra N d)]) = false.
Proof. intros; apply R.source_exclusion_void_query_false; auto using source_void_excluded. Qed.

Definition universe_zero_source names (HN : In A_h_universe names) :
  Derivation names (aH (EU EZ) (EU EZ)).
Proof.
  change (Derivation names (substitute_atom (fun _ => EZ)
    (conclusion (axiom_rule A_h_universe)))).
  apply use_axiom; [exact HN | | constructor].
  intros [|i] s H; cbn in H.
  - inversion H; constructor.
  - destruct i; discriminate.
Defined.
Definition universe_zero_fragment N d names (HN : In A_h_universe names)
  (HS : 2 <= N) (HD : 2 <= d) : G.GuardedDerivation names N d 1 (aH (EU EZ) (EU EZ)).
Proof.
  exists (universe_zero_source names HN); split.
  - unfold G.Bounds; cbn [universe_zero_source G.derivation_expressions
      G.derivations_expressions G.instance_expressions axiom_rule variables
      conclusion premises aH substitute_atom substitute].
    repeat constructor; cbn; lia.
  - cbn [universe_zero_source G.derivation_height G.derivations_height]; lia.
Defined.
Theorem guarded_universe_query_true N d names :
  In A_h_universe names -> 2 <= N -> 2 <= d ->
  R.query N d names (evaluate_atom None (A.algebra N d) [] (aH (EU EZ) (EU EZ))) = true.
Proof.
  intros HN HS HD; exact (R.guarded_source_query N d names _ 1
    (universe_zero_fragment N d names HN HS HD)).
Qed.
Theorem guarded_model_nonempty N d names :
  In A_h_universe names -> 2 <= N -> 2 <= d ->
  R.SourceTruth N d names (evaluate_atom None (A.algebra N d) [] (aH (EU EZ) (EU EZ))).
Proof.
  intros HN HS HD; apply R.accepted_query_reflects, guarded_universe_query_true; assumption.
Qed.
Theorem all55_guarded_model N d : 5 <= N -> 3 <= d ->
  G.GuardedModel None (A.algebra N d) (A.guard N d) (selected_rules all_axioms)
    [void_denial] (R.SourceTruth N d all_axioms) /\
  R.SourceTruth N d all_axioms
    (evaluate_atom None (A.algebra N d) [] (aH (EU EZ) (EU EZ))).
Proof.
  intros HS HD; split; [now apply guarded_model_exists |].
  apply guarded_model_nonempty; [apply all_axioms_complete | lia | lia].
Qed.

(** Coverage by genuinely accepted finite models, not merely by positive
    query tables at bounds too small to represent Void. *)
Theorem consistent_finite_union_exact (M T : Term nat 0) : C.Derives M T <->
  exists N d, 5 <= N /\ 3 <= d /\ A.checker N d all_axioms = true /\
    R.query N d all_axioms
      (evaluate_atom None (A.algebra N d) [] (aH (quote_term M) (quote_term T))) = true /\
    R.decoded_atom N d
      (evaluate_atom None (A.algebra N d) [] (aH (quote_term M) (quote_term T))) =
      aH (quote_term M) (quote_term T).
Proof.
  split.
  - intro H; destruct (catalogue_source_hilbert M T H) as [p].
    set (a := aH (quote_term M) (quote_term T)).
    set (N := Nat.max 5 (G.source_size_budget all_axioms a p)).
    set (d := Nat.max 3 (G.source_depth_budget all_axioms a p)).
    assert (HN : 5 <= N) by (unfold N; lia).
    assert (HD : 3 <= d) by (unfold d; lia).
    assert (gp : G.GuardedDerivation all_axioms N d
      (G.derivation_height all_axioms a p) a).
    { eapply G.guarded_derivation_monotone.
      - unfold N; apply Nat.le_max_r.
      - unfold d; apply Nat.le_max_r.
      - reflexivity.
      - apply G.every_source_derivation_covered. }
    exists N, d; split; [exact HN |]. split; [exact HD |].
    split; [now apply guarded_checker_accepts |].
    split; [exact (R.guarded_source_query _ _ _ _ _ gp) |
      exact (R.guarded_source_decoding _ _ _ _ _ gp)].
  - intros [N [d [HN [HD [HC [HQ HE]]]]]].
    apply literal_finite_union_exact; exists N, d; auto.
Qed.

End MM0HilbertAdequacy.

Print Assumptions MM0HilbertAdequacy.catalogue_derivations_sound.
Print Assumptions MM0HilbertAdequacy.native_axiom_sound.
Print Assumptions MM0HilbertAdequacy.source_native_meaning.
Print Assumptions MM0HilbertAdequacy.source_hilbert_reconstruct.
Print Assumptions MM0HilbertAdequacy.source_hilbert_sound.
Print Assumptions MM0HilbertAdequacy.source_original_typing.
Print Assumptions MM0HilbertAdequacy.catalogue_source_hilbert.
Print Assumptions MM0HilbertAdequacy.source_hilbert_exact.
Print Assumptions MM0HilbertAdequacy.literal_finite_union_exact.
Print Assumptions MM0HilbertAdequacy.source_void_excluded.
Print Assumptions MM0HilbertAdequacy.guarded_model_exists.
Print Assumptions MM0HilbertAdequacy.guarded_checker_accepts.
Print Assumptions MM0HilbertAdequacy.guarded_certificate_typed.
Print Assumptions MM0HilbertAdequacy.guarded_certificate_rank.
Print Assumptions MM0HilbertAdequacy.guarded_every_void_query_false.
Print Assumptions MM0HilbertAdequacy.universe_zero_source.
Print Assumptions MM0HilbertAdequacy.universe_zero_fragment.
Print Assumptions MM0HilbertAdequacy.guarded_universe_query_true.
Print Assumptions MM0HilbertAdequacy.guarded_model_nonempty.
Print Assumptions MM0HilbertAdequacy.all55_guarded_model.
Print Assumptions MM0HilbertAdequacy.consistent_finite_union_exact.
