(** Soundness for the ORIGINAL annotated PTS, with semantic conversion
    proved rather than assumed. Set-theoretic construction parameters remain
    explicit. Internal derivability in material BZC is a separate open audit
    of this same construction, not a premise disguised as a proved theorem. *)
From ZFC Require Import Sets Axioms.
From PTSrk Require Import Syntax Context Typing Ranks DefEq Preservation.
From PTSrkModel Require Import SetFunctions SetBijections CodeUniverses CountableCodes
  CardinalHierarchy HierarchyBounds SuppliedHierarchy CardinalClassification
  CountableDichotomy GlobalOperations Denotation InterpretedContexts
  RealizationInduction RankedNormalization.
Import CodeUniverses.CodeUniverses.

Module ModelSoundness.
Module RN := RankedNormalization.RankedNormalization.

Definition bottom {n} : Term nat n := Π (𝓤 0) (var fzero).
Definition bottom_code H s := semantic_product H s (repr (sort 0)) (fun x => x).

Lemma bottom_typed n (G : Ctx nat n) : @typ nat RankSorts n G bottom (𝓤 1).
Proof.
  unfold bottom; eapply typ_Π with (ℓₜ := 0) (ℓᵤ := 0).
  - apply typ_𝓤; reflexivity.
  - change (@typ nat RankSorts _ (G & 𝓤 0) (var fzero) ((G & 𝓤 0) !! fzero)).
    apply typ_var.
  - reflexivity.
Qed.

Lemma bottom_denotes H s n (G : Ctx nat n) rho :
  denotes H s n G rho bottom (bottom_code H s).
Proof.
  unfold bottom, bottom_code; eapply denotes_product.
  - apply denotes_sort.
  - intros x Hx; apply denotes_var.
  - intros x y E; apply decoding_extensional; exact E.
Qed.

Section Soundness.
Variables W H s : Ens.
Hypothesis HW : transitive_set W.
Hypothesis HO : INC omega_codes W.
Hypothesis HH : tower_envelope W H.
Variable classical_logic : forall P : Prop, P \/ ~ P.
Hypothesis comparison : cardinal_comparability.
Hypothesis gap : infinite_powerset_gap.
Hypothesis choice : family_choice.
Hypothesis selector : selects_global_witnesses H s.

Local Definition conversion := RN.original_typed_decoded_conversion
  W H s HW HO HH classical_logic comparison gap choice selector.

Theorem original_typing_sound n (G : Ctx nat n) t T :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
  forall rho, valid_valuation H s G rho -> realizes H s G rho t T.
Proof.
  exact (original_realization_from_conversion W H s HW HO HH classical_logic
    comparison gap choice selector conversion n G t T).
Qed.

Theorem original_denotation_coherent n (G : Ctx nat n) rho t T v w :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
  valid_valuation H s G rho ->
  denotes H s n G rho t v -> denotes H s n G rho t w -> EQ v w.
Proof.
  intros HG HT HV DV DW.
  exact (typed_coherence_from_conversion H s conversion n t G T rho HG HT HV v w DV DW).
Qed.

Theorem original_membership_sound n (G : Ctx nat n) rho t T v a :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T -> valid_valuation H s G rho ->
  denotes H s n G rho t v -> denotes H s n G rho T a -> IN v (decode a).
Proof.
  exact (typed_membership_from_conversion W H s HW HO HH classical_logic comparison gap
    choice selector conversion n G rho t T v a).
Qed.

Theorem original_rank_sound n (G : Ctx nat n) rho t k v :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t (𝓤 k) -> valid_valuation H s G rho ->
  denotes H s n G rho t v -> IN v (U k).
Proof.
  exact (typed_rank_from_conversion W H s HW HO HH classical_logic comparison gap
    choice selector conversion n G rho t k v).
Qed.

Theorem bottom_interpretation_empty v : ~ IN v (decode (bottom_code H s)).
Proof.
  intro Hv.
  assert (Ha : IN (repr (sort 0)) (U 0)) by apply sort_in_every_universe.
  assert (Hb : forall x, IN x (decode (repr (sort 0))) -> IN x (U 0)).
  { intros x Hx; eapply IN_sound_right; [apply decode_sort |exact Hx]. }
  pose proof (proj2 (semantic_product_typed W H s HW HO HH classical_logic comparison gap choice
    selector 0 0 (repr (sort 0)) (fun x => x) Ha Hb)) as HB.
  destruct (bijection_surjective_value _ _ _ v HB Hv) as [g [Hg Eg]].
  exact (decoded_sort_product_empty carrier 0 g Hg).
Qed.

Theorem closed_bottom_uninhabited (t : Term nat 0) :
  ~ @typ nat RankSorts 0 ε t bottom.
Proof.
  intro HT.
  set (rho := fun _ : Fin 0 => Vide).
  assert (HG : @wf nat RankSorts 0 ε) by constructor.
  assert (HV : valid_valuation H s ε rho) by exact I.
  destruct (original_typing_sound 0 ε t bottom HG HT rho HV)
    as [v [a [Dt [DA Hval]]]].
  assert (EA : EQ a (bottom_code H s)).
  { eapply original_denotation_coherent with (T := 𝓤 1); [exact HG |apply bottom_typed |
      exact HV |exact DA |apply bottom_denotes]. }
  apply (bottom_interpretation_empty v).
  eapply IN_sound_right; [apply decoding_extensional; exact EA |exact Hval].
Qed.
End Soundness.

(** Ordinary set-indexed Choice constructs the selector used by all rules.
    This theorem quantifies over ALL original typing derivations. *)
Theorem sound_model_exists W H :
  transitive_set W -> INC omega_codes W -> tower_envelope W H ->
  (forall P : Prop, P \/ ~ P) -> cardinal_comparability -> infinite_powerset_gap ->
  family_choice -> exists s, selects_global_witnesses H s /\
    (forall n (G : Ctx nat n) t T,
      @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
      forall rho, valid_valuation H s G rho -> realizes H s G rho t T) /\
    (forall n (G : Ctx nat n) rho t T v a,
      @wf nat RankSorts n G -> @typ nat RankSorts n G t T -> valid_valuation H s G rho ->
      denotes H s n G rho t v -> denotes H s n G rho T a -> IN v (decode a)).
Proof.
  intros HW HO HH classical_logic comparison gap choice.
  destruct (semantic_operations_exist choice H) as [s HS].
  exists s; split; [exact HS |]. split.
  - exact (original_typing_sound W H s HW HO HH classical_logic comparison gap choice HS).
  - exact (original_membership_sound W H s HW HO HH classical_logic comparison gap choice HS).
Qed.

Theorem sound_nontrivial_model_exists W H :
  transitive_set W -> INC omega_codes W -> tower_envelope W H ->
  (forall P : Prop, P \/ ~ P) -> cardinal_comparability -> infinite_powerset_gap ->
  family_choice -> exists s, selects_global_witnesses H s /\
    (forall n (G : Ctx nat n) t T,
      @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
      forall rho, valid_valuation H s G rho -> realizes H s G rho t T) /\
    (forall v, ~ IN v (decode (bottom_code H s))).
Proof.
  intros HW HO HH classical_logic comparison gap choice.
  destruct (semantic_operations_exist choice H) as [s HS].
  exists s; split; [exact HS |]. split.
  - exact (original_typing_sound W H s HW HO HH classical_logic comparison gap choice HS).
  - exact (bottom_interpretation_empty W H s HW HO HH classical_logic comparison gap choice HS).
Qed.
End ModelSoundness.

Print Assumptions ModelSoundness.original_typing_sound.
Print Assumptions ModelSoundness.original_denotation_coherent.
Print Assumptions ModelSoundness.original_membership_sound.
Print Assumptions ModelSoundness.original_rank_sound.
Print Assumptions ModelSoundness.sound_model_exists.
Print Assumptions ModelSoundness.bottom_interpretation_empty.
Print Assumptions ModelSoundness.closed_bottom_uninhabited.
Print Assumptions ModelSoundness.sound_nontrivial_model_exists.
Check ModelSoundness.original_typing_sound.
Check ModelSoundness.sound_model_exists.
Check ModelSoundness.sound_nontrivial_model_exists.
