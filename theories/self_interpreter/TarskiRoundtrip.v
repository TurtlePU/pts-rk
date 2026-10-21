From Stdlib Require Import Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation
  Ranks DefEq Reduction AbstractRewriting Congruence.
From PTSrk.NormalizationComplexity Require Import Greedy.
From PTSrk.SelfInterpreter Require Import BrownPalsberg IndexedEquality
  TarskiCasts ChurchSyntaxFaithful.
Import Context.

(** A precise limitation of the EXISTING neutral casts: their roundtrip
    is not original beta conversion. This does not exclude an internal
    equality witness, additional independently realized coherence fields,
    different casts, or a full dependent PHOAS construction. *)
Module TarskiRoundtrip.
Module BP := BrownPalsberg.BrownPalsberg.
Module IE := IndexedEquality.IndexedEquality.
Module TC := TarskiCasts.TarskiCasts.

Definition types_context c : Ctx nat 2 := (ε & 𝓤 c) & 𝓤 c.
Definition proof_context c : Ctx nat 3 := types_context c &
  TC.type_law c (var (fsucc fzero)) (var fzero).
Definition context c : Ctx nat 4 := proof_context c & var (fsucc (fsucc fzero)).

Definition source_type : Term nat 4 := var (fsucc (fsucc (fsucc fzero))).
Definition target_type : Term nat 4 := var (fsucc (fsucc fzero)).
Definition evidence : Term nat 4 := var (fsucc fzero).
Definition value : Term nat 4 := var fzero.
Definition roundtrip c : Term nat 4 :=
  app (TC.backward c source_type evidence)
    (app (TC.forward c source_type evidence) value).

Lemma types_context_wf c : @wf nat RankSorts 2 (types_context c).
Proof.
  unfold types_context; apply wf_cons with (ℓ := 0).
  - apply wf_cons with (ℓ := 0); [constructor | constructor; reflexivity].
  - constructor; reflexivity.
Qed.

Lemma proof_context_wf c : @wf nat RankSorts 3 (proof_context c).
Proof.
  unfold proof_context; apply wf_cons with (ℓ := c+2); [apply types_context_wf |].
  apply TC.type_law_sort.
  - change (typ (types_context c) (var (fsucc fzero))
      ((types_context c) !! fsucc fzero)); constructor.
  - change (typ (types_context c) (var fzero) ((types_context c) !! fzero)); constructor.
Qed.

Theorem context_wf c : @wf nat RankSorts 4 (context c).
Proof.
  unfold context; apply wf_cons with (ℓ := c); [apply proof_context_wf |].
  change (typ (proof_context c) (var (fsucc (fsucc fzero)))
    ((proof_context c) !! fsucc (fsucc fzero))); constructor.
Qed.

Theorem context_fields_typed c :
  @typ nat RankSorts 4 (context c) source_type (𝓤 c) /\
  @typ nat RankSorts 4 (context c) target_type (𝓤 c) /\
  @typ nat RankSorts 4 (context c) evidence (TC.type_law c source_type target_type) /\
  @typ nat RankSorts 4 (context c) value source_type.
Proof.
  repeat split.
  - change (typ (context c) (var (fsucc (fsucc (fsucc fzero))))
      ((context c) !! fsucc (fsucc (fsucc fzero)))); constructor.
  - change (typ (context c) (var (fsucc (fsucc fzero)))
      ((context c) !! fsucc (fsucc fzero))); constructor.
  - change (typ (context c) (var (fsucc fzero)) ((context c) !! fsucc fzero)); constructor.
  - change (typ (context c) (var fzero) ((context c) !! fzero)); constructor.
Qed.

Theorem roundtrip_typed c :
  @typ nat RankSorts 4 (context c) (roundtrip c) source_type.
Proof.
  destruct (context_fields_typed c) as [HS [HT [He Hx]]].
  destruct (TC.casts_typed c 4 (context c) source_type target_type evidence HS HT He)
    as [HF HB].
  unfold roundtrip; eapply BP.arr_apply; [exact HB |].
  eapply BP.arr_apply; eassumption.
Qed.

Theorem roundtrip_normal_distinct c :
  normalb (roundtrip c) = true /\ normalb value = true /\ roundtrip c <> value.
Proof. split; [reflexivity |]. split; [reflexivity | discriminate]. Qed.

Theorem roundtrip_not_convertible c : ~ def_equiv nat 4 (roundtrip c) value.
Proof.
  intro H. pose proof (normal_conversion_identity 4 (roundtrip c) value
    eq_refl eq_refl H) as E. discriminate E.
Qed.

(** The mismatch persists in actual dependent TYPE indices. K is an
    ordinary variable of type S -> U0, not an assumed separating model. *)
Definition dependent_context c : Ctx nat 5 := context c & BP.arr source_type (𝓤 0).
Definition direct_index : Term nat 5 := app (var fzero) (shift value).
Definition roundtrip_index c : Term nat 5 := app (var fzero) (shift (roundtrip c)).

Theorem dependent_context_wf c : @wf nat RankSorts 5 (dependent_context c).
Proof.
  unfold dependent_context; apply wf_cons with (ℓ := S c); [apply context_wf |].
  replace (S c) with (Nat.max (S c) 0) by lia.
  apply BP.arr_sort; [apply (proj1 (context_fields_typed c)) | constructor; reflexivity].
Qed.

Theorem dependent_indices_typed c :
  @typ nat RankSorts 5 (dependent_context c) direct_index (𝓤 0) /\
  @typ nat RankSorts 5 (dependent_context c) (roundtrip_index c) (𝓤 0).
Proof.
  assert (HK : typ (dependent_context c) (var fzero) (BP.arr (shift source_type) (𝓤 0))).
  { change (typ (dependent_context c) (var fzero) ((dependent_context c) !! fzero)); constructor. }
  split; unfold direct_index, roundtrip_index; eapply BP.arr_apply; try exact HK.
  - apply weakening. exact (proj2 (proj2 (proj2 (context_fields_typed c)))).
  - apply weakening, roundtrip_typed.
Qed.

Theorem dependent_indices_normal_distinct c :
  normalb direct_index = true /\ normalb (roundtrip_index c) = true /\
  direct_index <> roundtrip_index c.
Proof. split; [reflexivity |]. split; [reflexivity | discriminate]. Qed.

Theorem dependent_indices_not_convertible c :
  ~ def_equiv nat 5 direct_index (roundtrip_index c).
Proof.
  intro H. pose proof (normal_conversion_identity 5 direct_index (roundtrip_index c)
    eq_refl eq_refl H) as E. discriminate E.
Qed.

(** This negative result concerns a NEUTRAL supplied proof. At actual
    reflexivity the same cast definitions recover their literal input. *)
Theorem reflexive_roundtrip_recovers c n (S V x : Term nat n) :
  reduces_to nat n
    (app (TC.backward c S (IE.refl_case (Datatypes.S c) (𝓤 c) V))
      (app (TC.forward c S (IE.refl_case (Datatypes.S c) (𝓤 c) V)) x)) x.
Proof.
  destruct (TC.cast_application_reflexivity c n S V x) as [HF HB].
  eapply rtc_trans.
  - apply (@app_cong_par nat (reduces_to nat) _ _ n); [reflexivity | exact HF].
  - exact HB.
Qed.

Print Assumptions context_wf.
Print Assumptions context_fields_typed.
Print Assumptions roundtrip_typed.
Print Assumptions roundtrip_normal_distinct.
Print Assumptions roundtrip_not_convertible.
Print Assumptions dependent_context_wf.
Print Assumptions dependent_indices_typed.
Print Assumptions dependent_indices_normal_distinct.
Print Assumptions dependent_indices_not_convertible.
Print Assumptions reflexive_roundtrip_recovers.

End TarskiRoundtrip.
