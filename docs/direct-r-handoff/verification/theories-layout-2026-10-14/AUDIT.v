(** Public interfaces after the physical move. Compile against a fresh build;
    explicit semantic parameters remain visible in the printed theorem types. *)
From Interpretation_of_R.relational Require Import DirectRTheorem4.
From Interpretation_of_R.functional Require Import DirectRTheorem7.
From PTSrkModel Require Import RankedNormalization ModelSoundness.
From PTSrk.NormalizationComplexity Require Import
  BoundedNormalization Normalization STLCEmbedding.

Check Theorem4.theorem4.
Print Assumptions Theorem4.theorem4.
Check Theorem7.theorem7.
Print Assumptions Theorem7.theorem7.
Check Theorem7.theorem5_target.
Print Assumptions Theorem7.theorem5_target.
Check Theorem7.effective_deduction.
Print Assumptions Theorem7.effective_deduction.

Check RankedNormalization.original_typed_conversion_values.
Print Assumptions RankedNormalization.original_typed_conversion_values.
Check ModelSoundness.original_typing_sound.
Print Assumptions ModelSoundness.original_typing_sound.
Check ModelSoundness.original_membership_sound.
Print Assumptions ModelSoundness.original_membership_sound.
Check ModelSoundness.sound_nontrivial_model_exists.
Print Assumptions ModelSoundness.sound_nontrivial_model_exists.

Check fixed_rank_normalization.
Print Assumptions fixed_rank_normalization.
Check rank_bound_in_linear_time.
Print Assumptions rank_bound_in_linear_time.
Check normalization_in_TOWER.
Print Assumptions normalization_in_TOWER.
Check ChurchSTLC.church_stlc_reduction.
Print Assumptions ChurchSTLC.church_stlc_reduction.
