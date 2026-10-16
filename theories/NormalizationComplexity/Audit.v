Require Import PTSrk.NormalizationComplexity.Rank
  PTSrk.NormalizationComplexity.Greedy PTSrk.NormalizationComplexity.Bounds
  PTSrk.NormalizationComplexity.Literals PTSrk.NormalizationComplexity.Runtime
  PTSrk.NormalizationComplexity.RedexRanks
  PTSrk.NormalizationComplexity.Morphisms
  PTSrk.NormalizationComplexity.Safety
  PTSrk.NormalizationComplexity.Descent
  PTSrk.NormalizationComplexity.BoundedNormalization
  PTSrk.NormalizationComplexity.EstimatorChecks
  PTSrk.NormalizationComplexity.SortBounds
  PTSrk.NormalizationComplexity.AutomaticBound
  PTSrk.NormalizationComplexity.Normalization.
Print Assumptions RankEstimate.lookup_cache.
Print Assumptions RankEstimate.rankPair_correct.
Print Assumptions RankEstimate.rankCached_correct.
Print Assumptions RankEstimate.traversal_correct.
Print Assumptions RankEstimate.estimateRank_correct.
Print Assumptions greedy_sound.
Print Assumptions rounds_sound.
Print Assumptions normalb_sound.
Print Assumptions normalizeWithin_sound.
Print Assumptions estimator_linear_cost.
Print Assumptions traversal_numeric_bound.
Print Assumptions estimate_linear_magnitude.
Print Assumptions nodes_subst.
Print Assumptions greedy_size.
Print Assumptions rounds_size.
Print Assumptions literal_rename.
Print Assumptions literal_replace.
Print Assumptions literal_subst.
Print Assumptions literal_step.
Print Assumptions literal_reduction.
Print Assumptions reachable_sort_literal.
Print Assumptions renameCosted_correct.
Print Assumptions renameCosted_bound.
Print Assumptions replaceCosted_correct.
Print Assumptions replaceCosted_bound.
Print Assumptions substCosted_correct.
Print Assumptions substCosted_bound.
Print Assumptions greedyCosted_correct.
Print Assumptions greedyCosted_bound.
Print Assumptions roundsCosted_correct.
Print Assumptions roundsCosted_work.
Print Assumptions fixed_rounds_elementary_cost.
Print Assumptions normalizeCosted_correct.
Print Assumptions normalizeCosted_sound.
Print Assumptions normalizeCosted_elementary.
Print Assumptions estimatedAttempt_tower_cost.
Print Assumptions redex_rank_positive.
Print Assumptions nonnormal_has_redex_rank.
Print Assumptions zero_bound_normal.
Print Assumptions sort_rank_unique.
Print Assumptions convertible_sort_rank.
Print Assumptions type_rank_unique.
Print Assumptions type_rank_conversion.
Print Assumptions product_rank_components.
Print Assumptions application_argument_rank.
Print Assumptions type_rank_substitution.
Print Assumptions type_rank_reduction.
Print Assumptions type_rank_greedy.
Print Assumptions application_result_rank.
Print Assumptions abstraction_domain_rank.
Print Assumptions typing_type_rank.
Print Assumptions application_rank_le_function.
Print Assumptions exposed_lambda_rank.
Print Assumptions greedy_contracted_head_bound.
Print Assumptions typing_replace.
Print Assumptions type_rank_replace.
Print Assumptions typing_rename.
Print Assumptions type_rank_replace_reflect.
Print Assumptions typing_context_last_reduction.
Print Assumptions safe_iff_bound.
Print Assumptions safe_rename.
Print Assumptions safe_replace.
Print Assumptions redex_bound_substitution.
Print Assumptions safe_context_last_reduction.
Print Assumptions greedy_safe_descent.
Print Assumptions greedy_strict_descent.
Print Assumptions bounded_rounds_normal.
Print Assumptions bounded_normalizer_succeeds.
Print Assumptions fixed_rank_normalization.
Print Assumptions EstimatorChecks.witness_typed.
Print Assumptions EstimatorChecks.witness_rank_two.
Print Assumptions EstimatorChecks.estimator_does_not_bound_head_ranks.
Print Assumptions spine_value_bound.
Print Assumptions sort_rank_size.
Print Assumptions typed_sort_rank_bound.
Print Assumptions type_rank_syntax_bound.
Print Assumptions safe_syntax_bound.
Print Assumptions conservative_rank_sound.
Print Assumptions conservative_rank_magnitude.
Print Assumptions nodesCosted_correct.
Print Assumptions nodesCosted_linear.
Print Assumptions conservativeRankCosted_correct.
Print Assumptions conservative_rank_linear_cost.
Print Assumptions automaticNormalizer_projection.
Print Assumptions automaticNormalizer_cost.
Print Assumptions normalization_in_TOWER.
Print Assumptions rank_bound_in_linear_time.

Check normalizeCosted_correct.
Check normalizeCosted_elementary.
Check estimatedAttempt_tower_cost.
Check zero_bound_normal.
Check exposed_lambda_rank.
Check greedy_contracted_head_bound.
Check redex_bound_substitution.
Check greedy_strict_descent.
Check bounded_rounds_normal.
Check fixed_rank_normalization.
Check EstimatorChecks.witness_typed.
Check EstimatorChecks.estimator_does_not_bound_head_ranks.
Check conservative_rank_sound.
Check normalization_in_TOWER.
Check rank_bound_in_linear_time.

Require Import PTSrk.NormalizationComplexity.STLCEmbedding.
Print Assumptions ChurchSTLC.typing_preserved.
Print Assumptions ChurchSTLC.step_reflected.
Print Assumptions ChurchSTLC.conversion_preserved.
Print Assumptions ChurchSTLC.conversion_reflected.
Print Assumptions ChurchSTLC.closed_typing.
Print Assumptions ChurchSTLC.closed_conversion.
Print Assumptions ChurchSTLC.close_size.
Print Assumptions ChurchSTLC.church_stlc_reduction.
Check ChurchSTLC.church_stlc_reduction.
