(** Public contracts of the shared fold interface and its concrete instances.
    Compatibility endpoints remain in Audit.v. Both audits are required by
    the development's audit alias. *)
From PTSrk.SelfInterpreter Require Import Algebra GenericFold UnifiedAlgebra PHOASFold PHOASCPS CombinatoryFold CombinatoryAlgebra.

(** Algebra *)
Check Algebra.Algebra.fold_typed.
Print Assumptions Algebra.Algebra.fold_typed.
Check Algebra.Algebra.fold_type_typed.
Print Assumptions Algebra.Algebra.fold_type_typed.
Check Algebra.Algebra.fold_closure.
Print Assumptions Algebra.Algebra.fold_closure.
Check Algebra.Algebra.fold_substitution.
Print Assumptions Algebra.Algebra.fold_substitution.
Check Algebra.Algebra.fold_extensional.
Print Assumptions Algebra.Algebra.fold_extensional.
Check Algebra.Algebra.fold_conversion.
Print Assumptions Algebra.Algebra.fold_conversion.
Check Algebra.Algebra.fold_neutral_normal.
Print Assumptions Algebra.Algebra.fold_neutral_normal.
Check Algebra.Algebra.run_context.
Print Assumptions Algebra.Algebra.run_context.
Check Algebra.Algebra.fold_context.
Print Assumptions Algebra.Algebra.fold_context.
Check Algebra.Algebra.presented_algebra.
Print Assumptions Algebra.Algebra.presented_algebra.
Check Algebra.Algebra.presented_fold.
Print Assumptions Algebra.Algebra.presented_fold.
Check Algebra.Algebra.context_algebra.
Print Assumptions Algebra.Algebra.context_algebra.
Check Algebra.Algebra.fold_original_context.
Print Assumptions Algebra.Algebra.fold_original_context.

(** GenericFold *)
Check GenericFold.GenericFold.expand_replace.
Print Assumptions GenericFold.GenericFold.expand_replace.
Check GenericFold.GenericFold.expand_typed.
Print Assumptions GenericFold.GenericFold.expand_typed.
Check GenericFold.GenericFold.expand_normal.
Print Assumptions GenericFold.GenericFold.expand_normal.
Check GenericFold.GenericFold.head_typed.
Print Assumptions GenericFold.GenericFold.head_typed.
Check GenericFold.GenericFold.head_type_sort.
Print Assumptions GenericFold.GenericFold.head_type_sort.
Check GenericFold.GenericFold.head_normal.
Print Assumptions GenericFold.GenericFold.head_normal.
Check GenericFold.GenericFold.specialize_first.
Print Assumptions GenericFold.GenericFold.specialize_first.
Check GenericFold.GenericFold.specialize_reduces.
Print Assumptions GenericFold.GenericFold.specialize_reduces.
Check GenericFold.GenericFold.specialize_typed.
Print Assumptions GenericFold.GenericFold.specialize_typed.
Check GenericFold.GenericFold.fold_expand.
Print Assumptions GenericFold.GenericFold.fold_expand.
Check GenericFold.GenericFold.run_computes.
Print Assumptions GenericFold.GenericFold.run_computes.
Check GenericFold.GenericFold.run_typed.
Print Assumptions GenericFold.GenericFold.run_typed.
Check GenericFold.GenericFold.run_closure.
Print Assumptions GenericFold.GenericFold.run_closure.
Check GenericFold.GenericFold.run_composition.
Print Assumptions GenericFold.GenericFold.run_composition.

(** UnifiedAlgebra *)
Check UnifiedAlgebra.UnifiedAlgebra.identity_algebra.
Print Assumptions UnifiedAlgebra.UnifiedAlgebra.identity_algebra.
Check UnifiedAlgebra.UnifiedAlgebra.interface_formed.
Print Assumptions UnifiedAlgebra.UnifiedAlgebra.interface_formed.
Check UnifiedAlgebra.UnifiedAlgebra.type_program_typed.
Print Assumptions UnifiedAlgebra.UnifiedAlgebra.type_program_typed.
Check UnifiedAlgebra.UnifiedAlgebra.term_program_typed.
Print Assumptions UnifiedAlgebra.UnifiedAlgebra.term_program_typed.
Check UnifiedAlgebra.UnifiedAlgebra.programs_normal.
Print Assumptions UnifiedAlgebra.UnifiedAlgebra.programs_normal.
Check UnifiedAlgebra.UnifiedAlgebra.arbitrary_algebra_typed.
Print Assumptions UnifiedAlgebra.UnifiedAlgebra.arbitrary_algebra_typed.
Check UnifiedAlgebra.UnifiedAlgebra.identity_term_recovers.
Print Assumptions UnifiedAlgebra.UnifiedAlgebra.identity_term_recovers.
Check UnifiedAlgebra.UnifiedAlgebra.identity_type_recovers.
Print Assumptions UnifiedAlgebra.UnifiedAlgebra.identity_type_recovers.
Check UnifiedAlgebra.UnifiedAlgebra.identity_result_recovers.
Print Assumptions UnifiedAlgebra.UnifiedAlgebra.identity_result_recovers.
Check UnifiedAlgebra.UnifiedAlgebra.identity_original_type.
Print Assumptions UnifiedAlgebra.UnifiedAlgebra.identity_original_type.
Check UnifiedAlgebra.UnifiedAlgebra.head_typed.
Print Assumptions UnifiedAlgebra.UnifiedAlgebra.head_typed.
Check UnifiedAlgebra.UnifiedAlgebra.head_computes.
Print Assumptions UnifiedAlgebra.UnifiedAlgebra.head_computes.
Check UnifiedAlgebra.UnifiedAlgebra.head_normal.
Print Assumptions UnifiedAlgebra.UnifiedAlgebra.head_normal.
Check UnifiedAlgebra.UnifiedAlgebra.identity_fields_normal.
Print Assumptions UnifiedAlgebra.UnifiedAlgebra.identity_fields_normal.
Check UnifiedAlgebra.UnifiedAlgebra.interpret_typed.
Print Assumptions UnifiedAlgebra.UnifiedAlgebra.interpret_typed.
Check UnifiedAlgebra.UnifiedAlgebra.interpret_recovers.
Print Assumptions UnifiedAlgebra.UnifiedAlgebra.interpret_recovers.
Check UnifiedAlgebra.UnifiedAlgebra.interpret_original_type.
Print Assumptions UnifiedAlgebra.UnifiedAlgebra.interpret_original_type.
Check UnifiedAlgebra.UnifiedAlgebra.open_recovers.
Print Assumptions UnifiedAlgebra.UnifiedAlgebra.open_recovers.
Check UnifiedAlgebra.UnifiedAlgebra.open_original_type.
Print Assumptions UnifiedAlgebra.UnifiedAlgebra.open_original_type.
Check UnifiedAlgebra.UnifiedAlgebra.every_closed_original.
Print Assumptions UnifiedAlgebra.UnifiedAlgebra.every_closed_original.
Check UnifiedAlgebra.UnifiedAlgebra.recovery_reflects_conversion.
Print Assumptions UnifiedAlgebra.UnifiedAlgebra.recovery_reflects_conversion.
Check UnifiedAlgebra.UnifiedAlgebra.normal_recovery_injective.
Print Assumptions UnifiedAlgebra.UnifiedAlgebra.normal_recovery_injective.

(** PHOASFold *)
Check PHOASFold.PHOASFold.filling_typed.
Print Assumptions PHOASFold.PHOASFold.filling_typed.
Check PHOASFold.PHOASFold.fold_typed.
Print Assumptions PHOASFold.PHOASFold.fold_typed.
Check PHOASFold.PHOASFold.fold_quotation.
Print Assumptions PHOASFold.PHOASFold.fold_quotation.
Check PHOASFold.PHOASFold.shared_fold.
Print Assumptions PHOASFold.PHOASFold.shared_fold.
Check PHOASFold.PHOASFold.observer_handler_typed.
Print Assumptions PHOASFold.PHOASFold.observer_handler_typed.
Check PHOASFold.PHOASFold.observer_fold_typed.
Print Assumptions PHOASFold.PHOASFold.observer_fold_typed.
Check PHOASFold.PHOASFold.observe_typed.
Print Assumptions PHOASFold.PHOASFold.observe_typed.
Check PHOASFold.PHOASFold.observe_quotation.
Print Assumptions PHOASFold.PHOASFold.observe_quotation.
Check PHOASFold.PHOASFold.observations_distinct.
Print Assumptions PHOASFold.PHOASFold.observations_distinct.
Check PHOASFold.PHOASFold.observer_example_sources_typed.
Print Assumptions PHOASFold.PHOASFold.observer_example_sources_typed.
Check PHOASFold.PHOASFold.observer_example_source_beta.
Print Assumptions PHOASFold.PHOASFold.observer_example_source_beta.
Check PHOASFold.PHOASFold.observer_not_conversion_invariant.
Print Assumptions PHOASFold.PHOASFold.observer_not_conversion_invariant.

(** PHOASCPS *)
Check PHOASCPS.PHOASCPS.continuation_sort.
Print Assumptions PHOASCPS.PHOASCPS.continuation_sort.
Check PHOASCPS.PHOASCPS.return_value_typed.
Print Assumptions PHOASCPS.PHOASCPS.return_value_typed.
Check PHOASCPS.PHOASCPS.return_value_beta.
Print Assumptions PHOASCPS.PHOASCPS.return_value_beta.
Check PHOASCPS.PHOASCPS.abstraction_typed.
Print Assumptions PHOASCPS.PHOASCPS.abstraction_typed.
Check PHOASCPS.PHOASCPS.application_typed.
Print Assumptions PHOASCPS.PHOASCPS.application_typed.
Check PHOASCPS.PHOASCPS.application_run.
Print Assumptions PHOASCPS.PHOASCPS.application_run.
Check PHOASCPS.PHOASCPS.abstraction_application_run.
Print Assumptions PHOASCPS.PHOASCPS.abstraction_application_run.
Check PHOASCPS.PHOASCPS.continuation_not_same_rank.
Print Assumptions PHOASCPS.PHOASCPS.continuation_not_same_rank.
Check PHOASCPS.PHOASCPS.value_type_sort.
Print Assumptions PHOASCPS.PHOASCPS.value_type_sort.
Check PHOASCPS.PHOASCPS.computation_type_sort.
Print Assumptions PHOASCPS.PHOASCPS.computation_type_sort.
Check PHOASCPS.PHOASCPS.no_rank_one_cps_budget.
Print Assumptions PHOASCPS.PHOASCPS.no_rank_one_cps_budget.
Check PHOASCPS.PHOASCPS.no_rank_one_cps_type_budget.
Print Assumptions PHOASCPS.PHOASCPS.no_rank_one_cps_type_budget.

(** CombinatoryFold *)
Check CombinatoryFold.CombinatoryFold.fold_fusion.
Print Assumptions CombinatoryFold.CombinatoryFold.fold_fusion.
Check CombinatoryFold.CombinatoryFold.fold_map.
Print Assumptions CombinatoryFold.CombinatoryFold.fold_map.
Check CombinatoryFold.CombinatoryFold.quote_typed.
Print Assumptions CombinatoryFold.CombinatoryFold.quote_typed.
Check CombinatoryFold.CombinatoryFold.code_type_sorted.
Print Assumptions CombinatoryFold.CombinatoryFold.code_type_sorted.
Check CombinatoryFold.CombinatoryFold.run_quote_beta.
Print Assumptions CombinatoryFold.CombinatoryFold.run_quote_beta.
Check CombinatoryFold.CombinatoryFold.run_typed.
Print Assumptions CombinatoryFold.CombinatoryFold.run_typed.
Check CombinatoryFold.CombinatoryFold.quote_normal.
Print Assumptions CombinatoryFold.CombinatoryFold.quote_normal.
Check CombinatoryFold.CombinatoryFold.quote_injective.
Print Assumptions CombinatoryFold.CombinatoryFold.quote_injective.
Check CombinatoryFold.CombinatoryFold.quote_conversion_iff.
Print Assumptions CombinatoryFold.CombinatoryFold.quote_conversion_iff.
Check CombinatoryFold.CombinatoryFold.first_op_typed.
Print Assumptions CombinatoryFold.CombinatoryFold.first_op_typed.
Check CombinatoryFold.CombinatoryFold.constant_op_typed.
Print Assumptions CombinatoryFold.CombinatoryFold.constant_op_typed.
Check CombinatoryFold.CombinatoryFold.first_fold_beta.
Print Assumptions CombinatoryFold.CombinatoryFold.first_fold_beta.
Check CombinatoryFold.CombinatoryFold.first_leaf_typed.
Print Assumptions CombinatoryFold.CombinatoryFold.first_leaf_typed.
Check CombinatoryFold.CombinatoryFold.first_leaf_beta.
Print Assumptions CombinatoryFold.CombinatoryFold.first_leaf_beta.
Check CombinatoryFold.CombinatoryFold.test_node_typed.
Print Assumptions CombinatoryFold.CombinatoryFold.test_node_typed.
Check CombinatoryFold.CombinatoryFold.test_node_beta.
Print Assumptions CombinatoryFold.CombinatoryFold.test_node_beta.
Check CombinatoryFold.CombinatoryFold.test_node_at_typed.
Print Assumptions CombinatoryFold.CombinatoryFold.test_node_at_typed.
Check CombinatoryFold.CombinatoryFold.test_node_at_beta.
Print Assumptions CombinatoryFold.CombinatoryFold.test_node_at_beta.
Check CombinatoryFold.CombinatoryFold.continuation_sorted.
Print Assumptions CombinatoryFold.CombinatoryFold.continuation_sorted.
Check CombinatoryFold.CombinatoryFold.return_value_typed.
Print Assumptions CombinatoryFold.CombinatoryFold.return_value_typed.
Check CombinatoryFold.CombinatoryFold.cps_op_typed.
Print Assumptions CombinatoryFold.CombinatoryFold.cps_op_typed.
Check CombinatoryFold.CombinatoryFold.cps_fold_typed.
Print Assumptions CombinatoryFold.CombinatoryFold.cps_fold_typed.
Check CombinatoryFold.CombinatoryFold.cps_fold_beta.
Print Assumptions CombinatoryFold.CombinatoryFold.cps_fold_beta.
Check CombinatoryFold.CombinatoryFold.cps_fold_apply_beta.
Print Assumptions CombinatoryFold.CombinatoryFold.cps_fold_apply_beta.
Check CombinatoryFold.CombinatoryFold.cps_and_test_same_code.
Print Assumptions CombinatoryFold.CombinatoryFold.cps_and_test_same_code.
Check CombinatoryFold.CombinatoryFold.finitise_exact.
Print Assumptions CombinatoryFold.CombinatoryFold.finitise_exact.
Check CombinatoryFold.CombinatoryFold.fixed_dictionary_fidelity.
Print Assumptions CombinatoryFold.CombinatoryFold.fixed_dictionary_fidelity.
Check CombinatoryFold.CombinatoryFold.hilbert_finite_fold.
Print Assumptions CombinatoryFold.CombinatoryFold.hilbert_finite_fold.
Check CombinatoryFold.CombinatoryFold.catalogue_finite_fold.
Print Assumptions CombinatoryFold.CombinatoryFold.catalogue_finite_fold.

(** CombinatoryAlgebra *)
Check CombinatoryAlgebra.CombinatoryAlgebra.signature_filling_typed.
Print Assumptions CombinatoryAlgebra.CombinatoryAlgebra.signature_filling_typed.
Check CombinatoryAlgebra.CombinatoryAlgebra.fold_is_run.
Print Assumptions CombinatoryAlgebra.CombinatoryAlgebra.fold_is_run.
Check CombinatoryAlgebra.CombinatoryAlgebra.fold_quote_beta.
Print Assumptions CombinatoryAlgebra.CombinatoryAlgebra.fold_quote_beta.
Check CombinatoryAlgebra.CombinatoryAlgebra.fold_quote_typed.
Print Assumptions CombinatoryAlgebra.CombinatoryAlgebra.fold_quote_typed.
