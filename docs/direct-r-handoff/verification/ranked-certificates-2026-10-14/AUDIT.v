(** Partial proof checkpoint: print explicit premises as well as assumptions.
    In particular, closed reports do not discharge semantic conversion. *)
From PTSrkModel Require Import NeutralCutRank RankedDenotation RankedTransport
  RankedSubstitution RankedRootBeta CanonicalValuationTransport
  MaterialZermelo RealizationInduction.

Check NeutralCutRank.bounded_exposed_lambda_domain_rank.
Print Assumptions NeutralCutRank.bounded_exposed_lambda_domain_rank.
Check RankedDenotation.type_certificate.
Print Assumptions RankedDenotation.type_certificate.
Check RankedDenotation.membership.
Print Assumptions RankedDenotation.membership.
Check RankedTransport.certificate_type_alignment.
Print Assumptions RankedTransport.certificate_type_alignment.
Check RankedSubstitution.normalized_binder_extension.
Print Assumptions RankedSubstitution.normalized_binder_extension.
Check RankedSubstitution.certificate_replace_nonlambda.
Print Assumptions RankedSubstitution.certificate_replace_nonlambda.
Check RankedSubstitution.certificate_rank_zero_substitution.
Print Assumptions RankedSubstitution.certificate_rank_zero_substitution.
Check RankedRootBeta.certified_root_beta_nonlambda.
Print Assumptions RankedRootBeta.certified_root_beta_nonlambda.
Check CanonicalValuationTransport.corresponding_environment_transport.
Print Assumptions CanonicalValuationTransport.corresponding_environment_transport.
Check MaterialZermelo.bzc_satisfied.
Print Assumptions MaterialZermelo.bzc_satisfied.
Check MaterialZermelo.bzc_logical_soundness.
Print Assumptions MaterialZermelo.bzc_logical_soundness.

(** Original target remains conditional; retain the complete printed type. *)
Check original_realization_from_conversion.
Print Assumptions original_realization_from_conversion.
