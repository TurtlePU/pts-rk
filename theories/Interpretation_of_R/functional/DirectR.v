(** Checked direct functional interpretation, harmonized Theorem 7. *)

(** Public facade, including unconditional and effective theorem interfaces.
    The legacy bounded generator contracts remain separate. *)
From Interpretation_of_R.functional Require Export DirectRCodes DirectRProofs DirectRGenerated
  DirectRFirstOrder DirectRObligations DirectRTheorem7.
From Interpretation_of_R Require Export DirectRKernel DirectREval DirectRCheck.

Module Codes := DirectRCodes.Codes.
Module Kernel := DirectRProofs.Kernel.
Module Generated := DirectRGenerated.Generated.
Module FirstOrder := DirectRFirstOrder.FirstOrder.
Module Obligations := DirectRObligations.Obligations.
Module Theorem7 := DirectRTheorem7.Theorem7.
