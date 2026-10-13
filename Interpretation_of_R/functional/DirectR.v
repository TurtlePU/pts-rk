(** Direct R interpretation -- restructured draft, 2026-10-13.
    Compiler-unchecked. See docs/DirectR.md for the exact verification status. *)

(** Public facade. Concrete computations and Prop-level arithmetic are
    deliberately NOT imported into the default interpretation facade. *)
From Interpretation_of_R.functional Require Export DirectRCodes DirectRProofs DirectRGenerated
  DirectRFirstOrder DirectRObligations.
From Interpretation_of_R Require Export DirectRKernel DirectREval DirectRCheck.

Module Codes := DirectRCodes.Codes.
Module Kernel := DirectRProofs.Kernel.
Module Generated := DirectRGenerated.Generated.
Module FirstOrder := DirectRFirstOrder.FirstOrder.
Module Obligations := DirectRObligations.Obligations.
