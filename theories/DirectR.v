(** Direct R interpretation -- restructured draft, 2026-10-13.
    Compiler-unchecked. See docs/DirectR.md for the exact verification status. *)

(** Public facade. Concrete computations and Prop-level arithmetic are
    deliberately NOT imported into the default interpretation facade. *)
From PTSrk Require Export DirectRCodes DirectRKernel DirectREval DirectRCheck
  DirectRProofs DirectRGenerated DirectRFirstOrder DirectRObligations.

Module Codes := DirectRCodes.Codes.
Module Kernel := DirectRProofs.Kernel.
Module Generated := DirectRGenerated.Generated.
Module FirstOrder := DirectRFirstOrder.FirstOrder.
Module Obligations := DirectRObligations.Obligations.
