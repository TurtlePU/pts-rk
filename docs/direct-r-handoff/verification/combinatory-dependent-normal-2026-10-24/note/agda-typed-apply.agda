-- Total application at the exact substituted type, with a bounded beta trace.
-- Rank descent and subject reduction are proved from the original rules.
applyTypedWithin : ∀ {a} (inputs : TypedInputs a) → TypedResult inputs
applyTypedWithin inputs = normal-result inputs , output-typed inputs
