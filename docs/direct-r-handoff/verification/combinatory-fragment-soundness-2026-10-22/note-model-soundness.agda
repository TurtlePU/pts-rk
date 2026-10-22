ModelOutput : ∀ {m n} → ModelInput m n → Set
ModelOutput x = FiniteInterpretation toℕ (certificate-context (target x))
  (model-term-code x) (model-type-code x)

model-soundness : ∀ {m n} (x : ModelInput m n) → InputAccepted x → ModelOutput x
model-soundness x h = realize-typing toℕ (input-target-wf h)
  (model-term-code x) (model-type-code x)
  (subst2 (Typ (certificate-context (target x)))
    (sym (model-term-recovers x)) (sym (model-type-recovers x)) (input-typing h))
