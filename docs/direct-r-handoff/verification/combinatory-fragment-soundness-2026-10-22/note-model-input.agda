record ModelInput (m n : Nat) : Set where
  field
    source : ContextCertificate m
    target : ContextCertificate n
    environment : ValuationCertificate m n
    derivation : Certificate m
open ModelInput public

InputAccepted : ∀ {m n} → ModelInput m n → Set
InputAccepted x = ContextAccepted (source x) × ContextAccepted (target x)
  × ValuationAccepted (certificate-context (source x))
      (certificate-context (target x)) (environment x)
  × Accepted (certificate-context (source x)) (derivation x)
