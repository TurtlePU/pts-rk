record SubNF (Γ : Context m) (Δ : Context n) : Set where
  constructor sub
  field
    sub-images : Fin m → Term n
    sub-normal : ∀ i → Normal (sub-images i)
    sub-typed : ∥ TypedSub Γ Δ sub-images ∥₁
