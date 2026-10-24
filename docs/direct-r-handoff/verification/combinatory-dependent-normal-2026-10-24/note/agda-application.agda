app : ∀ {Γ a b} (A : Ty Γ a) (B : Ty (ext Γ A) b) (f x : Tm Γ)
    → tyOf f ≡ (max (suc a) b , Pi A B)
    → tyOf x ≡ (a , A) → Tm Γ
app {a = a} A B f x pf px = app-guarded A B f x pf
  (px ∙ λ i → a , sym (ty-id A) i)
