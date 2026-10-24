SizedNf : (a n s : Nat) → Set
SizedNf a n s = Σ (Nf (Fin a) n) (λ t → nodes (erase (Fin a) t) ≤ s)

ExactNf : (a n N : Nat) → Set
ExactNf a n N = Σ (Nf (Fin a) n) (λ t → nodes (erase (Fin a) t) ≡ N)
