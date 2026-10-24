module _ (Label : Set) where
  data Nf (n : Nat) : Set
  data NonLamNf {n : Nat} : Nf n → Set
  erase : ∀ {n} → Nf n → Raw Label n

  data Nf n where
    nf-U   : Label → Nf n
    nf-var : Fin n → Nf n
    nf-pi nf-lam : Nf n → Nf (suc n) → Nf n
    nf-app : (f x : Nf n) → NonLamNf f → Nf n

  data NonLamNf {n} where
    non-lam : ∀ {f : Nf n} → NotLambda (erase f) → NonLamNf f

  erase (nf-U i) = U i
  erase (nf-var i) = var i
  erase (nf-pi A B) = pi (erase A) (erase B)
  erase (nf-lam A b) = lam (erase A) (erase b)
  erase (nf-app f x p) = app (erase f) (erase x)
