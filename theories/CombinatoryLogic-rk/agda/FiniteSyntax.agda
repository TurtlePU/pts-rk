{-# OPTIONS --cubical --safe --guardedness #-}
module FiniteSyntax where

open import PTSPrelude public
open import Cubical.Data.Nat.Base public using (_+_; _·_)
open import Cubical.Data.FinData.Base public
  using (Fin) renaming (zero to fzero; suc to fsuc)

-- The original annotated, scoped syntax; the sort-label set is a parameter.
data Raw (Label : Set) (n : Nat) : Set where
  U   : Label → Raw Label n
  var : Fin n → Raw Label n
  pi lam : Raw Label n → Raw Label (suc n) → Raw Label n
  app : Raw Label n → Raw Label n → Raw Label n

nodes : ∀ {Label n} → Raw Label n → Nat
nodes (U _) = 1
nodes (var _) = 1
nodes (pi A B) = suc (nodes A + nodes B)
nodes (lam A b) = suc (nodes A + nodes b)
nodes (app f x) = suc (nodes f + nodes x)

relabel : ∀ {Label Other n} → (Label → Other) → Raw Label n → Raw Other n
relabel f (U i) = U (f i)
relabel f (var i) = var i
relabel f (pi A B) = pi (relabel f A) (relabel f B)
relabel f (lam A b) = lam (relabel f A) (relabel f b)
relabel f (app t u) = app (relabel f t) (relabel f u)

relabel-nodes : ∀ {Label Other n} (f : Label → Other) (t : Raw Label n)
  → nodes (relabel f t) ≡ nodes t
relabel-nodes f (U _) = refl
relabel-nodes f (var _) = refl
relabel-nodes f (pi A B) = cong suc
  (cong₂ _+_ (relabel-nodes f A) (relabel-nodes f B))
relabel-nodes f (lam A b) = cong suc
  (cong₂ _+_ (relabel-nodes f A) (relabel-nodes f b))
relabel-nodes f (app t u) = cong suc
  (cong₂ _+_ (relabel-nodes f t) (relabel-nodes f u))
