{-# OPTIONS --cubical --safe --guardedness #-}
module RawSizeBounds where

open import FiniteSyntax
open import BoundedReduction
open import FiniteBounds using (tower; _^_; product-monotone;
  power-exponent-monotone; power-addition; tower-monotone)
open import ExponentialBounds using (exponential-join)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Properties using (·-identityˡ)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Tactics.NatSolver

private
  variable
    Label : Set
    m n : Nat

nodes-positive : (t : Raw Label n) → 1 ≤ nodes t
nodes-positive (U i) = ≤-refl
nodes-positive (var i) = ≤-refl
nodes-positive (pi A B) = suc-≤-suc zero-≤
nodes-positive (lam A b) = suc-≤-suc zero-≤
nodes-positive (app f u) = suc-≤-suc zero-≤

nodes-rename : (ρ : Fin m → Fin n) (t : Raw Label m)
  → nodes (rename ρ t) ≡ nodes t
nodes-rename ρ (U i) = refl
nodes-rename ρ (var i) = refl
nodes-rename ρ (pi A B) = cong suc
  (cong₂ _+_ (nodes-rename ρ A) (nodes-rename (liftRenaming ρ) B))
nodes-rename ρ (lam A b) = cong suc
  (cong₂ _+_ (nodes-rename ρ A) (nodes-rename (liftRenaming ρ) b))
nodes-rename ρ (app f u) = cong suc
  (cong₂ _+_ (nodes-rename ρ f) (nodes-rename ρ u))

private
  lifted-bound : (σ : Fin m → Raw Label n) (bound : Nat)
    → 1 ≤ bound → (∀ i → nodes (σ i) ≤ bound)
    → ∀ i → nodes (liftSubstitution σ i) ≤ bound
  lifted-bound σ bound one h i =
    caseFin-rel (λ t (_ : Unit) → nodes t ≤ bound) i
      (var fzero) (λ j → shift (σ j)) tt (λ _ → tt)
      one (λ j → subst (_≤ bound) (sym (nodes-rename fsuc (σ j))) (h j))

  replace-join : (x y l r bound : Nat) → 1 ≤ bound
    → x ≤ l · bound → y ≤ r · bound
    → suc (x + y) ≤ suc (l + r) · bound
  replace-join x y l r bound one hx hy =
    subst (suc (x + y) ≤_) distribute (≤-+-≤ one (≤-+-≤ hx hy))
    where
    distribute : bound + (l · bound + r · bound) ≡ suc (l + r) · bound
    distribute = solveℕ!

nodes-replace : (σ : Fin m → Raw Label n) (t : Raw Label m) (bound : Nat)
  → 1 ≤ bound → (∀ i → nodes (σ i) ≤ bound)
  → nodes (replace σ t) ≤ nodes t · bound
nodes-replace σ (U i) bound one h =
  subst (1 ≤_) (sym (·-identityˡ bound)) one
nodes-replace σ (var i) bound one h =
  subst (nodes (σ i) ≤_) (sym (·-identityˡ bound)) (h i)
nodes-replace σ (pi A B) bound one h =
  replace-join _ _ (nodes A) (nodes B) bound one
    (nodes-replace σ A bound one h)
    (nodes-replace (liftSubstitution σ) B bound one (lifted-bound σ bound one h))
nodes-replace σ (lam A b) bound one h =
  replace-join _ _ (nodes A) (nodes b) bound one
    (nodes-replace σ A bound one h)
    (nodes-replace (liftSubstitution σ) b bound one (lifted-bound σ bound one h))
nodes-replace σ (app f u) bound one h =
  replace-join _ _ (nodes f) (nodes u) bound one
    (nodes-replace σ f bound one h) (nodes-replace σ u bound one h)

nodes-substitute : (b : Raw Label (suc n)) (u : Raw Label n)
  → nodes (substitute b u) ≤ nodes b · nodes u
nodes-substitute b u = nodes-replace (single u) b (nodes u)
  (nodes-positive u)
  (λ i → caseFin-rel (λ t (_ : Unit) → nodes t ≤ nodes u) i
    u var tt (λ _ → tt) ≤-refl (λ _ → nodes-positive u))

private
  join-size : (a b x y : Nat) → 1 ≤ a → 1 ≤ b
    → x ≤ 2 ^ a → y ≤ 2 ^ b → suc (x + y) ≤ 2 ^ suc (a + b)
  join-size a b x y pa pb hx hy = ≤-trans
    (suc-≤-suc (≤-+-≤ hx hy)) (exponential-join a b pa pb)

  contract-size : (f u : Raw Label n) (a b : Nat) → 1 ≤ a → 1 ≤ b
    → nodes f ≤ 2 ^ a → nodes u ≤ 2 ^ b
    → nodes (contract f u) ≤ 2 ^ suc (a + b)
  contract-size (U i) u a b pa pb hf hu = join-size a b _ _ pa pb hf hu
  contract-size (var i) u a b pa pb hf hu = join-size a b _ _ pa pb hf hu
  contract-size (pi A B) u a b pa pb hf hu = join-size a b _ _ pa pb hf hu
  contract-size (app f v) u a b pa pb hf hu = join-size a b _ _ pa pb hf hu
  contract-size (lam A body) u a b pa pb hf hu = ≤-trans
    (nodes-substitute body u)
    (≤-trans multiplied
      (power-exponent-monotone 2 {m = a + b} {n = suc (a + b)} (1 , refl) ≤-sucℕ))
    where
    body-bound : nodes body ≤ 2 ^ a
    body-bound = ≤-trans (≤-suc ≤SumRight) hf
    multiplied : nodes body · nodes u ≤ 2 ^ (a + b)
    multiplied = subst (nodes body · nodes u ≤_) (sym (power-addition 2 a b))
      (product-monotone body-bound hu)

-- Every raw annotated term satisfies these bounds, without a typing premise.
-- BEGINRAWSIZE
greedy-size : (t : Raw Label n) → nodes (greedy t) ≤ 2 ^ nodes t
greedy-size (U i) = 1 , refl
greedy-size (var i) = 1 , refl
greedy-size (pi A B) = join-size (nodes A) (nodes B) _ _
  (nodes-positive A) (nodes-positive B) (greedy-size A) (greedy-size B)
greedy-size (lam A b) = join-size (nodes A) (nodes b) _ _
  (nodes-positive A) (nodes-positive b) (greedy-size A) (greedy-size b)
greedy-size (app f u) = contract-size (greedy f) (greedy u) (nodes f) (nodes u)
  (nodes-positive f) (nodes-positive u) (greedy-size f) (greedy-size u)

private
  tower-exponential : (d x : Nat) → tower d (2 ^ x) ≡ tower (suc d) x
  tower-exponential zero x = refl
  tower-exponential (suc d) x = cong (2 ^_) (tower-exponential d x)

rounds-size : (d : Nat) (t : Raw Label n)
  → nodes (rounds d t) ≤ tower d (nodes t)
rounds-size zero t = ≤-refl
rounds-size (suc d) t = subst (nodes (rounds d (greedy t)) ≤_)
  (tower-exponential d (nodes t))
  (≤-trans (rounds-size d (greedy t)) (tower-monotone d (greedy-size t)))
-- ENDRAWSIZE
