{-# OPTIONS --cubical --safe --guardedness #-}
module SKBracketSize where

-- Output tree size only: each S, K and ground label counts as one atom.
-- Type-index payloads, label bit lengths, proof objects, compiler working
-- storage and runtime are NOT included in this measure.
open import PTSPrelude
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Nat.Order using
  (_≤_; ≤-refl; ≤-trans; ≤-sucℕ; suc-≤-suc; ≤-+-≤; ≤SumLeft; ≤SumRight)
open import Cubical.Tactics.NatSolver
open import FiniteBounds using
  (_+_; _·_; _^_; tower; product-monotone; power-exponent-monotone)
open import RawSizeBounds using (rounds-size)
import BoundedReduction as R
import BinderFreeCore as SK
import BinderFreeBoundary as B
import SKSource as L
import SKSourceNormal as SN
import SKBracket as C
import SKCanonical as Canonical

private
  variable
    Γ : L.Con
    A D : SK.Ty

atoms : SK.Tm A → Nat
atoms SK.S = 1
atoms SK.K = 1
atoms (SK.ground n) = 1
atoms (f SK.· x) = atoms f + atoms x

open-atoms : C.Code Γ A → Nat
open-atoms C.s = 1
open-atoms C.k = 1
open-atoms (C.label n) = 1
open-atoms (C.cv x) = 1
open-atoms (f C.· x) = open-atoms f + open-atoms x

source-nodes : L.Source Γ A → Nat
source-nodes (L.var x) = 1
source-nodes (L.ground n) = 1
source-nodes (L.lam b) = suc (source-nodes b)
source-nodes (L.app f x) = suc (source-nodes f + source-nodes x)

private
  no-fin : ∀ {X : Set} → R.Fin zero → X
  no-fin ()

  bracket-join : (a b f x : Nat) → suc f ≤ 4 · a → suc x ≤ 4 · b
    → suc (suc f + x) ≤ 4 · (a + b)
  bracket-join a b f x hf hx =
    subst (λ q → q ≤ 4 · (a + b)) left-law
      (subst (suc f + suc x ≤_) right-law
        (≤-+-≤ hf hx))
    where
    left-law : suc f + suc x ≡ suc (suc f + x)
    left-law = solveℕ!
    right-law : 4 · a + 4 · b ≡ 4 · (a + b)
    right-law = solveℕ!

  double-four : (p : Nat) → p + p ≤ 4 · p
  double-four p = 2 · p , solveℕ!

  power-join : (a b : Nat) → 4 ^ a + 4 ^ b ≤ 4 ^ suc (a + b)
  power-join a b = ≤-trans {m = 4 ^ (a + b) + 4 ^ (a + b)} {n = 4 ^ suc (a + b)}
    (≤-+-≤ (power-exponent-monotone 4 {m = a} {n = a + b} (3 , refl) ≤SumLeft)
      (power-exponent-monotone 4 {m = b} {n = a + b} (3 , refl) ≤SumRight))
    (double-four (4 ^ (a + b)))

-- The extra one absorbs the S introduced at each application node.
bracket-bound : (p : C.Code (Γ L.▻ A) D)
  → suc (open-atoms (C.bracket p)) ≤ 4 · open-atoms p
bracket-bound C.s = 1 , refl
bracket-bound C.k = 1 , refl
bracket-bound (C.label n) = 1 , refl
bracket-bound {Γ} {A} (C.cv x) = L.caseVar-rel
  {P = λ D → C.Code Γ (A SK.⇒ D)} {Q = Unit}
  (λ _ p _ → suc (open-atoms p) ≤ 4) x
  C.identity (λ y → C.k C.· C.cv y) tt (λ _ → tt)
  ≤-refl (λ y → 1 , refl)
bracket-bound (f C.· x) = bracket-join
  (open-atoms f) (open-atoms x) (open-atoms (C.bracket f))
  (open-atoms (C.bracket x)) (bracket-bound f) (bracket-bound x)

compile-open-bound : (s : L.Source Γ A)
  → open-atoms (C.compile-open s) ≤ 4 ^ source-nodes s
compile-open-bound (L.var x) = 3 , refl
compile-open-bound (L.ground n) = 3 , refl
compile-open-bound (L.lam b) = ≤-trans {m = 4 · open-atoms (C.compile-open b)}
  (≤-trans ≤-sucℕ (bracket-bound (C.compile-open b)))
  (product-monotone {a = 4} {b = 4} ≤-refl (compile-open-bound b))
compile-open-bound (L.app f x) = ≤-trans
  (≤-+-≤ (compile-open-bound f) (compile-open-bound x))
  (power-join (source-nodes f) (source-nodes x))

close-atoms : (p : C.Code L.ε A) → atoms (C.close p) ≡ open-atoms p
close-atoms C.s = refl
close-atoms C.k = refl
close-atoms (C.label n) = refl
close-atoms (C.cv x) = no-fin (L.eraseVar x)
close-atoms (f C.· x) = cong₂ _+_ (close-atoms f) (close-atoms x)

compile-bound : (s : L.Source L.ε A) → atoms (C.compile s) ≤ 4 ^ source-nodes s
compile-bound s = subst (_≤ 4 ^ source-nodes s)
  (sym (close-atoms (C.compile-open s))) (compile-open-bound s)

source-native-nodes : (s : L.Source Γ A) → source-nodes s ≤ R.nodes (L.erase s)
source-native-nodes (L.var x) = ≤-refl
source-native-nodes (L.ground n) = ≤-refl
source-native-nodes (L.lam b) = suc-≤-suc
  (≤-trans (source-native-nodes b) ≤SumRight)
source-native-nodes (L.app f x) = suc-≤-suc
  (≤-+-≤ (source-native-nodes f) (source-native-nodes x))

normalized-source-bound : (s : L.Source Γ A)
  → source-nodes (SN.normalize s) ≤ tower (SN.budget s) (R.nodes (L.erase s))
normalized-source-bound s = ≤-trans (source-native-nodes (SN.normalize s))
  (subst (λ u → R.nodes u ≤ tower (SN.budget s) (R.nodes (L.erase s)))
    (sym (L.erase-rounds (SN.budget s) s))
    (rounds-size (SN.budget s) (L.erase s)))

-- BEGINSKCANONICALSIZE
canonical-output-bound : (t : SK.Tm A)
  → atoms (Canonical.normalize t)
      ≤ 4 ^ tower (SN.budget (C.expand-source t)) (R.nodes (B.expand {zero} t))
canonical-output-bound t = subst
  (λ u → atoms (Canonical.normalize t)
    ≤ 4 ^ tower (SN.budget (C.expand-source t)) (R.nodes u))
  (C.erase-expand t)
  (≤-trans (compile-bound (SN.normalize (C.expand-source t)))
    (power-exponent-monotone 4 (3 , refl) (normalized-source-bound (C.expand-source t))))
-- ENDSKCANONICALSIZE
