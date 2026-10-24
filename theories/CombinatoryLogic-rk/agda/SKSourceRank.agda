{-# OPTIONS --cubical --safe --guardedness #-}
module SKSourceRank where

-- A syntax-only redex-rank bound for the intrinsic simple-type fragment.
-- Computing the bound does not evaluate typing or rank-uniqueness proofs.
open import PTSPrelude
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Nat.Order using (_≤_; ≤-trans)
open import BinderFreeCore using (Ty; ι; _⇒_)
open import SKSource using (Con; Source; var; ground; lam; app;
  erase; context; context-wf; erase-typed)
import BinderFreeBoundary as B
import BoundedReduction as R
import NativeTyping as T
import NativeRanks as Rank
import NativeSafety as Safety

private
  variable
    Γ : Con
    A : Ty

head-order : Source Γ A → Nat
head-order (var x) = 0
head-order (ground n) = 0
head-order (lam {A = A} {D = D} b) = B.order (A ⇒ D)
head-order (app f x) = 0

-- BEGINSKSOURCEBUDGET
budget : Source Γ A → Nat
budget (var x) = 0
budget (ground n) = 0
budget (lam b) = budget b
budget (app f x) = max (max (budget f) (budget x)) (head-order f)
-- ENDSKSOURCEBUDGET

private
  decode-safe : ∀ {n} (Δ : T.Context n) (A : Ty) (d : Nat)
    → Safety.RankSafe Δ (B.decode A) d
  decode-safe Δ ι d = tt
  decode-safe Δ (A ⇒ D) d = decode-safe Δ A d ,
    decode-safe (T.extend Δ (B.decode A)) D d

  head-bound : (t : Source Γ A) → Rank.IsLambda (erase t)
    → (r : Nat) → Rank.TypeRank (context Γ) (erase t) r → r ≤ head-order t
  head-bound (var x) () r hr
  head-bound (ground n) () r hr
  head-bound {Γ} (lam {A = A} {D = D} b) hl r hr =
    subst (λ q → q ≤ B.order (A ⇒ D))
      (sym (Rank.type-rank-unique (context-wf Γ) hr
        (B.decode (A ⇒ D) , erase-typed (lam b) , B.decode-sorted (context Γ) (A ⇒ D))))
      Cubical.Data.Nat.Order.≤-refl
  head-bound (app f x) () r hr

rank-safe : (t : Source Γ A) → Safety.RankSafe (context Γ) (erase t) (budget t)
rank-safe (var x) = tt
rank-safe (ground n) = tt
rank-safe {Γ} (lam {A = A} b) = decode-safe (context Γ) A (budget b) , rank-safe b
rank-safe (app f x) =
  Safety.safe-monotone (erase f) (rank-safe f)
    (≤-trans (Rank.max-left (budget f) (budget x))
      (Rank.max-left (max (budget f) (budget x)) (head-order f))) ,
  Safety.safe-monotone (erase x) (rank-safe x)
    (≤-trans (Rank.max-right (budget f) (budget x))
      (Rank.max-left (max (budget f) (budget x)) (head-order f))) ,
  λ hl r hr → ≤-trans (head-bound f hl r hr)
    (Rank.max-right (max (budget f) (budget x)) (head-order f))

redex-bound : (t : Source Γ A) → T.RedexBound (context Γ) (erase t) (budget t)
redex-bound t = Safety.safe-to-bound (rank-safe t)

neutral-head-zero : (t : Source Γ A) → R.NotLambda (erase t) → head-order t ≡ 0
neutral-head-zero (var x) h = refl
neutral-head-zero (ground n) h = refl
neutral-head-zero (lam b) ()
neutral-head-zero (app f x) h = refl

normal-budget-zero : (t : Source Γ A) → R.Normal (erase t) → budget t ≡ 0
normal-budget-zero (var x) h = refl
normal-budget-zero (ground n) h = refl
normal-budget-zero (lam b) h = normal-budget-zero b (snd h)
normal-budget-zero (app f x) h = cong₂ max
  (cong₂ max (normal-budget-zero f (fst h)) (normal-budget-zero x (fst (snd h))))
  (neutral-head-zero f (snd (snd h)))

normal-application-budget : ∀ {D} (f : Source Γ (A ⇒ D)) (x : Source Γ A)
  → R.Normal (erase f) → R.Normal (erase x) → budget (app f x) ≡ head-order f
normal-application-budget f x hf hx = cong (λ d → max d (head-order f))
  (cong₂ max (normal-budget-zero f hf) (normal-budget-zero x hx))
