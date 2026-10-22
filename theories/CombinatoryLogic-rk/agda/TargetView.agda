{-# OPTIONS --cubical --safe --guardedness #-}
module TargetView where

open import PTSPrelude
import Combinatory as C
open C using (Con; Ty; Tm; tyOf; ext)

-- A source-indexed view of the SAME substitutions, not a new QIIRT.
-- Sub Γ contains a target context together with a substitution into Γ.
Sub : Con → Set
Sub Γ = Σ Con (C.Sub Γ)

ctxOf : ∀ {Γ} → Sub Γ → Con
ctxOf = fst

indexed : ∀ {Γ} (σ : Sub Γ) → C.Sub Γ (ctxOf σ)
indexed = snd

forget : ∀ {Γ Δ} → C.Sub Γ Δ → Sub Γ
forget {Δ = Δ} σ = Δ , σ

-- Forgetting and recovering the inferred target loses no information.
forget-indexed : ∀ {Γ} (σ : Sub Γ) → forget (indexed σ) ≡ σ
forget-indexed σ = refl

indexed-forget : ∀ {Γ Δ} (σ : C.Sub Γ Δ) → indexed (forget σ) ≡ σ
indexed-forget σ = refl

identity : (Γ : Con) → Sub Γ
identity Γ = Γ , C.id

empty : ∀ {Γ} → Sub Γ
empty = C.empty , C.eps

-- Reordering dependent arguments keeps composition and substitution guard-free.
compose : ∀ {Γ} (σ : Sub Γ) → Sub (ctxOf σ) → Sub Γ
compose σ τ = ctxOf τ , C.comp (indexed τ) (indexed σ)

subTy : ∀ {Γ r} (σ : Sub Γ) → Ty (ctxOf σ) r → Ty Γ r
subTy σ A = C.subTy A (indexed σ)

subTm : ∀ {Γ} (σ : Sub Γ) → Tm (ctxOf σ) → Tm Γ
subTm σ t = C.subTm t (indexed σ)

extend : ∀ {Γ r} (σ : Sub Γ) (A : Ty (ctxOf σ) r) (t : Tm Γ)
       → tyOf t ≡ (r , subTy σ A) → Sub Γ
extend σ A t p = ext (ctxOf σ) A , C.pair (indexed σ) t p

-- To use a substitution at a previously fixed target, its target equality
-- must be supplied. This transport was absent from the doubly indexed API.
atTarget : ∀ {Γ Δ} (σ : Sub Γ) → ctxOf σ ≡ Δ → C.Sub Γ Δ
atTarget {Γ} σ p = subst (C.Sub Γ) p (indexed σ)

-- In particular, projections require evidence that the target is extended.
first : ∀ {Γ Δ r} {A : Ty Δ r} (σ : Sub Γ)
      → ctxOf σ ≡ ext Δ A → Sub Γ
first {Δ = Δ} σ p = Δ , C.fstS (atTarget σ p)

second : ∀ {Γ Δ r} {A : Ty Δ r} (σ : Sub Γ)
       → ctxOf σ ≡ ext Δ A → Tm Γ
second σ p = C.sndS (atTarget σ p)

-- The target computation itself is transparent, even for composition.
ctx-compose : ∀ {Γ} (σ : Sub Γ) (τ : Sub (ctxOf σ))
            → ctxOf (compose σ τ) ≡ ctxOf τ
ctx-compose σ τ = refl

ctx-extend : ∀ {Γ r} (σ : Sub Γ) (A : Ty (ctxOf σ) r) (t : Tm Γ)
             (p : tyOf t ≡ (r , subTy σ A))
           → ctxOf (extend σ A t p) ≡ ext (ctxOf σ) A
ctx-extend σ A t p = refl
