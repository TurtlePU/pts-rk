{-# OPTIONS --cubical --safe --guardedness #-}
module SKSourceFast where

-- A syntax-only redex-rank bound for the intrinsic simple-type fragment.
-- Its computation never evaluates typing derivations or rank-uniqueness
-- proofs. The normalizer still traverses lambda source, not SK directly.
open import PTSPrelude
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Nat.Order using (_≤_; ≤-trans)
open import BinderFreeCore using (Ty; ι; _⇒_)
open import SKSource using (Con; ε; _▻_; Source; var; ground; lam; app;
  vz; vs; erase; context; context-wf; erase-typed; rounds; erase-rounds)
open import SKSourceEquality using (erase-injective)
import BinderFreeBoundary as B
import BoundedReduction as R
import NativeTyping as T
import NativeRanks as Rank
import NativeSafety as Safety
import NativeNormalization as N
import SKSourceNormal as Reference

private
  variable
    Γ : Con
    A : Ty

head-order : Source Γ A → Nat
head-order (var x) = 0
head-order (ground n) = 0
head-order (lam {A = A} {D = D} b) = B.order (A ⇒ D)
head-order (app f x) = 0

-- BEGIN SK FAST BUDGET
budget : Source Γ A → Nat
budget (var x) = 0
budget (ground n) = 0
budget (lam b) = budget b
budget (app f x) = max (max (budget f) (budget x)) (head-order f)

normalize : Source Γ A → Source Γ A
normalize t = rounds (budget t) t
-- END SK FAST BUDGET

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

reference : (t : Source Γ A)
  → N.Normalized (context Γ) (erase t) (B.decode A) (budget t)
reference {Γ} t = N.normalize (budget t) (context-wf Γ) (erase-typed t) (redex-bound t)

erase-reference : (t : Source Γ A) → erase (normalize t) ≡ N.nf (reference t)
erase-reference t = erase-rounds (budget t) t

normal : (t : Source Γ A) → R.Normal (erase (normalize t))
normal t = subst R.Normal (sym (erase-reference t)) (N.nf-normal (reference t))

reduces : (t : Source Γ A) → R.Steps (erase t) (erase (normalize t))
reduces t = SKSource.rounds-sound (budget t) t

-- Faster budget computation changes neither the source normal form nor
-- the retained annotations and hidden intrinsic application types.
agrees : (t : Source Γ A) → normalize t ≡ Reference.normalize t
agrees t = erase-injective (normalize t) (Reference.normalize t)
  (erase-reference t ∙ N.budget-independent (reference t) (Reference.reference t)
    ∙ sym (Reference.erase-native-reference t))

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

normalize-normal : (t : Source Γ A) → R.Normal (erase t) → normalize t ≡ t
normalize-normal t h = cong (λ d → rounds d t) (normal-budget-zero t h)

normal-application-budget : ∀ {D} (f : Source Γ (A ⇒ D)) (x : Source Γ A)
  → R.Normal (erase f) → R.Normal (erase x) → budget (app f x) ≡ head-order f
normal-application-budget f x hf hx = cong (λ d → max d (head-order f))
  (cong₂ max (normal-budget-zero f hf) (normal-budget-zero x hx))

identity-source : Source ε (ι ⇒ ι)
identity-source = lam (var vz)

identity-budget : budget identity-source ≡ 0
identity-budget = refl

identity-computes : normalize identity-source ≡ identity-source
identity-computes = refl

application-budget : budget (app identity-source (ground 7)) ≡ 1
application-budget = refl

application-computes : normalize (app identity-source (ground 7)) ≡ ground 7
application-computes = refl

under-lambda-computes : normalize
  (app (lam (lam {A = ι} (var (vs vz)))) (ground {Γ = ε} 7))
  ≡ lam (ground 7)
under-lambda-computes = refl

created-redex-computes : normalize
  (app (lam (app (var vz) (ground {Γ = ε ▻ (ι ⇒ ι)} 7)))
    (lam (var vz))) ≡ ground 7
created-redex-computes = refl
