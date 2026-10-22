{-# OPTIONS --cubical --safe --guardedness #-}
module FragmentMachineSoundness where

-- Soundness of the actual finite-state executor on originally typed inputs.
open import FiniteSyntax
open import FiniteBounds using (tower)
open import FiniteTrace using (State; decode-state)
open import FiniteMachine
open import NativeTyping
open import NativeNormalization
open import NativeDescent using (normal-application-rank-bound)
open import BoundedReduction using (Normal; Steps; relabel-rounds; substitute)
open import BoundedTrace using (BoundedSteps)
open import Cubical.Data.Nat.Order using (_≤_)

private
  realize : ∀ {n Γ t T d} (v : Normalized {n} Γ t T d)
    (u : Term n) → u ≡ nf v → Normalized Γ t T d
  realize {Γ = Γ} {t} {T} {d} v u e = normalized u
    (subst Normal (sym e) (nf-normal v))
    (subst (λ w → Typ Γ w T) (sym e) (nf-typed v))
    (subst (Steps t) (sym e) (nf-reduces v))
    (subst (λ w → RedexBound Γ w d) (sym e) (nf-bound v))
    (subst (λ w → nodes w ≤ tower d (nodes t)) (sym e) (nf-size v))
    (subst (BoundedSteps (tower d (nodes t)) t) (sym e) (nf-trace v))

-- Every pass operates on State a n (tower d N). The node-budget premise
-- rules out clipping; the original rank premise proves final normality.
finite-normalize : ∀ {a n Γ T} (labels : Fin a → Nat) (d N : Nat)
  (t : Raw (Fin a) n) (small : nodes t ≤ N)
  → WellFormed Γ → Typ Γ (relabel labels t) T
  → RedexBound Γ (relabel labels t) d
  → Normalized Γ (relabel labels t) T d
finite-normalize {a} {n} labels d N t small wf ht rank =
  realize (normalize d wf ht rank)
    (relabel labels (decode-state {a} {n} {tower d N} (run-bounded d N t small)))
    (cong (relabel labels) (run-bounded-correct d N t small) ∙ relabel-rounds labels d t)

finite-normalize-computes : ∀ {a n Γ T} (labels : Fin a → Nat) (d N : Nat)
  (t : Raw (Fin a) n) (small : nodes t ≤ N) (wf : WellFormed Γ)
  (ht : Typ Γ (relabel labels t) T) (rank : RedexBound Γ (relabel labels t) d)
  → nf (finite-normalize labels d N t small wf ht rank)
      ≡ relabel labels (decode-state {a} {n} {tower d N} (run-bounded d N t small))
finite-normalize-computes labels d N t small wf ht rank = refl

-- The application constructor and all passes use the same finite carrier.
-- The returned certificate includes exact Y[y], forward reduction, rank,
-- normality and a bounded single-beta trace, not merely raw table agreement.
finite-apply : ∀ {a s X Y} (labels : Fin a → Nat) (d : Nat)
  (i j : State a 0 s)
  → tower d (nodes (app (decode-state {a} {0} {s} i) (decode-state {a} {0} {s} j))) ≤ s
  → Typ empty (relabel labels (decode-state {a} {0} {s} i)) (pi X Y)
  → Typ empty (relabel labels (decode-state {a} {0} {s} j)) X
  → Typ empty (pi X Y) (U d)
  → Normal (relabel labels (decode-state {a} {0} {s} i))
  → Normal (relabel labels (decode-state {a} {0} {s} j))
  → Normalized empty
      (app (relabel labels (decode-state {a} {0} {s} i))
           (relabel labels (decode-state {a} {0} {s} j)))
      (substitute Y (relabel labels (decode-state {a} {0} {s} j))) d
finite-apply {a} {s} labels d i j small hf hy hp nf ny =
  realize (normalize d wf-empty (application hf hy)
    (normal-application-rank-bound wf-empty nf ny (_ , hf , hp)))
    (relabel labels (decode-state {a} {0} {s} (apply-state {a} {0} {s} d i j)))
    (cong (relabel labels) (apply-state-correct {a} {0} {s} d i j small)
      ∙ relabel-rounds labels d _)

finite-apply-computes : ∀ {a s X Y} (labels : Fin a → Nat) (d : Nat)
  (i j : State a 0 s)
  (small : tower d (nodes (app (decode-state {a} {0} {s} i)
    (decode-state {a} {0} {s} j))) ≤ s)
  (hf : Typ empty (relabel labels (decode-state {a} {0} {s} i)) (pi X Y))
  (hy : Typ empty (relabel labels (decode-state {a} {0} {s} j)) X)
  (hp : Typ empty (pi X Y) (U d))
  (nf : Normal (relabel labels (decode-state {a} {0} {s} i)))
  (ny : Normal (relabel labels (decode-state {a} {0} {s} j)))
  → NativeNormalization.nf (finite-apply labels d i j small hf hy hp nf ny)
      ≡ relabel labels (decode-state {a} {0} {s} (apply-state {a} {0} {s} d i j))
finite-apply-computes labels d i j small hf hy hp nf ny = refl
