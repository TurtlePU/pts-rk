{-# OPTIONS --cubical --safe --guardedness #-}
module SKDirectSoundness where

-- Direct weak SK evaluation has forward ORIGINAL beta semantics. This
-- bridge does not assert that weak normal forms are native-beta canonical.
open import PTSPrelude
import BinderFreeCore as SK
import BinderFreeCoherence as Weak
import BinderFreeBoundary as B
import BinderFreeQuotient as WQ
import SKBracket as Bracket
import SKCanonical as Canonical
import SKNativeCanonical as NQ
import BoundedReduction as R
import NativeTyping as T
open import NativeConfluence using (steps-beta)
import Cubical.HITs.SetQuotients as Q

private
  variable
    n : Nat
    A D E : SK.Ty

step-expands : ∀ {t u : SK.Tm A} → t SK.↝ u
  → R.Steps (B.expand {n} t) (B.expand u)
step-expands (SK.βS {A = A} {D = D} {E = E} f g x) =
  Bracket.s-applied {A = A} {D = D} {E = E} (B.expand f) (B.expand g) (B.expand x)
step-expands (SK.βK {A = A} {D = D} x y) =
  Bracket.k-applied {A = A} {D = D} (B.expand x) (B.expand y)
step-expands (SK.left p) = R.steps-app (step-expands p) R.done
step-expands (SK.right p) = R.steps-app R.done (step-expands p)

steps-expand : ∀ {t u : SK.Tm A} → t SK.↠ u
  → R.Steps (B.expand {n} t) (B.expand u)
steps-expand SK.done = R.done
steps-expand (SK.step p ps) = R.steps-trans (step-expands p) (steps-expand ps)

weak-to-native : ∀ {t u : SK.Tm A} → Weak.WeakConversion t u
  → T.Beta (B.expand {n} t) (B.expand u)
weak-to-native Weak.conv-refl = T.beta-refl
weak-to-native (Weak.conv-step p) = steps-beta (step-expands p)
weak-to-native (Weak.conv-sym p) = T.beta-sym (weak-to-native p)
weak-to-native (Weak.conv-trans p q) = T.beta-trans (weak-to-native p) (weak-to-native q)

-- Neither computational projection below constructs lambda source syntax.
direct : SK.Tm A → SK.Tm A
direct t = SK.erase (Weak.nf t)

direct-expands : (t : SK.Tm A) → R.Steps (B.expand {n} t) (B.expand (direct t))
direct-expands t = steps-expand (Weak.nf-sound t)

apply-normal-expands : (f : SK.Nf (A SK.⇒ D)) (x : SK.Nf A)
  → R.Steps (B.expand {n} (SK.erase f SK.· SK.erase x))
      (B.expand (SK.erase (Weak.appNF f x)))
apply-normal-expands f x = steps-expand
  (SK.application-sound (Weak.appNF-evaluates f x))

direct-typed : (t : SK.Tm A) → T.Typ T.empty (B.expand (direct t)) (B.decode A)
direct-typed t = B.expand-typed T.empty (direct t)

apply-normal-typed : (f : SK.Nf (A SK.⇒ D)) (x : SK.Nf A)
  → T.Typ T.empty (B.expand (SK.erase (Weak.appNF f x))) (B.decode D)
apply-normal-typed f x = B.expand-typed T.empty (SK.erase (Weak.appNF f x))

-- Direct weak reduction can safely precede the stronger reference. The
-- right-hand canonicalization still uses lambda syntax internally.
canonical-after-direct : (t : SK.Tm A)
  → Canonical.normalize t ≡ Canonical.normalize (direct t)
canonical-after-direct t = Canonical.coherent t (direct t)
  (steps-beta (direct-expands t))

canonical-after-apply : (f : SK.Nf (A SK.⇒ D)) (x : SK.Nf A)
  → Canonical.normalize (SK.erase f SK.· SK.erase x)
    ≡ Canonical.normalize (SK.erase (Weak.appNF f x))
canonical-after-apply f x = Canonical.coherent _ _
  (steps-beta (apply-normal-expands f x))

-- The actual quotient map forgets only the extra distinctions of weak SK
-- conversion; it preserves application, but need not be injective.
forgetQ : WQ.Quotient A → NQ.Quotient A
forgetQ = Q.rec Q.squash/ (λ t → Q.[ t ])
  (λ t u e → Q.eq/ t u (weak-to-native e))

forgetQ-apply : (f : WQ.Quotient (A SK.⇒ D)) (x : WQ.Quotient A)
  → forgetQ (WQ.applyQ f x) ≡ NQ.applyQ (forgetQ f) (forgetQ x)
forgetQ-apply = Q.elimProp2 (λ _ _ → Q.squash/ _ _)
  (λ f x → cong forgetQ (WQ.applyQ-represents f x))

direct-idempotent : (t : SK.Tm A) → direct (direct t) ≡ direct t
direct-idempotent t = cong SK.erase (Weak.nf-erase (Weak.nf t))

regression-direct-identity : direct (SK.identity SK.· SK.ground 7) ≡ SK.ground 7
regression-direct-identity = refl
