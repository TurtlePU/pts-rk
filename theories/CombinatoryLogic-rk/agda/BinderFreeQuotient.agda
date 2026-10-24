{-# OPTIONS --cubical --safe --guardedness #-}
module BinderFreeQuotient where

-- A genuine set quotient for the independent simply typed weak SK
-- calculus. It is NOT the dependent PTS QIIRT or native beta quotient.
open import BinderFreeCore
open import BinderFreeCoherence
open import BinderFreeEquality using (normal-discrete; normal-isSet)
open import Cubical.Foundations.Prelude
  using (_≡_; refl; sym; cong; _∙_)
open import Cubical.Foundations.Isomorphism using (Iso; iso)
open import Cubical.Relation.Nullary using (Dec; yes; no)
open import Cubical.Data.Bool using (Bool; true; false)
import Cubical.HITs.SetQuotients as Q

private
  variable
    A D : Ty

-- BEGINBINDERFREEQUOTIENT
Quotient : Ty → Set
Quotient A = Tm A Q./ WeakConversion

normalizeQ : Quotient A → Nf A
normalizeQ = Q.rec normal-isSet nf (λ _ _ → conversion-coherent)

quoteQ : Nf A → Quotient A
quoteQ n = Q.[ erase n ]

normalize-quote : (n : Nf A) → normalizeQ (quoteQ n) ≡ n
normalize-quote = nf-erase

quote-normalize : (q : Quotient A) → quoteQ (normalizeQ q) ≡ q
quote-normalize = Q.elimProp (λ q → Q.squash/ _ _)
  (λ t → sym (Q.eq/ t (erase (nf t)) (steps-conversion (nf-sound t))))

quotient-normal-iso : Iso (Quotient A) (Nf A)
quotient-normal-iso = iso normalizeQ quoteQ normalize-quote quote-normalize
-- ENDBINDERFREEQUOTIENT

-- The same normalizing application supplies the quotient's total operation.
applyQ : Quotient (A ⇒ D) → Quotient A → Quotient D
applyQ f x = quoteQ (appNF (normalizeQ f) (normalizeQ x))

applyQ-represents : (f : Tm (A ⇒ D)) (x : Tm A)
  → applyQ Q.[ f ] Q.[ x ] ≡ Q.[ f · x ]
applyQ-represents f x = quote-normalize Q.[ f · x ]

weak-conversion? : (t u : Tm A) → Dec (WeakConversion t u)
weak-conversion? t u with normal-discrete (nf t) (nf u)
... | yes p = yes (conversion-reflects p)
... | no bad = no (λ p → bad (conversion-coherent p))

quotient-equality? : (p q : Quotient A) → Dec (p ≡ q)
quotient-equality? p q with normal-discrete (normalizeQ p) (normalizeQ q)
... | yes eq = yes
  (sym (quote-normalize p) ∙ cong quoteQ eq ∙ quote-normalize q)
... | no bad = no (λ eq → bad (cong normalizeQ eq))

regression-quotient-identity : normalizeQ
  (applyQ Q.[ identity ] Q.[ ground 7 ]) ≡ lit 7
regression-quotient-identity = refl

private
  accepts : ∀ {P : Set} → Dec P → Bool
  accepts (yes _) = true
  accepts (no _) = false

regression-conversion-identity :
  accepts (weak-conversion? (identity · ground 7) (ground 7)) ≡ true
regression-conversion-identity = refl

-- Exactly the extra native-beta identification witnessed in Boundary is
-- deliberately absent from this smaller weak combinatory quotient.
regression-distinct-identities :
  accepts (weak-conversion? (S · K {ι} {ι} · identity) identity) ≡ false
regression-distinct-identities = refl
