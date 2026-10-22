{-# OPTIONS --cubical --safe --guardedness #-}
module CertificateContexts where

-- Independent context and valuation certificates for contextual soundness.
-- Context validity and typed substitution are conclusions of checking,
-- never native judgments stored in the input certificate data.
open import PTSPrelude
open import FiniteSyntax
open import BoundedReduction using (replace)
open import NativeTyping
open import NativeCertificates
open import NativeSubstitution using (TypedSub)
open import NativeAlgebra using (fin-cases)
open import Cubical.Data.Sigma.Base using (_×_)
open import Cubical.Data.Unit using (Unit; tt; isPropUnit)
open import Cubical.Relation.Nullary using (Dec; yes; no; Discrete→isSet)
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Foundations.Prelude using (isProp)
open import Cubical.Foundations.HLevels using (isProp×; isPropΠ)

private
  variable
    m n : Nat

-- BEGIN CONTEXTCERTIFICATE
data ContextCertificate : Nat → Set where
  empty-context : ContextCertificate zero
  extend-context : ContextCertificate n → Term n → Nat
    → Certificate n → ContextCertificate (suc n)

certificate-context : ContextCertificate n → Context n
certificate-context empty-context = empty
certificate-context (extend-context Γ A r p) = extend (certificate-context Γ) A

ContextAccepted : ContextCertificate n → Set
ContextAccepted empty-context = Unit
ContextAccepted (extend-context Γ A r p) = ContextAccepted Γ
  × Accepted (certificate-context Γ) p × Matches p A (U r)

context-accepted-wf : (Γ : ContextCertificate n) → ContextAccepted Γ
  → WellFormed (certificate-context Γ)
context-accepted-wf empty-context h = wf-empty
context-accepted-wf (extend-context Γ A r p) (hΓ , hp , match) =
  wf-extend (context-accepted-wf Γ hΓ) (accepted-at hp match)
-- END CONTEXTCERTIFICATE

certify-context : {Γ : Context n} → WellFormed Γ
  → Σ (ContextCertificate n) (λ c → ContextAccepted c × (certificate-context c ≡ Γ))
certify-context wf-empty = empty-context , tt , refl
certify-context (wf-extend {A = A} {r} wf p) with certify-context wf | certify p
... | c , hc , ec | d , hd , md =
  extend-context c A r d ,
    (hc , subst (λ Γ → Accepted Γ d) (sym ec) hd , md) ,
    cong (λ Γ → extend Γ A) ec

private
  infixr 4 _×?_
  _×?_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
  yes p ×? yes q = yes (p , q)
  yes p ×? no nq = no (λ z → nq (snd z))
  no np ×? q = no (λ z → np (fst z))

context-accepted? : (Γ : ContextCertificate n) → Dec (ContextAccepted Γ)
context-accepted? empty-context = yes tt
context-accepted? (extend-context Γ A r p) = context-accepted? Γ
  ×? accepted? (certificate-context Γ) p ×? matches? p A (U r)

-- BEGIN VALUATIONCERTIFICATE
record ValuationCertificate (m n : Nat) : Set where
  constructor valuation-certificate
  field
    valuation-images : Fin m → Term n
    valuation-proofs : Fin m → Certificate n
open ValuationCertificate public

ValuationAccepted : Context m → Context n → ValuationCertificate m n → Set
ValuationAccepted Γ Δ c = ∀ i → Accepted Δ (valuation-proofs c i)
  × Matches (valuation-proofs c i) (valuation-images c i)
      (replace (valuation-images c) (lookup Γ i))

valuation-accepted-typed : {Γ : Context m} {Δ : Context n}
  (c : ValuationCertificate m n) → ValuationAccepted Γ Δ c
  → TypedSub Γ Δ (valuation-images c)
valuation-accepted-typed c h i = accepted-at (fst (h i)) (snd (h i))
-- END VALUATIONCERTIFICATE

certify-valuation : {Γ : Context m} {Δ : Context n} {σ : Fin m → Term n}
  → TypedSub Γ Δ σ
  → Σ (ValuationCertificate m n) (λ c → ValuationAccepted Γ Δ c × (valuation-images c ≡ σ))
certify-valuation {σ = σ} h =
  valuation-certificate σ (λ i → fst (certify (h i))) ,
    (λ i → fst (snd (certify (h i))) , snd (snd (certify (h i)))) , refl

private
  all-fin? : {P : Fin m → Set} → (∀ i → Dec (P i)) → Dec (∀ i → P i)
  all-fin? {m = zero} p = yes (λ ())
  all-fin? {m = suc m} {P} p with p fzero | all-fin? (λ i → p (fsuc i))
  ... | yes p0 | yes ps = yes (λ i → fin-cases P i p0 ps)
  ... | yes p0 | no nps = no (λ h → nps (λ i → h (fsuc i)))
  ... | no np0 | ps = no (λ h → np0 (h fzero))

valuation-accepted? : (Γ : Context m) (Δ : Context n) (c : ValuationCertificate m n)
  → Dec (ValuationAccepted Γ Δ c)
valuation-accepted? Γ Δ c = all-fin? (λ i → accepted? Δ (valuation-proofs c i)
  ×? matches? (valuation-proofs c i) (valuation-images c i)
      (replace (valuation-images c) (lookup Γ i)))

-- The acceptance checker also handles empty contexts and empty valuations.
empty-valuation : ValuationCertificate zero n
empty-valuation = valuation-certificate (λ ()) (λ ())

empty-valuation-accepted : (Δ : Context n) → ValuationAccepted empty Δ empty-valuation
empty-valuation-accepted Δ ()

private
  match-prop : (c : Certificate n) (t A : Term n) → isProp (Matches c t A)
  match-prop c t A = isProp× (Discrete→isSet term-discrete _ _)
    (Discrete→isSet term-discrete _ _)

context-accepted-isProp : (Γ : ContextCertificate n) → isProp (ContextAccepted Γ)
context-accepted-isProp empty-context = isPropUnit
context-accepted-isProp (extend-context Γ A r p) = isProp× (context-accepted-isProp Γ)
  (isProp× (accepted-isProp (certificate-context Γ) p) (match-prop p A (U r)))

valuation-accepted-isProp : (Γ : Context m) (Δ : Context n) (c : ValuationCertificate m n)
  → isProp (ValuationAccepted Γ Δ c)
valuation-accepted-isProp Γ Δ c = isPropΠ (λ i → isProp×
  (accepted-isProp Δ (valuation-proofs c i))
  (match-prop (valuation-proofs c i) (valuation-images c i)
    (replace (valuation-images c) (lookup Γ i))))

-- Executable regressions distinguish checking raw evidence from assuming
-- the desired typing judgment. The invalid variable has the wrong type.
private
  answer : ∀ {A : Set} → Dec A → Bool
  answer (yes p) = true
  answer (no p) = false

identity-certificate : Certificate zero
identity-certificate = abstraction-rule (U zero) (var fzero) (U zero) zero
  (sort-rule zero) (variable-rule fzero (U zero))

identity-accepted-by-checker : answer (accepted? empty identity-certificate) ≡ true
identity-accepted-by-checker = refl

wrong-variable-rejected :
  answer (accepted? (extend empty (U zero)) (variable-rule fzero (U 1))) ≡ false
wrong-variable-rejected = refl

one-variable-context : ContextCertificate 1
one-variable-context = extend-context empty-context (U zero) zero (sort-rule zero)

one-variable-context-checked : answer (context-accepted? one-variable-context) ≡ true
one-variable-context-checked = refl
