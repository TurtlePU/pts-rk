{-# OPTIONS --cubical --safe --guardedness #-}
module FragmentModelSoundness where

-- All-six-rule contextual soundness from independently checked finite trees.
-- The resulting carriers are graded; this does not assert that a fixed
-- finite carrier is closed under the full first-order theory's operations.
open import FiniteSyntax
open import NativeTyping
open import NativeCertificates
open import CertificateContexts
open import NativeSubstitution using (typed-replace)
open import NativePreservation using (subject-reductions)
open import NativeConfluence using (normal-results-coherent)
open import NativeCanonicity using (Void; Void-empty)
open import NativeRanks using (max-left; max-right)
open import BoundedReduction using (replace; Steps)
open import FiniteBounds using (capacity; tower)
open import FiniteCarriers using (AtMost)
open import FragmentInterpretation
open import FragmentUniverses
open import FragmentPackages
open import AlphabetCoverage
open import Cubical.Data.FinData.Base using (toℕ)
open import Cubical.Data.Sigma.Base using (_×_)
open import Cubical.Foundations.Prelude using (subst2)
open import Cubical.Relation.Nullary using (Dec; yes; no)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Nat.Order using (_≤_; ≤-refl; ≤-trans)

-- BEGIN FRAGMENTMODELINPUT
record ModelInput (m n : Nat) : Set where
  field
    source : ContextCertificate m
    target : ContextCertificate n
    environment : ValuationCertificate m n
    derivation : Certificate m
open ModelInput public

InputAccepted : ∀ {m n} → ModelInput m n → Set
InputAccepted x = ContextAccepted (source x) × ContextAccepted (target x)
  × ValuationAccepted (certificate-context (source x))
      (certificate-context (target x)) (environment x)
  × Accepted (certificate-context (source x)) (derivation x)
-- END FRAGMENTMODELINPUT

private
  infixr 4 _×?_
  _×?_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
  yes p ×? yes q = yes (p , q)
  yes p ×? no q = no (λ h → q (snd h))
  no p ×? q = no (λ h → p (fst h))

input-accepted? : ∀ {m n} (x : ModelInput m n) → Dec (InputAccepted x)
input-accepted? x = context-accepted? (source x) ×? context-accepted? (target x)
  ×? valuation-accepted? (certificate-context (source x))
    (certificate-context (target x)) (environment x)
  ×? accepted? (certificate-context (source x)) (derivation x)

instantiated-term instantiated-type : ∀ {m n} → ModelInput m n → Term n
instantiated-term x = replace (valuation-images (environment x)) (certificate-term (derivation x))
instantiated-type x = replace (valuation-images (environment x)) (certificate-type (derivation x))

input-target-wf : ∀ {m n} {x : ModelInput m n}
  → InputAccepted x → WellFormed (certificate-context (target x))
input-target-wf {x = x} h = context-accepted-wf (target x) (fst (snd h))

-- Native typing is a derived conclusion; it is absent from InputAccepted.
input-typing : ∀ {m n} {x : ModelInput m n} → InputAccepted x
  → Typ (certificate-context (target x)) (instantiated-term x) (instantiated-type x)
input-typing {x = x} h = typed-replace
  (valuation-accepted-typed {Γ = certificate-context (source x)}
    {Δ = certificate-context (target x)} (environment x) (fst (snd (snd h))))
  (accepted-typing {Γ = certificate-context (source x)}
    {c = derivation x} (snd (snd (snd h))))

model-alphabet : ∀ {m n} → ModelInput m n → Nat
model-alphabet x = max (contextBound (certificate-context (target x)))
  (packetBound (instantiated-term x) (instantiated-type x))

private
  model-term-bound : ∀ {m n} (x : ModelInput m n)
    → labelBound (instantiated-term x) ≤ model-alphabet x
  model-term-bound x = ≤-trans (packet-term-bound (instantiated-term x) (instantiated-type x))
    (max-right (contextBound (certificate-context (target x)))
      (packetBound (instantiated-term x) (instantiated-type x)))

  model-type-bound : ∀ {m n} (x : ModelInput m n)
    → labelBound (instantiated-type x) ≤ model-alphabet x
  model-type-bound x = ≤-trans (packet-type-bound (instantiated-term x) (instantiated-type x))
    (max-right (contextBound (certificate-context (target x)))
      (packetBound (instantiated-term x) (instantiated-type x)))

model-term-code model-type-code : ∀ {m n} (x : ModelInput m n)
  → Raw (Fin (model-alphabet x)) n
model-term-code x = encode-under (instantiated-term x) (model-alphabet x) (model-term-bound x)
model-type-code x = encode-under (instantiated-type x) (model-alphabet x) (model-type-bound x)

model-term-recovers : ∀ {m n} (x : ModelInput m n)
  → relabel toℕ (model-term-code x) ≡ instantiated-term x
model-term-recovers x = encode-under-recovers (instantiated-term x) (model-alphabet x)
  (model-term-bound x)

model-type-recovers : ∀ {m n} (x : ModelInput m n)
  → relabel toℕ (model-type-code x) ≡ instantiated-type x
model-type-recovers x = encode-under-recovers (instantiated-type x) (model-alphabet x)
  (model-type-bound x)

-- BEGIN FRAGMENTMODELSOUNDNESS
ModelOutput : ∀ {m n} → ModelInput m n → Set
ModelOutput x = FiniteInterpretation toℕ (certificate-context (target x))
  (model-term-code x) (model-type-code x)

model-soundness : ∀ {m n} (x : ModelInput m n) → InputAccepted x → ModelOutput x
model-soundness x h = realize-typing toℕ (input-target-wf h)
  (model-term-code x) (model-type-code x)
  (subst2 (Typ (certificate-context (target x)))
    (sym (model-term-recovers x)) (sym (model-type-recovers x)) (input-typing h))
-- END FRAGMENTMODELSOUNDNESS

model-size : ∀ {m n} (x : ModelInput m n) → ModelOutput x → Nat
model-size x v = max (contextMaxNodes (certificate-context (target x)))
  (tower (depth v) (interpretationSeed (model-term-code x) (model-type-code x)))

-- Context, type and value are all counted, rather than ranging over an
-- unbounded external collection of contexts or type indices.
model-package : ∀ {m n} (x : ModelInput m n) (h : InputAccepted x) (v : ModelOutput x)
  → ContextElementPackage {model-alphabet x} toℕ n (model-size x v) (typeRank v)
model-package x h v = package-in-context (certificate-context (target x))
  (model-alphabet x) (model-size x v) (typeRank v)
  (max-left _ _) (max-left _ _) (input-target-wf h)
  (embedElement (max-right _ _) ≤-refl (element v))

model-package-finite : ∀ {m n} (x : ModelInput m n) (v : ModelOutput x)
  → AtMost (ContextElementPackage {model-alphabet x} toℕ n (model-size x v) (typeRank v))
      (contextCapacity (model-alphabet x) n (model-size x v) ·
        (capacity (model-alphabet x) n (model-size x v) ·
         capacity (model-alphabet x) n (model-size x v)))
model-package-finite x v = contextElementPackage-finite toℕ _ _ _

model-package-term : ∀ {m n} (x : ModelInput m n) (h : InputAccepted x) (v : ModelOutput x)
  → packageTerm (model-package x h v) ≡ nativeElement (element v)
model-package-term x h v = refl

model-package-type : ∀ {m n} (x : ModelInput m n) (h : InputAccepted x) (v : ModelOutput x)
  → packageType (model-package x h v) ≡ nativeElementType (element v)
model-package-type x h v = refl

model-package-context : ∀ {m n} (x : ModelInput m n) (h : InputAccepted x) (v : ModelOutput x)
  → packageContext (model-package x h v) ≡ certificate-context (target x)
model-package-context x h v = package-in-context-context (certificate-context (target x))
  (model-alphabet x) (model-size x v) (typeRank v)
  (max-left _ _) (max-left _ _) (input-target-wf h)
  (embedElement (max-right _ _) ≤-refl (element v))

-- Nothing means rejected certificate data, never failed normalization.
check-and-interpret : ∀ {m n} (x : ModelInput m n) → Maybe (ModelOutput x)
check-and-interpret x with input-accepted? x
... | yes accepted = just (model-soundness x accepted)
... | no _ = nothing

model-value : ∀ {m n} (x : ModelInput m n) → ModelOutput x → Term n
model-value x v = nativeElement (element v)

model-type : ∀ {m n} (x : ModelInput m n) → ModelOutput x → Term n
model-type x v = nativeElementType (element v)

model-reduces : ∀ {m n} (x : ModelInput m n) (v : ModelOutput x)
  → Steps (instantiated-term x) (model-value x v)
model-reduces x v = subst (λ t → Steps t (model-value x v))
  (model-term-recovers x) (term-reduces v)

model-type-reduces : ∀ {m n} (x : ModelInput m n) (v : ModelOutput x)
  → Steps (instantiated-type x) (model-type x v)
model-type-reduces x v = subst (λ t → Steps t (model-type x v))
  (model-type-recovers x) (type-reduces v)

-- Besides the jointly normalized type, the exact substituted source type
-- is retained by original subject reduction.
model-exact-typing : ∀ {m n} (x : ModelInput m n) (h : InputAccepted x)
  (v : ModelOutput x)
  → Typ (certificate-context (target x)) (model-value x v) (instantiated-type x)
model-exact-typing x h v = subject-reductions (input-target-wf h)
  (input-typing h) (model-reduces x v)

-- Grades, finite alphabets, derivation trees and target contexts may differ.
-- Equal/convertible instantiated subjects still have the same normal value.
model-coherent : ∀ {m k n} (x : ModelInput m n) (y : ModelInput k n)
  (v : ModelOutput x) (w : ModelOutput y)
  → Beta (instantiated-term x) (instantiated-term y)
  → model-value x v ≡ model-value y w
model-coherent x y v w e = normal-results-coherent e
  (model-reduces x v) (model-reduces y w)
  (elementCarrier-normal (element v)) (elementCarrier-normal (element w))

model-type-coherent : ∀ {m k n} (x : ModelInput m n) (y : ModelInput k n)
  (v : ModelOutput x) (w : ModelOutput y)
  → Beta (instantiated-type x) (instantiated-type y)
  → model-type x v ≡ model-type y w
model-type-coherent x y v w e = normal-results-coherent e
  (model-type-reduces x v) (model-type-reduces y w)
  (typeCarrier-normal (elementType (element v)))
  (typeCarrier-normal (elementType (element w)))

-- External checker consistency, not an inhabitant of an internal consistency
-- sentence and not a finite first-order model existence theorem.
private
  EmptyContextCase : (n : Nat) → Context n → Set
  EmptyContextCase zero Γ = Γ ≡ empty
  EmptyContextCase (suc n) Γ = Unit

  empty-context-case : ∀ {n} (Γ : Context n) → EmptyContextCase n Γ
  empty-context-case empty = refl
  empty-context-case (extend Γ A) = tt

  empty-context-unique : (Γ : Context zero) → Γ ≡ empty
  empty-context-unique = empty-context-case

model-Void-rejected : ∀ {m} (x : ModelInput m zero) → InputAccepted x
  → instantiated-type x ≡ Void → ⊥
model-Void-rejected x h e = Void-empty
  (subst (Typ empty (instantiated-term x)) e
    (subst (λ Γ → Typ Γ (instantiated-term x) (instantiated-type x))
      (empty-context-unique (certificate-context (target x))) (input-typing h)))
