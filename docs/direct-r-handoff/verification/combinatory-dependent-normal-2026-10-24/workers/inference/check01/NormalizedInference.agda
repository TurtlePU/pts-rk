{-# OPTIONS --cubical --safe --guardedness #-}
module NormalizedInference where

-- Computed types for normal terms of the ORIGINAL dependent PTS.
-- The input carries mere typability, not a chosen type or typing derivation.
-- This is a normal-form-first semantic interface, not raw type inference.
open import PTSPrelude
open import BoundedReduction
open import NativeTyping
open import NativeInversion using (uniqueness; beta-path)
open import NativePreservation using (type-correct; type-stability)
open import NativeConfluence using (sort-injective; steps-beta; normal-beta-unique)
open import NativeNormalization
open import NativeRankCoverage using (normalize-typed)
open import NativeCertificates using (term-discrete)
import NormalizedFamilies as NF
open import Cubical.Data.Sigma using (_×_; Σ≡Prop)
open import Cubical.Foundations.Prelude using (isProp→isSet)
open import Cubical.Foundations.HLevels using (isProp×; isSetRetract)
open import Cubical.Foundations.Isomorphism using (Iso; iso)
open import Cubical.Relation.Nullary using (Dec; yes; no; Discrete→isSet)
open import Cubical.Data.Empty using (isProp⊥)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; ∣_∣₁; squash₁)
import Cubical.HITs.PropositionalTruncation as PT

private
  variable
    n : Nat

-- BEGINNORMALCOMPUTED
record Tm (Γ : Context n) : Set where
  constructor normal-term
  field
    body : Term n
    body-normal : Normal body
    typable : ∥ Σ (Term n) (λ A → Typ Γ body A) ∥₁
open Tm public
-- ENDNORMALCOMPUTED

private
  term-set : isSet (Term n)
  term-set = Discrete→isSet term-discrete

tm-view : {Γ : Context n} → Tm Γ
  → Σ (Term n) (λ t → Normal t × ∥ Σ (Term n) (λ A → Typ Γ t A) ∥₁)
tm-view (normal-term t nt ht) = t , nt , ht

tm-from-view : {Γ : Context n}
  → Σ (Term n) (λ t → Normal t × ∥ Σ (Term n) (λ A → Typ Γ t A) ∥₁)
  → Tm Γ
tm-from-view (t , nt , ht) = normal-term t nt ht

tm-path : {Γ : Context n} {t u : Tm Γ} → body t ≡ body u → t ≡ u
tm-path {t = t} {u} p = cong tm-from-view
  (Σ≡Prop (λ _ → isProp× normal-isProp squash₁)
    {u = tm-view t} {v = tm-view u} p)

tm-isSet : {Γ : Context n} → isSet (Tm Γ)
tm-isSet = isSetRetract tm-view tm-from-view (λ _ → refl)
  (isSetΣ term-set (λ _ → isProp→isSet (isProp× normal-isProp squash₁)))

private
  result : {Γ : Context n} {t A : Term n}
    → (wf : WellFormed Γ) → (p : Typ Γ t A) → _
  result wf p = normalize-typed wf (snd (type-correct wf p))

  choice : {Γ : Context n} (wf : WellFormed Γ) (t : Term n)
    → Σ (Term n) (λ A → Typ Γ t A) → Nat × Term n
  choice wf t (A , p) = fst (type-correct wf p) , nf (result wf p)

  choice-coherent : {Γ : Context n} (wf : WellFormed Γ) (t : Term n)
    (p q : Σ (Term n) (λ A → Typ Γ t A))
    → choice wf t p ≡ choice wf t q
  choice-coherent wf t (A , p) (B , q) = cong₂ _,_
    (sort-injective (type-stability wf
      (snd (type-correct wf p)) (snd (type-correct wf q)) (uniqueness p q)))
    (normalization-coherent (result wf p) (result wf q) (uniqueness p q))

  recover : {Γ : Context n} (wf : WellFormed Γ) (t : Term n)
    → ∥ Σ (Term n) (λ A → Typ Γ t A) ∥₁ → Nat × Term n
  recover wf t = PT.rec→Set (isSetΣ isSetℕ (λ _ → term-set))
    (choice wf t) (choice-coherent wf t)

-- Neither projection depends on a chosen typing witness. Rank is the
-- universe rank of the computed type, not an asserted redex-rank bound.
rankOf : {Γ : Context n} → WellFormed Γ → Tm Γ → Nat
rankOf wf t = fst (recover wf (body t) (typable t))

tyOf : {Γ : Context n} → WellFormed Γ → Tm Γ → Term n
tyOf wf t = snd (recover wf (body t) (typable t))

type-normal : {Γ : Context n} (wf : WellFormed Γ) (t : Tm Γ)
  → Normal (tyOf wf t)
type-normal wf t = PT.elim
  {P = λ h → Normal (snd (recover wf (body t) h))}
  (λ _ → normal-isProp) (λ { (A , p) → nf-normal (result wf p) }) (typable t)

type-sorted : {Γ : Context n} (wf : WellFormed Γ) (t : Tm Γ)
  → ∥ Typ Γ (tyOf wf t) (U (rankOf wf t)) ∥₁
type-sorted {Γ = Γ} wf t = PT.elim
  {P = λ h → ∥ Typ Γ (snd (recover wf (body t) h))
    (U (fst (recover wf (body t) h))) ∥₁}
  (λ _ → squash₁) (λ { (A , p) → ∣ nf-typed (result wf p) ∣₁ }) (typable t)

has-type : {Γ : Context n} (wf : WellFormed Γ) (t : Tm Γ)
  → ∥ Typ Γ (body t) (tyOf wf t) ∥₁
has-type {Γ = Γ} wf t = PT.elim
  {P = λ h → ∥ Typ Γ (body t) (snd (recover wf (body t) h)) ∥₁}
  (λ _ → squash₁) (λ { (A , p) → ∣ conversion p
    (nf-typed (result wf p)) (steps-beta (nf-reduces (result wf p))) ∣₁ }) (typable t)

computed-type : {Γ : Context n} (wf : WellFormed Γ) (t : Tm Γ)
  → NF.TyNF Γ (rankOf wf t)
computed-type wf t = NF.normal-at (tyOf wf t) (type-normal wf t) (type-sorted wf t)

-- The type is characterized among normal original types, not by an
-- independent checking judgment. No completeness premise is introduced.
type-characterization : {Γ : Context n} (wf : WellFormed Γ) (t : Tm Γ)
  {A : Term n} → Normal A → Typ Γ (body t) A → tyOf wf t ≡ A
type-characterization {Γ = Γ} wf t {A} nA p = PT.elim
  {P = λ h → snd (recover wf (body t) h) ≡ A}
  (λ _ → term-set _ _) (λ { (B , q) →
    normal-convertible-unique (result wf q) nA (uniqueness q p) }) (typable t)

from-normal : {Γ : Context n} {A : Term n} → NF.NfAt Γ A → Tm Γ
from-normal {A = A} t = normal-term (NF.term t) (NF.normal t)
  (PT.map (λ p → A , p) (NF.typed t))

TmAt : {Γ : Context n} (wf : WellFormed Γ) → Term n → Set
TmAt {Γ = Γ} wf A = Σ (Tm Γ) (λ t → tyOf wf t ≡ A)

embed : {Γ : Context n} (wf : WellFormed Γ) {A : Term n}
  → Normal A → NF.NfAt Γ A → TmAt wf A
embed wf nA t = from-normal t , PT.rec (term-set _ _)
  (type-characterization wf (from-normal t) nA) (NF.typed t)

at : {Γ : Context n} (wf : WellFormed Γ) {A : Term n}
  → TmAt wf A → NF.NfAt Γ A
at {Γ = Γ} wf (t , e) = NF.normal-at (body t) (body-normal t)
  (subst (λ A → ∥ Typ Γ (body t) A ∥₁) e (has-type wf t))

at-embed : {Γ : Context n} (wf : WellFormed Γ) {A : Term n}
  (nA : Normal A) (t : NF.NfAt Γ A) → at wf (embed wf nA t) ≡ t
at-embed wf nA t = NF.nf-path refl

embed-at : {Γ : Context n} (wf : WellFormed Γ) {A : Term n}
  (nA : Normal A) (t : TmAt wf A) → embed wf nA (at wf t) ≡ t
embed-at wf nA (t , e) = Σ≡Prop (λ _ → term-set _ _) (tm-path refl)

fibre-iso : {Γ : Context n} (wf : WellFormed Γ) {A : Term n}
  → Normal A → Iso (NF.NfAt Γ A) (TmAt wf A)
fibre-iso wf nA = iso (embed wf nA) (at wf) (embed-at wf nA) (at-embed wf nA)

conversion? : {Γ : Context n} (t u : Tm Γ) → Dec (Beta (body t) (body u))
conversion? t u with term-discrete (body t) (body u)
... | yes p = yes (beta-path p)
... | no bad = no (λ e → bad (normal-beta-unique (body-normal t) (body-normal u) e))

equality? : {Γ : Context n} (t u : Tm Γ) → Dec (t ≡ u)
equality? t u with term-discrete (body t) (body u)
... | yes p = yes (tm-path p)
... | no bad = no (λ p → bad (cong body p))

-- Checking against a normal type is decidable for an ALREADY typable
-- normal subject. This does not claim decision of raw untyped typability.
check-type? : {Γ : Context n} (wf : WellFormed Γ) (t : Tm Γ)
  (A : Term n) → Normal A → Dec ∥ Typ Γ (body t) A ∥₁
check-type? {Γ = Γ} wf t A nA with term-discrete (tyOf wf t) A
... | yes e = yes (subst (λ A → ∥ Typ Γ (body t) A ∥₁) e (has-type wf t))
... | no bad = no (PT.rec isProp⊥ (λ p → bad (type-characterization wf t nA p)))
