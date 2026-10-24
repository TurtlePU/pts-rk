{-# OPTIONS --cubical --safe --guardedness #-}
module NormalizedFamilies where

-- Normal families over the ORIGINAL dependent PTS. Only typing witnesses
-- are truncated; equality is equality of normal annotated syntax.
open import PTSPrelude
open import BoundedReduction
open import NativeTyping
open import NativeAlgebra using (replace-id; replace-compose; beta-replace)
open import NativeSubstitution using (typed-replace)
open import NativeInversion using (beta-path)
open import NativeConfluence using (steps-beta; normal-beta-unique)
open import NativeRankCoverage using (normalize-typed)
open import NativeNormalization
open import NativeCertificates using (term-discrete)
open import NativeValuations using (valuation; compose; equivalent-action)
open import NormalizedSubstitution
open import Cubical.Data.Sigma using (_×_; Σ≡Prop)
open import Cubical.Foundations.Prelude using (isProp→isSet; subst-filler)
open import Cubical.Foundations.HLevels using (isProp×; isSetRetract)
open import Cubical.Relation.Nullary using (Discrete→isSet)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; ∣_∣₁; squash₁)
import Cubical.HITs.PropositionalTruncation as PT

private
  variable
    l m n r : Nat

-- BEGINNORMALFAMILIES
record NfAt (Γ : Context n) (A : Term n) : Set where
  constructor normal-at
  field
    term : Term n
    normal : Normal term
    typed : ∥ Typ Γ term A ∥₁
open NfAt public

TyNF : Context n → Nat → Set
TyNF Γ r = NfAt Γ (U r)
-- ENDNORMALFAMILIES

private
  nf-view : {Γ : Context n} {A : Term n} → NfAt Γ A
    → Σ (Term n) (λ t → Normal t × ∥ Typ Γ t A ∥₁)
  nf-view (normal-at t nt ht) = t , nt , ht

  nf-from-view : {Γ : Context n} {A : Term n}
    → Σ (Term n) (λ t → Normal t × ∥ Typ Γ t A ∥₁) → NfAt Γ A
  nf-from-view (t , nt , ht) = normal-at t nt ht

nf-path : {Γ : Context n} {A : Term n} {t u : NfAt Γ A}
  → term t ≡ term u → t ≡ u
nf-path {t = t} {u} e = cong nf-from-view
  (Σ≡Prop (λ _ → isProp× normal-isProp squash₁)
    {u = nf-view t} {v = nf-view u} e)

nf-isSet : {Γ : Context n} {A : Term n} → isSet (NfAt Γ A)
nf-isSet = isSetRetract nf-view nf-from-view (λ _ → refl)
  (isSetΣ (Discrete→isSet term-discrete)
    (λ _ → isProp→isSet (isProp× normal-isProp squash₁)))

normalizeAt : {Γ : Context n} {t A : Term n}
  → WellFormed Γ → Typ Γ t A → NfAt Γ A
normalizeAt wf ht = normal-at (nf result) (nf-normal result) ∣ nf-typed result ∣₁
  where result = normalize-typed wf ht

normalizeAt-coherent : {Γ : Context n} {t u A : Term n}
  (wf wf′ : WellFormed Γ) (ht : Typ Γ t A) (hu : Typ Γ u A)
  → Beta t u → normalizeAt wf ht ≡ normalizeAt wf′ hu
normalizeAt-coherent wf wf′ ht hu p = nf-path
  (normalization-coherent (normalize-typed wf ht) (normalize-typed wf′ hu) p)

normalizeAt-reflects : {Γ : Context n} {t u A : Term n}
  (wf wf′ : WellFormed Γ) (ht : Typ Γ t A) (hu : Typ Γ u A)
  → normalizeAt wf ht ≡ normalizeAt wf′ hu → Beta t u
normalizeAt-reflects wf wf′ ht hu p = normalization-reflects
  (normalize-typed wf ht) (normalize-typed wf′ hu) (cong term p)

normalizeProof : {Γ : Context n} {t A : Term n}
  → WellFormed Γ → ∥ Typ Γ t A ∥₁ → NfAt Γ A
normalizeProof wf = PT.rec→Set nf-isSet (normalizeAt wf)
  (λ ht hu → normalizeAt-coherent wf wf ht hu beta-refl)

normalizeProof-sound : {Γ : Context n} {t A : Term n}
  (wf : WellFormed Γ) (ht : ∥ Typ Γ t A ∥₁)
  → ∥ Beta t (term (normalizeProof wf ht)) ∥₁
normalizeProof-sound wf = PT.elim (λ _ → squash₁)
  (λ ht → ∣ steps-beta (nf-reduces (normalize-typed wf ht)) ∣₁)

normalizeProof-retraction : {Γ : Context n} {A : Term n}
  (wf : WellFormed Γ) (t : NfAt Γ A)
  → normalizeProof wf (typed t) ≡ t
normalizeProof-retraction wf (normal-at t nt ht) = PT.elim
  (λ ht → nf-isSet (normalizeProof wf ht) (normal-at t nt ht))
  (λ ht → nf-path (normal-convertible-unique
    (normalize-typed wf ht) nt beta-refl)) ht

raw-act : {Γ : Context m} {Δ : Context n}
  → SubNF Γ Δ → Term m → Term n
raw-act σ = replace (sub-images σ)

raw-act-typed : {Γ : Context m} {Δ : Context n} {t A : Term m}
  → (σ : SubNF Γ Δ) → ∥ Typ Γ t A ∥₁
  → ∥ Typ Δ (raw-act σ t) (raw-act σ A) ∥₁
raw-act-typed σ ht = PT.rec2 squash₁
  (λ ps pt → ∣ typed-replace ps pt ∣₁) (sub-typed σ) ht

-- Substitution normalizes the type as well as its inhabitants.
pullTy : {Γ : Context m} {Δ : Context n}
  → WellFormed Δ → SubNF Γ Δ → TyNF Γ r → TyNF Δ r
pullTy wf σ A = normalizeProof wf (raw-act-typed σ (typed A))

pullTy-sound : {Γ : Context m} {Δ : Context n}
  (wf : WellFormed Δ) (σ : SubNF Γ Δ) (A : TyNF Γ r)
  → ∥ Beta (raw-act σ (term A)) (term (pullTy wf σ A)) ∥₁
pullTy-sound wf σ A = normalizeProof-sound wf (raw-act-typed σ (typed A))

pullTm-typing : {Γ : Context m} {Δ : Context n}
  (wf : WellFormed Δ) (σ : SubNF Γ Δ) (A : TyNF Γ r)
  (t : NfAt Γ (term A))
  → ∥ Typ Δ (raw-act σ (term t)) (term (pullTy wf σ A)) ∥₁
pullTm-typing wf σ A t = PT.rec3 squash₁ (λ ht hA e → ∣ conversion ht hA e ∣₁)
  (raw-act-typed σ (typed t)) (typed (pullTy wf σ A)) (pullTy-sound wf σ A)

pullTm : {Γ : Context m} {Δ : Context n}
  (wf : WellFormed Δ) (σ : SubNF Γ Δ) (A : TyNF Γ r)
  → NfAt Γ (term A) → NfAt Δ (term (pullTy wf σ A))
pullTm wf σ A t = normalizeProof wf (pullTm-typing wf σ A t)

pullTm-sound : {Γ : Context m} {Δ : Context n}
  (wf : WellFormed Δ) (σ : SubNF Γ Δ) (A : TyNF Γ r) (t : NfAt Γ (term A))
  → ∥ Beta (raw-act σ (term t)) (term (pullTm wf σ A t)) ∥₁
pullTm-sound wf σ A t = normalizeProof-sound wf (pullTm-typing wf σ A t)

-- The public laws are paths of canonical objects, not extra path constructors.
normal-equal : {t u : Term n} → Normal t → Normal u → ∥ Beta t u ∥₁ → t ≡ u
normal-equal nt nu = PT.rec (Discrete→isSet term-discrete _ _)
  (normal-beta-unique nt nu)

normalizeProof-coherent : {Γ : Context n} {t u A : Term n}
  (wf wf′ : WellFormed Γ) (ht : ∥ Typ Γ t A ∥₁) (hu : ∥ Typ Γ u A ∥₁)
  → ∥ Beta t u ∥₁ → normalizeProof wf ht ≡ normalizeProof wf′ hu
normalizeProof-coherent wf wf′ ht hu p = nf-path
  (normal-equal (normal (normalizeProof wf ht)) (normal (normalizeProof wf′ hu))
    (PT.rec3 squash₁ (λ left e right →
      ∣ beta-trans (beta-sym left) (beta-trans e right) ∣₁)
      (normalizeProof-sound wf ht) p (normalizeProof-sound wf′ hu)))

normalizeProof-reflects : {Γ : Context n} {t u A : Term n}
  (wf wf′ : WellFormed Γ) (ht : ∥ Typ Γ t A ∥₁) (hu : ∥ Typ Γ u A ∥₁)
  → normalizeProof wf ht ≡ normalizeProof wf′ hu → ∥ Beta t u ∥₁
normalizeProof-reflects wf wf′ ht hu p = PT.rec2 squash₁
  (λ left right → ∣ beta-trans left
    (beta-trans (beta-path (cong term p)) (beta-sym right)) ∣₁)
  (normalizeProof-sound wf ht) (normalizeProof-sound wf′ hu)

pullTy-identity : {Γ : Context n} (wf : WellFormed Γ) (A : TyNF Γ r)
  → pullTy wf (idNF Γ) A ≡ A
pullTy-identity wf A = nf-path (normal-equal (normal (pullTy wf (idNF _) A))
  (normal A) (PT.map (λ e → beta-trans (beta-sym e) (beta-path (replace-id (term A))))
    (pullTy-sound wf (idNF _) A)))

compose-action-sound : {Γ : Context l} {Δ : Context m} {Θ : Context n}
  (wf : WellFormed Θ) (σ : SubNF Γ Δ) (τ : SubNF Δ Θ) (t : Term l)
  → ∥ Beta (raw-act τ (raw-act σ t)) (raw-act (composeNF wf σ τ) t) ∥₁
compose-action-sound {Γ = Γ} {Δ} {Θ} wf (sub σ ns hs) (sub τ nt ht) t = PT.elim2
  {P = λ hs ht → ∥ Beta
    (raw-act (sub {Γ = Δ} {Δ = Θ} τ nt ht)
      (raw-act (sub {Γ = Γ} {Δ = Δ} σ ns hs) t))
    (raw-act (composeNF wf (sub {Γ = Γ} {Δ = Δ} σ ns hs)
      (sub {Γ = Δ} {Δ = Θ} τ nt ht)) t) ∥₁}
  (λ _ _ → squash₁)
  (λ ps pt → ∣ beta-trans (beta-path (replace-compose σ τ t))
    (equivalent-action
      {σ = compose (valuation {Γ = Γ} {Δ = Δ} σ ps) (valuation {Γ = Δ} {Δ = Θ} τ pt)}
      {τ = normalize-valuation wf
        (compose (valuation {Γ = Γ} {Δ = Δ} σ ps) (valuation {Γ = Δ} {Δ = Θ} τ pt))}
      (λ i → beta-sym (Normalize.equivalent wf
        (compose (valuation {Γ = Γ} {Δ = Δ} σ ps) (valuation {Γ = Δ} {Δ = Θ} τ pt)) i)) t) ∣₁)
  hs ht

pullTy-composition : {Γ : Context l} {Δ : Context m} {Θ : Context n}
  (wfΔ : WellFormed Δ) (wfΘ : WellFormed Θ)
  (σ : SubNF Γ Δ) (τ : SubNF Δ Θ) (A : TyNF Γ r)
  → pullTy wfΘ τ (pullTy wfΔ σ A) ≡ pullTy wfΘ (composeNF wfΘ σ τ) A
pullTy-composition wfΔ wfΘ σ τ A = nf-path
  (normal-equal (normal (pullTy wfΘ τ (pullTy wfΔ σ A)))
    (normal (pullTy wfΘ (composeNF wfΘ σ τ) A))
    (PT.rec3 squash₁ (λ left inner composite → PT.map
      (λ right → beta-trans (beta-sym left)
        (beta-trans (beta-replace (sub-images τ) (beta-sym inner))
          (beta-trans composite right)))
      (pullTy-sound wfΘ (composeNF wfΘ σ τ) A))
      (pullTy-sound wfΘ τ (pullTy wfΔ σ A)) (pullTy-sound wfΔ σ A)
      (compose-action-sound wfΘ σ τ (term A))))

term-transport : {Γ : Context n} {A B : Term n}
  (p : A ≡ B) (t : NfAt Γ A) → term (subst (NfAt Γ) p t) ≡ term t
term-transport {Γ = Γ} p t = sym (λ i → term (subst-filler (NfAt Γ) p t i))

pullTm-identity : {Γ : Context n} (wf : WellFormed Γ)
  (A : TyNF Γ r) (t : NfAt Γ (term A))
  → subst (NfAt Γ) (cong term (pullTy-identity wf A)) (pullTm wf (idNF Γ) A t) ≡ t
pullTm-identity wf A t = nf-path
  (term-transport (cong term (pullTy-identity wf A)) (pullTm wf (idNF _) A t)
  ∙ normal-equal (normal (pullTm wf (idNF _) A t)) (normal t)
    (PT.map (λ e → beta-trans (beta-sym e) (beta-path (replace-id (term t))))
      (pullTm-sound wf (idNF _) A t)))

pullTm-composition : {Γ : Context l} {Δ : Context m} {Θ : Context n}
  (wfΔ : WellFormed Δ) (wfΘ : WellFormed Θ)
  (σ : SubNF Γ Δ) (τ : SubNF Δ Θ) (A : TyNF Γ r) (t : NfAt Γ (term A))
  → subst (NfAt Θ) (cong term (pullTy-composition wfΔ wfΘ σ τ A))
      (pullTm wfΘ τ (pullTy wfΔ σ A) (pullTm wfΔ σ A t))
    ≡ pullTm wfΘ (composeNF wfΘ σ τ) A t
pullTm-composition wfΔ wfΘ σ τ A t = nf-path
  (term-transport (cong term (pullTy-composition wfΔ wfΘ σ τ A))
    (pullTm wfΘ τ (pullTy wfΔ σ A) (pullTm wfΔ σ A t))
  ∙ normal-equal
    (normal (pullTm wfΘ τ (pullTy wfΔ σ A) (pullTm wfΔ σ A t)))
    (normal (pullTm wfΘ (composeNF wfΘ σ τ) A t))
    (PT.rec3 squash₁ (λ left inner composite → PT.map
      (λ right → beta-trans (beta-sym left)
        (beta-trans (beta-replace (sub-images τ) (beta-sym inner))
          (beta-trans composite right)))
      (pullTm-sound wfΘ (composeNF wfΘ σ τ) A t))
      (pullTm-sound wfΘ τ (pullTy wfΔ σ A) (pullTm wfΔ σ A t))
      (pullTm-sound wfΔ σ A t) (compose-action-sound wfΘ σ τ (term t))))
