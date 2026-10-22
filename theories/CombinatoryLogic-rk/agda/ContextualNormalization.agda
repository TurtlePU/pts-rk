{-# OPTIONS --cubical --safe --guardedness #-}
module ContextualNormalization where

-- Normal-form interpretation under arbitrary original typed valuations.
-- The rank budget is computed, never supplied as a termination premise.
open import PTSPrelude
open import FiniteSyntax
open import NativeTyping
open import NativeValuations
open import NativeNormalization
open import NativeRankCoverage
open import NativeCertificates
open import NativeConfluence using (steps-beta)
open import BoundedReduction using (Normal; Steps)

private
  variable
    l m n : Nat

evaluation-budget : {Γ : Context m} {Δ : Context n} {t A : Term m}
  → WellFormed Δ → (σ : Valuation Γ Δ) → Typ Γ t A → Nat
evaluation-budget wf σ ht = rank-budget wf (act-typed σ ht)

-- BEGINCONTEXTUALEVALUATION
evaluate : {Γ : Context m} {Δ : Context n} {t A : Term m}
  → (wf : WellFormed Δ) → (σ : Valuation Γ Δ) → (ht : Typ Γ t A)
  → Normalized Δ (act σ t) (act σ A) (evaluation-budget wf σ ht)
evaluate wf σ ht = normalize-typed wf (act-typed σ ht)

value : {Γ : Context m} {Δ : Context n} {t A : Term m}
  → WellFormed Δ → (σ : Valuation Γ Δ) → Typ Γ t A → Term n
value wf σ ht = nf (evaluate wf σ ht)

value-typed : {Γ : Context m} {Δ : Context n} {t A : Term m}
  (wf : WellFormed Δ) (σ : Valuation Γ Δ) (ht : Typ Γ t A)
  → Typ Δ (value wf σ ht) (act σ A)
value-typed wf σ ht = nf-typed (evaluate wf σ ht)

value-normal : {Γ : Context m} {Δ : Context n} {t A : Term m}
  (wf : WellFormed Δ) (σ : Valuation Γ Δ) (ht : Typ Γ t A)
  → Normal (value wf σ ht)
value-normal wf σ ht = nf-normal (evaluate wf σ ht)

value-reduces : {Γ : Context m} {Δ : Context n} {t A : Term m}
  (wf : WellFormed Δ) (σ : Valuation Γ Δ) (ht : Typ Γ t A)
  → Steps (act σ t) (value wf σ ht)
value-reduces wf σ ht = nf-reduces (evaluate wf σ ht)
-- ENDCONTEXTUALEVALUATION

-- Neither derivation identity, a chosen type nor a common rank budget is
-- required: only the converted source terms determine their normal values.
value-source-coherent : {Γ : Context l} {Γ′ : Context m} {Δ : Context n}
  {t A : Term l} {u B : Term m}
  (wf wf′ : WellFormed Δ) (σ : Valuation Γ Δ) (τ : Valuation Γ′ Δ)
  (ht : Typ Γ t A) (hu : Typ Γ′ u B)
  → Beta (act σ t) (act τ u) → value wf σ ht ≡ value wf′ τ hu
value-source-coherent wf wf′ σ τ ht hu =
  normalization-coherent (evaluate wf σ ht) (evaluate wf′ τ hu)

value-coherent : {Γ : Context m} {Δ : Context n} {t u A B : Term m}
  (wf wf′ : WellFormed Δ) (σ τ : Valuation Γ Δ)
  (ht : Typ Γ t A) (hu : Typ Γ u B)
  → Equivalent σ τ → Beta t u → value wf σ ht ≡ value wf′ τ hu
value-coherent wf wf′ σ τ ht hu eq terms =
  value-source-coherent wf wf′ σ τ ht hu
    (action-congruence {σ = σ} {τ = τ} eq terms)

value-proof-independent : {Γ : Context m} {Δ : Context n} {t A B : Term m}
  (wf wf′ : WellFormed Δ) (σ : Valuation Γ Δ)
  (ht : Typ Γ t A) (ht′ : Typ Γ t B)
  → value wf σ ht ≡ value wf′ σ ht′
value-proof-independent wf wf′ σ ht ht′ =
  value-source-coherent wf wf′ σ σ ht ht′ beta-refl

value-reflects : {Γ : Context l} {Γ′ : Context m} {Δ : Context n}
  {t A : Term l} {u B : Term m}
  (wf wf′ : WellFormed Δ) (σ : Valuation Γ Δ) (τ : Valuation Γ′ Δ)
  (ht : Typ Γ t A) (hu : Typ Γ′ u B)
  → value wf σ ht ≡ value wf′ τ hu → Beta (act σ t) (act τ u)
value-reflects wf wf′ σ τ ht hu =
  normalization-reflects (evaluate wf σ ht) (evaluate wf′ τ hu)

value-on-normal : {Γ : Context m} {Δ : Context n} {t A : Term m}
  (wf : WellFormed Δ) (σ : Valuation Γ Δ) (ht : Typ Γ t A)
  → Normal (act σ t) → value wf σ ht ≡ act σ t
value-on-normal wf σ ht normal = normal-convertible-unique
  (evaluate wf σ ht) normal beta-refl

value-identity : {Γ : Context n} {t A : Term n}
  (wf : WellFormed Γ) (ht : Typ Γ t A)
  → value wf (identity Γ) ht ≡ nf (normalize-typed wf ht)
value-identity {Γ = Γ} {t} wf ht = normalization-coherent
  (evaluate wf (identity Γ) ht) (normalize-typed wf ht)
  (subst (Beta (act (identity Γ) t)) (act-identity Γ t) beta-refl)

value-identity-normal : {Γ : Context n} {t A : Term n}
  (wf : WellFormed Γ) (ht : Typ Γ t A) → Normal t
  → value wf (identity Γ) ht ≡ t
value-identity-normal {Γ = Γ} {t} wf ht normal =
  normal-convertible-unique (evaluate wf (identity Γ) ht) normal
    (subst (Beta (act (identity Γ) t)) (act-identity Γ t) beta-refl)

-- Substituting after normalization yields the same value as composing the
-- valuations before normalization, even though their computed budgets differ.
-- BEGINCONTEXTUALCOMPOSITION
value-composition : {Γ : Context l} {Δ : Context m} {Θ : Context n}
  {t A : Term l} (wfΔ : WellFormed Δ) (wfΘ : WellFormed Θ)
  (σ : Valuation Γ Δ) (τ : Valuation Δ Θ) (ht : Typ Γ t A)
  → value wfΘ τ (value-typed wfΔ σ ht)
      ≡ value wfΘ (compose σ τ) ht
value-composition {t = t} wfΔ wfΘ σ τ ht =
  value-source-coherent wfΘ wfΘ τ (compose σ τ) (value-typed wfΔ σ ht) ht
    (beta-trans (beta-sym (steps-beta (act-steps τ (value-reduces wfΔ σ ht))))
      (subst (Beta (act τ (act σ t))) (act-compose σ τ t) beta-refl))
-- ENDCONTEXTUALCOMPOSITION

value-idempotent : {Γ : Context m} {Δ : Context n} {t A : Term m}
  (wf : WellFormed Δ) (σ : Valuation Γ Δ) (ht : Typ Γ t A)
  → value wf (identity Δ) (value-typed wf σ ht) ≡ value wf σ ht
value-idempotent wf σ ht = value-identity-normal wf
  (value-typed wf σ ht) (value-normal wf σ ht)

-- Independent proof-tree acceptance supplies all six original typing rules.
-- Only the target valuation is typed; the caller supplies no Typ derivation
-- for the certificate's subject, no rank bound, and no normalization result.
-- BEGINCERTIFICATEINTERPRETATION
interpret-certificate : {Γ : Context m} {Δ : Context n}
  (wf : WellFormed Δ) (σ : Valuation Γ Δ) (c : Certificate m)
  (accepted : Accepted Γ c)
  → Normalized Δ (act σ (certificate-term c)) (act σ (certificate-type c))
      (evaluation-budget wf σ (accepted-typing accepted))
interpret-certificate wf σ c accepted = evaluate wf σ (accepted-typing accepted)

certificate-value : {Γ : Context m} {Δ : Context n}
  → WellFormed Δ → (σ : Valuation Γ Δ) → (c : Certificate m)
  → Accepted Γ c → Term n
certificate-value wf σ c accepted = nf (interpret-certificate wf σ c accepted)

certificate-value-typed : {Γ : Context m} {Δ : Context n}
  (wf : WellFormed Δ) (σ : Valuation Γ Δ) (c : Certificate m)
  (accepted : Accepted Γ c)
  → Typ Δ (certificate-value wf σ c accepted) (act σ (certificate-type c))
certificate-value-typed wf σ c accepted = nf-typed (interpret-certificate wf σ c accepted)
-- ENDCERTIFICATEINTERPRETATION

certificate-value-coherent : {Γ : Context m} {Δ : Context n}
  (wf wf′ : WellFormed Δ) (σ τ : Valuation Γ Δ) (c d : Certificate m)
  (accepted : Accepted Γ c) (accepted′ : Accepted Γ d)
  → Equivalent σ τ → Beta (certificate-term c) (certificate-term d)
  → certificate-value wf σ c accepted ≡ certificate-value wf′ τ d accepted′
certificate-value-coherent wf wf′ σ τ c d accepted accepted′ =
  value-coherent wf wf′ σ τ (accepted-typing accepted) (accepted-typing accepted′)

certificate-value-proof-independent : {Γ : Context m} {Δ : Context n}
  (wf wf′ : WellFormed Δ) (σ : Valuation Γ Δ) (c d : Certificate m)
  (accepted : Accepted Γ c) (accepted′ : Accepted Γ d)
  → certificate-term c ≡ certificate-term d
  → certificate-value wf σ c accepted ≡ certificate-value wf′ σ d accepted′
certificate-value-proof-independent wf wf′ σ c d accepted accepted′ same =
  certificate-value-coherent wf wf′ σ σ c d accepted accepted′ (equivalent-refl {σ = σ})
    (subst (Beta (certificate-term c)) same beta-refl)

interpret-equality : {Γ : Context m} {Δ : Context n}
  (wf : WellFormed Δ) (σ : Valuation Γ Δ) (c d : Certificate m)
  (accepted : Accepted Γ c) (accepted′ : Accepted Γ d)
  (e : EqualityCertificate m) → EqualityAccepted e
  → equality-source e ≡ certificate-term c → equality-target e ≡ certificate-term d
  → certificate-value wf σ c accepted ≡ certificate-value wf σ d accepted′
interpret-equality wf σ c d accepted accepted′ e he source target =
  certificate-value-coherent wf wf σ σ c d accepted accepted′ (equivalent-refl {σ = σ})
    (subst (Beta (certificate-term c)) target
      (subst (λ t → Beta t (equality-target e)) source (accepted-equality e he)))

certificate-value-composition : {Γ : Context l} {Δ : Context m} {Θ : Context n}
  (wfΔ : WellFormed Δ) (wfΘ : WellFormed Θ)
  (σ : Valuation Γ Δ) (τ : Valuation Δ Θ) (c : Certificate l) (accepted : Accepted Γ c)
  → value wfΘ τ (certificate-value-typed wfΔ σ c accepted)
      ≡ certificate-value wfΘ (compose σ τ) c accepted
certificate-value-composition wfΔ wfΘ σ τ c accepted =
  value-composition wfΔ wfΘ σ τ (accepted-typing accepted)
