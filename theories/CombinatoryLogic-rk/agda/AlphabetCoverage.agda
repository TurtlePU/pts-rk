{-# OPTIONS --cubical --safe --guardedness #-}
module AlphabetCoverage where

-- Every finite annotated source has a canonical finite universe alphabet.
-- This prefix encoding counts numeric labels, not distinct occurrences:
-- its alphabet bound need not be at most the source's node count.
open import PTSPrelude
open import FiniteSyntax
open import NativeTyping using (Term; Context; empty; extend)
open import NativeAlgebra using (fin-cases)
open import NativeRanks using (max-left; max-right; max-least)
open import NativeValuations using (Valuation; images)
open import FragmentAlphabet using (include-alphabet; include-label; dictionary-agreement; relabel-injective)
open import BoundedReduction using (Normal; normal-reflect; rounds; relabel-rounds)
open import Cubical.Data.Nat.Order using (_≤_; _<_; ≤-refl; ≤-trans; zero-≤; ≤Dec)
open import Cubical.Data.FinData.Base using (toℕ)
open import Cubical.Data.FinData.Properties using (fromℕ'; toFromId'; toℕ<n; inj-toℕ)
open import Cubical.Data.Sigma.Base using (_×_)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Relation.Nullary using (Dec; yes; no)

private
  variable
    m n : Nat

-- BEGINALPHABETCOVERAGE
labelBound : Term n → Nat
labelBound (U i) = suc i
labelBound (var i) = zero
labelBound (pi A B) = max (labelBound A) (labelBound B)
labelBound (lam A b) = max (labelBound A) (labelBound b)
labelBound (app f y) = max (labelBound f) (labelBound y)

AllLabelsBelow : Nat → Term n → Set
AllLabelsBelow a (U i) = i < a
AllLabelsBelow a (var i) = Unit
AllLabelsBelow a (pi A B) = AllLabelsBelow a A × AllLabelsBelow a B
AllLabelsBelow a (lam A b) = AllLabelsBelow a A × AllLabelsBelow a b
AllLabelsBelow a (app f y) = AllLabelsBelow a f × AllLabelsBelow a y

encode-under : (t : Term n) (a : Nat) → labelBound t ≤ a → Raw (Fin a) n
encode-under (U i) a bound = U (fromℕ' a i bound)
encode-under (var i) a bound = var i
encode-under (pi A B) a bound = pi
  (encode-under A a (≤-trans (max-left _ _) bound))
  (encode-under B a (≤-trans (max-right _ _) bound))
encode-under (lam A b) a bound = lam
  (encode-under A a (≤-trans (max-left _ _) bound))
  (encode-under b a (≤-trans (max-right _ _) bound))
encode-under (app f y) a bound = app
  (encode-under f a (≤-trans (max-left _ _) bound))
  (encode-under y a (≤-trans (max-right _ _) bound))

encode-under-recovers : (t : Term n) (a : Nat) (bound : labelBound t ≤ a)
  → relabel toℕ (encode-under t a bound) ≡ t
encode-under-recovers (U i) a bound = cong U (toFromId' a i bound)
encode-under-recovers (var i) a bound = refl
encode-under-recovers (pi A B) a bound = cong₂ pi
  (encode-under-recovers A a (≤-trans (max-left _ _) bound))
  (encode-under-recovers B a (≤-trans (max-right _ _) bound))
encode-under-recovers (lam A b) a bound = cong₂ lam
  (encode-under-recovers A a (≤-trans (max-left _ _) bound))
  (encode-under-recovers b a (≤-trans (max-right _ _) bound))
encode-under-recovers (app f y) a bound = cong₂ app
  (encode-under-recovers f a (≤-trans (max-left _ _) bound))
  (encode-under-recovers y a (≤-trans (max-right _ _) bound))
-- ENDALPHABETCOVERAGE

encode-under-nodes : (t : Term n) (a : Nat) (bound : labelBound t ≤ a)
  → nodes (encode-under t a bound) ≡ nodes t
encode-under-nodes t a bound = sym (relabel-nodes toℕ (encode-under t a bound))
  ∙ cong nodes (encode-under-recovers t a bound)

bound-labels : (t : Term n) (a : Nat) → labelBound t ≤ a → AllLabelsBelow a t
bound-labels (U i) a bound = bound
bound-labels (var i) a bound = tt
bound-labels (pi A B) a bound = bound-labels A a (≤-trans (max-left _ _) bound)
  , bound-labels B a (≤-trans (max-right _ _) bound)
bound-labels (lam A b) a bound = bound-labels A a (≤-trans (max-left _ _) bound)
  , bound-labels b a (≤-trans (max-right _ _) bound)
bound-labels (app f y) a bound = bound-labels f a (≤-trans (max-left _ _) bound)
  , bound-labels y a (≤-trans (max-right _ _) bound)

labels-bound : (t : Term n) (a : Nat) → AllLabelsBelow a t → labelBound t ≤ a
labels-bound (U i) a bound = bound
labels-bound (var i) a bound = zero-≤
labels-bound (pi A B) a (p , q) = max-least (labels-bound A a p) (labels-bound B a q)
labels-bound (lam A b) a (p , q) = max-least (labels-bound A a p) (labels-bound b a q)
labels-bound (app f y) a (p , q) = max-least (labels-bound f a p) (labels-bound y a q)

labels-dec : (t : Term n) (a : Nat) → Dec (AllLabelsBelow a t)
labels-dec t a with ≤Dec (labelBound t) a
... | yes bound = yes (bound-labels t a bound)
... | no refute = no (λ h → refute (labels-bound t a h))

represented-labels : ∀ {a} (t : Raw (Fin a) n) → AllLabelsBelow a (relabel toℕ t)
represented-labels (U i) = toℕ<n i
represented-labels (var i) = tt
represented-labels (pi A B) = represented-labels A , represented-labels B
represented-labels (lam A b) = represented-labels A , represented-labels b
represented-labels (app f y) = represented-labels f , represented-labels y

represented-bound : ∀ {a} (t : Raw (Fin a) n) → labelBound (relabel toℕ t) ≤ a
represented-bound {a = a} t = labels-bound (relabel toℕ t) a (represented-labels t)

encode-under-normal : (t : Term n) (a : Nat) (bound : labelBound t ≤ a)
  → Normal t → Normal (encode-under t a bound)
encode-under-normal t a bound normal = normal-reflect toℕ
  (subst Normal (sym (encode-under-recovers t a bound)) normal)

encode-under-unique : (t : Term n) (a : Nat) (p q : labelBound t ≤ a)
  → encode-under t a p ≡ encode-under t a q
encode-under-unique t a p q = relabel-injective toℕ (λ i j → inj-toℕ) _ _
  (encode-under-recovers t a p ∙ sym (encode-under-recovers t a q))

encode-under-coherent : (t : Term n) (a b : Nat)
  (p : labelBound t ≤ a) (q : labelBound t ≤ b) (include : a ≤ b)
  → relabel (include-alphabet include) (encode-under t a p) ≡ encode-under t b q
encode-under-coherent t a b p q include = relabel-injective toℕ (λ i j → inj-toℕ) _ _
  (dictionary-agreement (include-alphabet include) toℕ toℕ (include-label include)
      (encode-under t a p)
    ∙ encode-under-recovers t a p ∙ sym (encode-under-recovers t b q))

-- Two subjects, e.g. a term and its type, share this explicitly computed alphabet.
packetBound : Term m → Term n → Nat
packetBound t A = max (labelBound t) (labelBound A)

packet-term-bound : (t : Term m) (A : Term n) → labelBound t ≤ packetBound t A
packet-term-bound t A = max-left _ _

packet-type-bound : (t : Term m) (A : Term n) → labelBound A ≤ packetBound t A
packet-type-bound t A = max-right _ _

packet-term : (t : Term m) (A : Term n) → Raw (Fin (packetBound t A)) m
packet-term t A = encode-under t (packetBound t A) (packet-term-bound t A)

packet-type : (t : Term m) (A : Term n) → Raw (Fin (packetBound t A)) n
packet-type t A = encode-under A (packetBound t A) (packet-type-bound t A)

-- The actual reducer cannot introduce a new universe label.
rounds-label-bound : (d : Nat) (t : Term n) (a : Nat) → labelBound t ≤ a
  → labelBound (rounds d t) ≤ a
rounds-label-bound d t a bound = subst (λ u → labelBound u ≤ a)
  (relabel-rounds toℕ d (encode-under t a bound)
    ∙ cong (rounds d) (encode-under-recovers t a bound))
  (represented-bound (rounds d (encode-under t a bound)))

encode-rounds : (d : Nat) (t : Term n) (a : Nat) (bound : labelBound t ≤ a)
  → rounds d (encode-under t a bound)
      ≡ encode-under (rounds d t) a (rounds-label-bound d t a bound)
encode-rounds d t a bound = relabel-injective toℕ (λ i j → inj-toℕ) _ _
  (relabel-rounds toℕ d (encode-under t a bound)
    ∙ cong (rounds d) (encode-under-recovers t a bound)
    ∙ sym (encode-under-recovers (rounds d t) a (rounds-label-bound d t a bound)))

-- A context is encoded declaration by declaration, retaining every annotation.
data AlphabetContext (a : Nat) : Nat → Set where
  ctx-empty : AlphabetContext a zero
  ctx-extend : AlphabetContext a n → Raw (Fin a) n → AlphabetContext a (suc n)

decode-context : ∀ {a} → AlphabetContext a n → Context n
decode-context ctx-empty = empty
decode-context (ctx-extend Γ A) = extend (decode-context Γ) (relabel toℕ A)

contextBound : Context n → Nat
contextBound empty = zero
contextBound (extend Γ A) = max (contextBound Γ) (labelBound A)

encode-context : (Γ : Context n) (a : Nat) → contextBound Γ ≤ a → AlphabetContext a n
encode-context empty a bound = ctx-empty
encode-context (extend Γ A) a bound = ctx-extend
  (encode-context Γ a (≤-trans (max-left _ _) bound))
  (encode-under A a (≤-trans (max-right _ _) bound))

encode-context-recovers : (Γ : Context n) (a : Nat) (bound : contextBound Γ ≤ a)
  → decode-context (encode-context Γ a bound) ≡ Γ
encode-context-recovers empty a bound = refl
encode-context-recovers (extend Γ A) a bound = cong₂ extend
  (encode-context-recovers Γ a (≤-trans (max-left _ _) bound))
  (encode-under-recovers A a (≤-trans (max-right _ _) bound))

-- Finite tuples cover all substitution images, including the empty tuple.
familyBound : (Fin m → Term n) → Nat
familyBound {m = zero} ts = zero
familyBound {m = suc m} ts = max (labelBound (ts fzero)) (familyBound (λ i → ts (fsuc i)))

family-member-bound : (ts : Fin m → Term n) (i : Fin m) → labelBound (ts i) ≤ familyBound ts
family-member-bound {m = zero} ts ()
family-member-bound {m = suc m} ts i = fin-cases
  (λ i → labelBound (ts i) ≤ familyBound ts) i (max-left _ _)
  (λ j → ≤-trans (family-member-bound (λ k → ts (fsuc k)) j) (max-right _ _))

encode-family : (ts : Fin m → Term n) (a : Nat) → familyBound ts ≤ a
  → Fin m → Raw (Fin a) n
encode-family ts a bound i = encode-under (ts i) a (≤-trans (family-member-bound ts i) bound)

encode-family-recovers : (ts : Fin m → Term n) (a : Nat) (bound : familyBound ts ≤ a)
  → ∀ i → relabel toℕ (encode-family ts a bound i) ≡ ts i
encode-family-recovers ts a bound i = encode-under-recovers (ts i) a
  (≤-trans (family-member-bound ts i) bound)

valuationBound : {Γ : Context m} {Δ : Context n} → Valuation Γ Δ → Nat
valuationBound σ = familyBound (images σ)

encode-valuation-images : {Γ : Context m} {Δ : Context n}
  (σ : Valuation Γ Δ) (a : Nat) → valuationBound σ ≤ a → Fin m → Raw (Fin a) n
encode-valuation-images σ = encode-family (images σ)

encode-valuation-recovers : {Γ : Context m} {Δ : Context n}
  (σ : Valuation Γ Δ) (a : Nat) (bound : valuationBound σ ≤ a)
  → ∀ i → relabel toℕ (encode-valuation-images σ a bound i) ≡ images σ i
encode-valuation-recovers σ = encode-family-recovers (images σ)
