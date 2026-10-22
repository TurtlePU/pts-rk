{-# OPTIONS --cubical --safe --guardedness #-}
module FiniteCarriers where

open import FiniteSyntax
open import FiniteBounds using (capacity; tower; tetration; capacity-knuth)
open import Cubical.Foundations.Prelude using (isProp)
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sum using (_⊎_; inl; inr; ⊎-equiv)
open import Cubical.Data.Sigma using (_×_; ≃-×; Σ≡Prop)
open import Cubical.Data.Unit using (Unit; tt; isPropUnit)
open import Cubical.Data.Empty as Empty using (⊥; isProp⊥)
open import Cubical.Data.FinData.Properties as FinProperties
  using (toℕ<n; fromℕ'; toFromId'; inj-toℕ)
open import Cubical.Data.FinData.Base using (toℕ)

-- Every universe label is an index in a fixed, finite input alphabet.
-- Depth codes preserve lambda annotations and de Bruijn scoping exactly.
Code : (a n depth : Nat) → Set
Code a n zero = ⊥
Code a n (suc d) = Fin a ⊎ (Fin n ⊎
  ((Code a n d × Code a (suc n) d) ⊎
   ((Code a n d × Code a (suc n) d) ⊎ (Code a n d × Code a n d))))

private
  sum-fin : ∀ {A B : Set} {a b} → A ≃ Fin a → B ≃ Fin b
    → (A ⊎ B) ≃ Fin (a + b)
  sum-fin {a = a} {b} e f = compEquiv (⊎-equiv e f) (FinProperties.FinSumChar.Equiv a b)

  prod-fin : ∀ {A B : Set} {a b} → A ≃ Fin a → B ≃ Fin b
    → (A × B) ≃ Fin (a · b)
  prod-fin {a = a} {b} e f = compEquiv (≃-× e f) (FinProperties.FinProdChar.Equiv a b)

-- An actual equivalence, not merely an enumeration of finite samples.
code-fin : (a n d : Nat) → Code a n d ≃ Fin (capacity a n d)
code-fin a n zero = Empty.uninhabEquiv (λ ()) (λ ())
code-fin a n (suc d) = sum-fin (idEquiv _) (sum-fin (idEquiv _)
  (sum-fin (prod-fin (code-fin a n d) (code-fin a (suc n) d))
    (sum-fin (prod-fin (code-fin a n d) (code-fin a (suc n) d))
      (prod-fin (code-fin a n d) (code-fin a n d)))))

decode : ∀ {a n d} → Code a n d → Raw (Fin a) n
decode {d = suc d} (inl i) = U i
decode {d = suc d} (inr (inl i)) = var i
decode {d = suc d} (inr (inr (inl (A , B)))) = pi (decode A) (decode B)
decode {d = suc d} (inr (inr (inr (inl (A , b))))) = lam (decode A) (decode b)
decode {d = suc d} (inr (inr (inr (inr (f , x))))) = app (decode f) (decode x)

Fits : ∀ {Label n} → Nat → Raw Label n → Set
Fits zero t = ⊥
Fits (suc d) (U i) = Unit
Fits (suc d) (var i) = Unit
Fits (suc d) (pi A B) = Fits d A × Fits d B
Fits (suc d) (lam A b) = Fits d A × Fits d b
Fits (suc d) (app f x) = Fits d f × Fits d x

encode : ∀ {a n} (d : Nat) (t : Raw (Fin a) n) → Fits d t → Code a n d
encode zero t ()
encode (suc d) (U i) p = inl i
encode (suc d) (var i) p = inr (inl i)
encode (suc d) (pi A B) (p , q) = inr (inr (inl (encode d A p , encode d B q)))
encode (suc d) (lam A b) (p , q) = inr (inr (inr (inl (encode d A p , encode d b q))))
encode (suc d) (app f x) (p , q) = inr (inr (inr (inr (encode d f p , encode d x q))))

decode-encode : ∀ {a n} (d : Nat) (t : Raw (Fin a) n) (p : Fits d t)
  → decode (encode d t p) ≡ t
decode-encode zero t ()
decode-encode (suc d) (U i) p = refl
decode-encode (suc d) (var i) p = refl
decode-encode (suc d) (pi A B) (p , q) =
  cong₂ pi (decode-encode d A p) (decode-encode d B q)
decode-encode (suc d) (lam A b) (p , q) =
  cong₂ lam (decode-encode d A p) (decode-encode d b q)
decode-encode (suc d) (app f x) (p , q) =
  cong₂ app (decode-encode d f p) (decode-encode d x q)

raise-fit : ∀ {Label n} (d : Nat) (t : Raw Label n) → Fits d t → Fits (suc d) t
raise-fit zero t ()
raise-fit (suc d) (U i) p = tt
raise-fit (suc d) (var i) p = tt
raise-fit (suc d) (pi A B) (p , q) = raise-fit d A p , raise-fit d B q
raise-fit (suc d) (lam A b) (p , q) = raise-fit d A p , raise-fit d b q
raise-fit (suc d) (app f x) (p , q) = raise-fit d f p , raise-fit d x q

raise-fits : ∀ {Label n} (k d : Nat) (t : Raw Label n) → Fits d t → Fits (k + d) t
raise-fits zero d t p = p
raise-fits (suc k) d t p = raise-fit (k + d) t (raise-fits k d t p)

weaken-fit : ∀ {Label n d e} {t : Raw Label n} → d ≤ e → Fits d t → Fits e t
weaken-fit {d = d} {t = t} (k , pEq) p = subst (λ e → Fits e t) pEq (raise-fits k d t p)

fits-nodes : ∀ {Label n} (t : Raw Label n) → Fits (nodes t) t
fits-nodes (U i) = tt
fits-nodes (var i) = tt
fits-nodes (pi A B) = weaken-fit ≤SumLeft (fits-nodes A) , weaken-fit ≤SumRight (fits-nodes B)
fits-nodes (lam A b) = weaken-fit ≤SumLeft (fits-nodes A) , weaken-fit ≤SumRight (fits-nodes b)
fits-nodes (app f x) = weaken-fit ≤SumLeft (fits-nodes f) , weaken-fit ≤SumRight (fits-nodes x)

Sized : (a n s : Nat) → Set
Sized a n s = Σ (Raw (Fin a) n) (λ t → nodes t ≤ s)

-- BEGINFINITEINJECTION
record AtMost (A : Set) (k : Nat) : Set where
  field
    index : A → Fin k
    injective : (x y : A) → index x ≡ index y → x ≡ y
open AtMost public

sized-index : ∀ {a n s} → Sized a n s → Fin (capacity a n s)
sized-index {a} {n} {s} (t , p) = equivFun (code-fin a n s)
  (encode s t (weaken-fit p (fits-nodes t)))

sized-finite : (a n s : Nat) → AtMost (Sized a n s) (capacity a n s)
sized-finite a n s .index = sized-index
sized-finite a n s .injective (t , p) (u , q) pEq = Σ≡Prop (λ _ → isProp≤)
  (sym (decode-encode s t (weaken-fit p (fits-nodes t))) ∙
   cong decode
     (sym (retEq (code-fin a n s) _) ∙ cong (invEq (code-fin a n s)) pEq ∙
       retEq (code-fin a n s) _) ∙
   decode-encode s u (weaken-fit q (fits-nodes u)))
-- ENDFINITEINJECTION

-- Proof-valued fibres do not multiply the number of represented terms.
subtype-finite : ∀ {A : Set} {k} (P : A → Set)
  → ((x : A) → isProp (P x)) → AtMost A k → AtMost (Σ A P) k
subtype-finite P prop finite .index (x , p) = index finite x
subtype-finite P prop finite .injective (x , p) (y , q) pEq =
  Σ≡Prop prop (injective finite x y pEq)

private
  raise-fin : ∀ {m k} → m ≤ k → Fin m → Fin k
  raise-fin {m} {k} p i = fromℕ' k (toℕ i) (≤-trans (toℕ<n i) p)

  raise-fin-injective : ∀ {m k} (p : m ≤ k) (i j : Fin m)
    → raise-fin p i ≡ raise-fin p j → i ≡ j
  raise-fin-injective {k = k} p i j pEq = inj-toℕ
    (sym (toFromId' k (toℕ i) _) ∙ cong toℕ pEq ∙ toFromId' k (toℕ j) _)

enlarge : ∀ {A : Set} {m k} → m ≤ k → AtMost A m → AtMost A k
enlarge p finite .index x = raise-fin p (index finite x)
enlarge p finite .injective x y pEq = injective finite x y
  (raise-fin-injective p (index finite x) (index finite y) pEq)

-- BEGINKNUTHCARRIER
closed-carrier-bound : (a d N : Nat) → a ≤ N
  → AtMost (Sized a 0 (tower d N)) (tetration (4 · N + 4) (d + 3))
closed-carrier-bound a d N p =
  enlarge (capacity-knuth a d N p) (sized-finite a 0 (tower d N))
-- ENDKNUTHCARRIER
