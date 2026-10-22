{-# OPTIONS --cubical --safe --guardedness #-}
module FragmentAlphabet where

-- Enlarging the finite alphabet changes codes, not their native meaning.
open import FiniteSyntax
open import NormalForms
open import FragmentEmbeddings
open import NativeTyping
open import BoundedReduction using (normal-relabel; rounds; relabel-rounds)
open import FiniteApplication using (inputSize)
import FragmentApplication as Application
open import Cubical.Data.Nat.Order using (_≤_; ≤-refl; ≤-trans; isProp≤)
open import Cubical.Data.Sigma using (_×_; Σ≡Prop)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Data.FinData.Base using (toℕ)
open import Cubical.Data.FinData.Properties using (fromℕ'; toℕ<n; toFromId'; inj-toℕ)
import Cubical.HITs.PropositionalTruncation as PT

private
  variable
    L M K : Set
    n : Nat

relabel-cong : (f g : L → M) → (∀ i → f i ≡ g i)
  → (t : Raw L n) → relabel f t ≡ relabel g t
relabel-cong f g h (U i) = cong U (h i)
relabel-cong f g h (var i) = refl
relabel-cong f g h (pi A B) = cong₂ pi (relabel-cong f g h A) (relabel-cong f g h B)
relabel-cong f g h (lam A b) = cong₂ lam (relabel-cong f g h A) (relabel-cong f g h b)
relabel-cong f g h (app t u) = cong₂ app (relabel-cong f g h t) (relabel-cong f g h u)

relabel-identity : (t : Raw L n) → relabel (λ i → i) t ≡ t
relabel-identity (U i) = refl
relabel-identity (var i) = refl
relabel-identity (pi A B) = cong₂ pi (relabel-identity A) (relabel-identity B)
relabel-identity (lam A b) = cong₂ lam (relabel-identity A) (relabel-identity b)
relabel-identity (app t u) = cong₂ app (relabel-identity t) (relabel-identity u)

relabel-composition : (f : L → M) (g : M → K) (t : Raw L n)
  → relabel g (relabel f t) ≡ relabel (λ i → g (f i)) t
relabel-composition f g (U i) = refl
relabel-composition f g (var i) = refl
relabel-composition f g (pi A B) = cong₂ pi
  (relabel-composition f g A) (relabel-composition f g B)
relabel-composition f g (lam A b) = cong₂ lam
  (relabel-composition f g A) (relabel-composition f g b)
relabel-composition f g (app t u) = cong₂ app
  (relabel-composition f g t) (relabel-composition f g u)

private
  -- A computed equality code avoids indexed matching in Cubical Agda.
  RawEq : Raw L n → Raw L n → Set
  RawEq (U i) (U j) = i ≡ j
  RawEq (var i) (var j) = i ≡ j
  RawEq (pi A B) (pi C D) = RawEq A C × RawEq B D
  RawEq (lam A b) (lam C d) = RawEq A C × RawEq b d
  RawEq (app f x) (app g y) = RawEq f g × RawEq x y
  RawEq _ _ = ⊥

  raw-eq-refl : (t : Raw L n) → RawEq t t
  raw-eq-refl (U i) = refl
  raw-eq-refl (var i) = refl
  raw-eq-refl (pi A B) = raw-eq-refl A , raw-eq-refl B
  raw-eq-refl (lam A b) = raw-eq-refl A , raw-eq-refl b
  raw-eq-refl (app f x) = raw-eq-refl f , raw-eq-refl x

  raw-eq-path : (t u : Raw L n) → RawEq t u → t ≡ u
  raw-eq-path (U i) (U j) p = cong U p
  raw-eq-path (var i) (var j) p = cong var p
  raw-eq-path (pi A B) (pi C D) (p , q) = cong₂ pi (raw-eq-path A C p) (raw-eq-path B D q)
  raw-eq-path (lam A b) (lam C d) (p , q) = cong₂ lam (raw-eq-path A C p) (raw-eq-path b d q)
  raw-eq-path (app f x) (app g y) (p , q) = cong₂ app (raw-eq-path f g p) (raw-eq-path x y q)
  raw-eq-path (U i) (var j) ()
  raw-eq-path (U i) (pi A B) ()
  raw-eq-path (U i) (lam A b) ()
  raw-eq-path (U i) (app f x) ()
  raw-eq-path (var i) (U j) ()
  raw-eq-path (var i) (pi A B) ()
  raw-eq-path (var i) (lam A b) ()
  raw-eq-path (var i) (app f x) ()
  raw-eq-path (pi A B) (U i) ()
  raw-eq-path (pi A B) (var i) ()
  raw-eq-path (pi A B) (lam C d) ()
  raw-eq-path (pi A B) (app f x) ()
  raw-eq-path (lam A b) (U i) ()
  raw-eq-path (lam A b) (var i) ()
  raw-eq-path (lam A b) (pi C D) ()
  raw-eq-path (lam A b) (app f x) ()
  raw-eq-path (app f x) (U i) ()
  raw-eq-path (app f x) (var i) ()
  raw-eq-path (app f x) (pi A B) ()
  raw-eq-path (app f x) (lam A b) ()

  relabel-eq-reflect : (f : L → M)
    → (∀ i j → f i ≡ f j → i ≡ j) → (t u : Raw L n)
    → RawEq (relabel f t) (relabel f u) → RawEq t u
  relabel-eq-reflect f inj (U i) (U j) p = inj i j p
  relabel-eq-reflect f inj (var i) (var j) p = p
  relabel-eq-reflect f inj (pi A B) (pi C D) (p , q) =
    relabel-eq-reflect f inj A C p , relabel-eq-reflect f inj B D q
  relabel-eq-reflect f inj (lam A b) (lam C d) (p , q) =
    relabel-eq-reflect f inj A C p , relabel-eq-reflect f inj b d q
  relabel-eq-reflect f inj (app t u) (app v w) (p , q) =
    relabel-eq-reflect f inj t v p , relabel-eq-reflect f inj u w q
  relabel-eq-reflect f inj (U i) (var j) p = p
  relabel-eq-reflect f inj (U i) (pi A B) p = p
  relabel-eq-reflect f inj (U i) (lam A b) p = p
  relabel-eq-reflect f inj (U i) (app t u) p = p
  relabel-eq-reflect f inj (var i) (U j) p = p
  relabel-eq-reflect f inj (var i) (pi A B) p = p
  relabel-eq-reflect f inj (var i) (lam A b) p = p
  relabel-eq-reflect f inj (var i) (app t u) p = p
  relabel-eq-reflect f inj (pi A B) (U i) p = p
  relabel-eq-reflect f inj (pi A B) (var i) p = p
  relabel-eq-reflect f inj (pi A B) (lam C d) p = p
  relabel-eq-reflect f inj (pi A B) (app t u) p = p
  relabel-eq-reflect f inj (lam A b) (U i) p = p
  relabel-eq-reflect f inj (lam A b) (var i) p = p
  relabel-eq-reflect f inj (lam A b) (pi C D) p = p
  relabel-eq-reflect f inj (lam A b) (app t u) p = p
  relabel-eq-reflect f inj (app t u) (U i) p = p
  relabel-eq-reflect f inj (app t u) (var i) p = p
  relabel-eq-reflect f inj (app t u) (pi A B) p = p
  relabel-eq-reflect f inj (app t u) (lam A b) p = p

relabel-injective : (f : L → M)
  → (∀ i j → f i ≡ f j → i ≡ j) → (t u : Raw L n)
  → relabel f t ≡ relabel f u → t ≡ u
relabel-injective f inj t u p = raw-eq-path t u
  (relabel-eq-reflect f inj t u
    (subst (RawEq (relabel f t)) p (raw-eq-refl (relabel f t))))

-- BEGINALPHABETNORMAL
map-normal : (f : L → M) → Nf L n → Nf M n
map-normal f t = from-normal (relabel f (erase _ t))
  (normal-relabel f (erase-normal t))

map-normal-erase : (f : L → M) (t : Nf L n)
  → erase M (map-normal f t) ≡ relabel f (erase L t)
map-normal-erase f t = erase-from-normal _ _

map-normal-nodes : (f : L → M) (t : Nf L n)
  → nodes (erase M (map-normal f t)) ≡ nodes (erase L t)
map-normal-nodes f t = cong nodes (map-normal-erase f t) ∙ relabel-nodes f (erase _ t)
-- ENDALPHABETNORMAL

map-normal-identity : (t : Nf L n) → map-normal (λ i → i) t ≡ t
map-normal-identity t = erase-injective _ _
  (map-normal-erase (λ i → i) t ∙ relabel-identity (erase _ t))

map-normal-cong : (f g : L → M) → (∀ i → f i ≡ g i) → (t : Nf L n)
  → map-normal f t ≡ map-normal g t
map-normal-cong f g h t = erase-injective _ _
  (map-normal-erase f t ∙ relabel-cong f g h (erase _ t) ∙ sym (map-normal-erase g t))

map-normal-composition : (f : L → M) (g : M → K) (t : Nf L n)
  → map-normal g (map-normal f t) ≡ map-normal (λ i → g (f i)) t
map-normal-composition f g t = erase-injective _ _
  (map-normal-erase g (map-normal f t)
    ∙ cong (relabel g) (map-normal-erase f t)
    ∙ relabel-composition f g (erase _ t)
    ∙ sym (map-normal-erase (λ i → g (f i)) t))

map-normal-injective : (f : L → M)
  → (∀ i j → f i ≡ f j → i ≡ j) → (t u : Nf L n)
  → map-normal f t ≡ map-normal f u → t ≡ u
map-normal-injective f inj t u p = erase-injective t u
  (relabel-injective f inj _ _
    (sym (map-normal-erase f t) ∙ cong (erase _) p ∙ map-normal-erase f u))

dictionary-agreement : ∀ {a b n} (ι : Fin a → Fin b)
  (labelsA : Fin a → Nat) (labelsB : Fin b → Nat)
  → (∀ i → labelsB (ι i) ≡ labelsA i) → (t : Raw (Fin a) n)
  → relabel labelsB (relabel ι t) ≡ relabel labelsA t
dictionary-agreement ι labelsA labelsB h t = relabel-composition ι labelsB t
  ∙ relabel-cong (λ i → labelsB (ι i)) labelsA h t

-- BEGINALPHABETFRAGMENT
map-fragment : ∀ {a b s A} (ι : Fin a → Fin b)
  (labelsA : Fin a → Nat) (labelsB : Fin b → Nat)
  → (∀ i → labelsB (ι i) ≡ labelsA i)
  → Fragment labelsA s A → Fragment labelsB s A
map-fragment {b = b} {s} {A} ι labelsA labelsB h x =
  (map-normal ι (fragment-nf x) ,
    subst (_≤ s) (sym (map-normal-nodes ι (fragment-nf x))) (fragment-bound x))
  , PT.map (subst (λ t → Typ empty t A) (sym decoded)) (fragment-typing x)
  where
  decoded : relabel labelsB (erase (Fin b) (map-normal ι (fragment-nf x)))
    ≡ fragment-term x
  decoded = cong (relabel labelsB) (map-normal-erase ι (fragment-nf x))
    ∙ dictionary-agreement ι labelsA labelsB h (fragment-raw x)

map-fragment-raw : ∀ {a b s A} (ι : Fin a → Fin b)
  (labelsA : Fin a → Nat) (labelsB : Fin b → Nat)
  (h : ∀ i → labelsB (ι i) ≡ labelsA i) (x : Fragment labelsA s A)
  → fragment-raw (map-fragment ι labelsA labelsB h x) ≡ relabel ι (fragment-raw x)
map-fragment-raw ι labelsA labelsB h x = map-normal-erase ι (fragment-nf x)

map-fragment-term : ∀ {a b s A} (ι : Fin a → Fin b)
  (labelsA : Fin a → Nat) (labelsB : Fin b → Nat)
  (h : ∀ i → labelsB (ι i) ≡ labelsA i) (x : Fragment labelsA s A)
  → fragment-term (map-fragment ι labelsA labelsB h x) ≡ fragment-term x
map-fragment-term ι labelsA labelsB h x =
  cong (relabel labelsB) (map-fragment-raw ι labelsA labelsB h x)
  ∙ dictionary-agreement ι labelsA labelsB h (fragment-raw x)
-- ENDALPHABETFRAGMENT

map-fragment-injective : ∀ {a b s A} (ι : Fin a → Fin b)
  (labelsA : Fin a → Nat) (labelsB : Fin b → Nat)
  (h : ∀ i → labelsB (ι i) ≡ labelsA i)
  → (∀ i j → ι i ≡ ι j → i ≡ j) → (x y : Fragment labelsA s A)
  → map-fragment ι labelsA labelsB h x ≡ map-fragment ι labelsA labelsB h y → x ≡ y
map-fragment-injective ι labelsA labelsB h inj x y p =
  fragment-nf-injective x y (map-normal-injective ι inj _ _ (cong fragment-nf p))

fragment-term-injective : ∀ {a s A} (labels : Fin a → Nat)
  → (∀ i j → labels i ≡ labels j → i ≡ j) → (x y : Fragment labels s A)
  → fragment-term x ≡ fragment-term y → x ≡ y
fragment-term-injective labels inj x y p = fragment-raw-injective x y
  (relabel-injective labels inj (fragment-raw x) (fragment-raw y) p)

map-fragment-eq : ∀ {a b s t A B} (ι : Fin a → Fin b)
  (labelsA : Fin a → Nat) (labelsB : Fin b → Nat)
  (h : ∀ i → labelsB (ι i) ≡ labelsA i)
  (x : Fragment labelsA s A) (y : Fragment labelsA t B)
  → FragmentEq x y
  → FragmentEq (map-fragment ι labelsA labelsB h x) (map-fragment ι labelsA labelsB h y)
map-fragment-eq ι labelsA labelsB h x y p =
  subst₂ Beta (sym (map-fragment-term ι labelsA labelsB h x))
    (sym (map-fragment-term ι labelsA labelsB h y)) p
  where
  subst₂ : ∀ {S T : Set} (P : S → T → Set) {s s′ t t′}
    → s ≡ s′ → t ≡ t′ → P s t → P s′ t′
  subst₂ P p q v = subst (P _) q (subst (λ s → P s _) p v)

map-fragment-eq-reflect : ∀ {a b s t A B} (ι : Fin a → Fin b)
  (labelsA : Fin a → Nat) (labelsB : Fin b → Nat)
  (h : ∀ i → labelsB (ι i) ≡ labelsA i)
  (x : Fragment labelsA s A) (y : Fragment labelsA t B)
  → FragmentEq (map-fragment ι labelsA labelsB h x) (map-fragment ι labelsA labelsB h y)
  → FragmentEq x y
map-fragment-eq-reflect ι labelsA labelsB h x y p =
  subst (Beta (fragment-term x)) (map-fragment-term ι labelsA labelsB h y)
    (subst (λ t → Beta t (fragment-term (map-fragment ι labelsA labelsB h y)))
      (map-fragment-term ι labelsA labelsB h x) p)

map-fragment-identity : ∀ {a s A} (labels : Fin a → Nat) (x : Fragment labels s A)
  → map-fragment (λ i → i) labels labels (λ i → refl) x ≡ x
map-fragment-identity labels x = fragment-nf-injective _ _ (map-normal-identity _)

map-fragment-composition : ∀ {a b c s A} (ι : Fin a → Fin b) (κ : Fin b → Fin c)
  (labelsA : Fin a → Nat) (labelsB : Fin b → Nat) (labelsC : Fin c → Nat)
  (h : ∀ i → labelsB (ι i) ≡ labelsA i) (k : ∀ i → labelsC (κ i) ≡ labelsB i)
  (x : Fragment labelsA s A)
  → map-fragment κ labelsB labelsC k (map-fragment ι labelsA labelsB h x)
      ≡ map-fragment (λ i → κ (ι i)) labelsA labelsC (λ i → k (ι i) ∙ h i) x
map-fragment-composition ι κ labelsA labelsB labelsC h k x =
  fragment-nf-injective _ _ (map-normal-composition ι κ (fragment-nf x))

map-fragment-cong : ∀ {a b s A} (ι κ : Fin a → Fin b)
  (labelsA : Fin a → Nat) (labelsB : Fin b → Nat)
  (h : ∀ i → labelsB (ι i) ≡ labelsA i) (k : ∀ i → labelsB (κ i) ≡ labelsA i)
  → (∀ i → ι i ≡ κ i) → (x : Fragment labelsA s A)
  → map-fragment ι labelsA labelsB h x ≡ map-fragment κ labelsA labelsB k x
map-fragment-cong ι κ labelsA labelsB h k p x =
  fragment-nf-injective _ _ (map-normal-cong ι κ p (fragment-nf x))

map-fragment-embed : ∀ {a b s t A} (ι : Fin a → Fin b)
  (labelsA : Fin a → Nat) (labelsB : Fin b → Nat)
  (h : ∀ i → labelsB (ι i) ≡ labelsA i) (p : s ≤ t) (x : Fragment labelsA s A)
  → map-fragment ι labelsA labelsB h (embed-fragment p x)
      ≡ embed-fragment p (map-fragment ι labelsA labelsB h x)
map-fragment-embed ι labelsA labelsB h p x = fragment-nf-injective _ _ refl

map-fragment-convert : ∀ {a b s A B r} (ι : Fin a → Fin b)
  (labelsA : Fin a → Nat) (labelsB : Fin b → Nat)
  (h : ∀ i → labelsB (ι i) ≡ labelsA i) (sorted : Typ empty B (U r))
  (eq : Beta A B) (x : Fragment labelsA s A)
  → map-fragment ι labelsA labelsB h (convert-fragment sorted eq x)
      ≡ convert-fragment sorted eq (map-fragment ι labelsA labelsB h x)
map-fragment-convert ι labelsA labelsB h sorted eq x = fragment-nf-injective _ _ refl

-- The actual raw reducer commutes with every alphabet map, not only injections.
normalize-alphabet : ∀ {a b n} (ι : Fin a → Fin b) d (t : Raw (Fin a) n)
  → relabel ι (rounds d t) ≡ rounds d (relabel ι t)
normalize-alphabet = relabel-rounds

-- A concrete directed alphabet system: labels are the first a naturals.
include-alphabet : ∀ {a b} → a ≤ b → Fin a → Fin b
include-alphabet {b = b} p i = fromℕ' b (toℕ i) (≤-trans (toℕ<n i) p)

include-label : ∀ {a b} (p : a ≤ b) (i : Fin a)
  → toℕ (include-alphabet p i) ≡ toℕ i
include-label {b = b} p i = toFromId' b (toℕ i) _

include-alphabet-injective : ∀ {a b} (p : a ≤ b) (i j : Fin a)
  → include-alphabet p i ≡ include-alphabet p j → i ≡ j
include-alphabet-injective p i j eq = inj-toℕ
  (sym (include-label p i) ∙ cong toℕ eq ∙ include-label p j)

enlarge-alphabet : ∀ {a b s A} → a ≤ b
  → Fragment {a} toℕ s A → Fragment {b} toℕ s A
enlarge-alphabet p = map-fragment (include-alphabet p) toℕ toℕ (include-label p)

enlarge-alphabet-term : ∀ {a b s A} (p : a ≤ b) (x : Fragment {a} toℕ s A)
  → fragment-term (enlarge-alphabet p x) ≡ fragment-term x
enlarge-alphabet-term p x = map-fragment-term (include-alphabet p) toℕ toℕ (include-label p) x

enlarge-alphabet-injective : ∀ {a b s A} (p : a ≤ b) (x y : Fragment {a} toℕ s A)
  → enlarge-alphabet p x ≡ enlarge-alphabet p y → x ≡ y
enlarge-alphabet-injective p = map-fragment-injective (include-alphabet p)
  toℕ toℕ (include-label p) (include-alphabet-injective p)

enlarge-alphabet-identity : ∀ {a s A} (x : Fragment {a} toℕ s A)
  → enlarge-alphabet ≤-refl x ≡ x
enlarge-alphabet-identity x = map-fragment-cong (include-alphabet ≤-refl)
  (λ i → i) toℕ toℕ (include-label ≤-refl) (λ i → refl)
  (λ i → inj-toℕ (include-label ≤-refl i)) x ∙ map-fragment-identity toℕ x

enlarge-alphabet-composition : ∀ {a b c s A} (p : a ≤ b) (q : b ≤ c)
  (x : Fragment {a} toℕ s A)
  → enlarge-alphabet q (enlarge-alphabet p x) ≡ enlarge-alphabet (≤-trans p q) x
enlarge-alphabet-composition p q x =
  map-fragment-composition (include-alphabet p) (include-alphabet q)
    toℕ toℕ toℕ (include-label p) (include-label q) x
  ∙ map-fragment-cong (λ i → include-alphabet q (include-alphabet p i))
      (include-alphabet (≤-trans p q)) toℕ toℕ
      (λ i → include-label q (include-alphabet p i) ∙ include-label p i)
      (include-label (≤-trans p q))
      (λ i → inj-toℕ (include-label q (include-alphabet p i) ∙ include-label p i
        ∙ sym (include-label (≤-trans p q) i))) x

-- Relabelling also commutes with the executable dependent application.
-- The enlarged alphabet must meet its own finite-state capacity premise.
apply-alphabet-raw : ∀ {a b s t X Y} (ι : Fin a → Fin b)
  (labelsA : Fin a → Nat) (labelsB : Fin b → Nat)
  (h : ∀ i → labelsB (ι i) ≡ labelsA i) (d : Nat)
  (f : Fragment labelsA s (pi X Y)) (y : Fragment labelsA t X)
  (hp : PT.∥ Typ empty (pi X Y) (U d) ∥₁)
  (smallA : a ≤ inputSize (fragment-nf f) (fragment-nf y))
  (smallB : b ≤ inputSize (fragment-nf (map-fragment ι labelsA labelsB h f))
    (fragment-nf (map-fragment ι labelsA labelsB h y)))
  → relabel ι (fragment-raw (Application.apply-fragment labelsA d f y hp smallA))
      ≡ fragment-raw (Application.apply-fragment labelsB d
        (map-fragment ι labelsA labelsB h f) (map-fragment ι labelsA labelsB h y) hp smallB)
apply-alphabet-raw ι labelsA labelsB h d f y hp smallA smallB =
  cong (relabel ι) (Application.apply-fragment-raw labelsA d f y hp smallA)
  ∙ relabel-rounds ι d (app (fragment-raw f) (fragment-raw y))
  ∙ cong (rounds d) (cong₂ app
      (sym (map-fragment-raw ι labelsA labelsB h f))
      (sym (map-fragment-raw ι labelsA labelsB h y)))
  ∙ sym (Application.apply-fragment-raw labelsB d
      (map-fragment ι labelsA labelsB h f) (map-fragment ι labelsA labelsB h y) hp smallB)
