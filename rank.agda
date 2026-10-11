open import Data.Fin.Base using (Fin; suc; zero)
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Vec.Base

wk : ∀ {m n} → (Fin m → Fin n) → Fin (suc m) → Fin (suc n)
wk _ zero = zero
wk f (suc n) = suc (f n)

data Syn (n : ℕ) : Set where
  𝓤 : ℕ → Syn n
  Π : Syn n → Syn (suc n) → Syn n
  ` : Fin n → Syn n
  λ' : Syn n → Syn (suc n) → Syn n
  _$_ : Syn n → Syn n → Syn n

rename : ∀ {m n} → (Fin m → Fin n) → Syn m → Syn n
rename _ (𝓤 x) = 𝓤 x
rename f (Π T U) = Π (rename f T) (rename (wk f) U)
rename f (` x) = ` (f x)
rename f (λ' T t) = λ' (rename f T) (rename (wk f) t)
rename f (t $ u) = rename f t $ rename f u

tp : ∀ {m n} → (Fin m → Syn n) → Fin (suc m) → Syn (suc n)
tp f zero = ` zero
tp f (suc i) = rename suc (f i)

replace : ∀ {m n} → (Fin m → Syn n) → Syn m → Syn n
replace _ (𝓤 x) = 𝓤 x
replace f (Π t t₁) = Π (replace f t) (replace (tp f) t₁)
replace f (` x) = f x
replace f (λ' t t₁) = λ' (replace f t) (replace (tp f) t₁)
replace f (t $ t₁) = replace f t $ replace f t₁

data Ctx : ℕ → Set where
  ε : Ctx 0
  _,x:_ : ∀ {n} → Ctx n → Syn n → Ctx (suc n)
  _,x:=_∷_ : ∀ {n} → Ctx n → Syn n → Syn n → Ctx (suc n)

data Args (n : ℕ) : Set where
  [] : Args n
  _∷_ : Syn n → Args n → Args n

shift : ∀ {n} → Args n → Args (suc n)
shift [] = []
shift (a ∷ as) = rename suc a ∷ shift as

subst : ∀ {n} → Syn n → Args (suc n) → Args n
subst _ [] = []
subst t (a ∷ as) = replace (λ { zero → t ; (suc i) → ` i }) a ∷ subst t as

-- 'valueOf Γ K usᴷ usᵀ default' assumes that 'K usᴷ' is a kind of 'T' for some
-- 'T' such that 'T usᵀ' is a type, and computes overapproximation of a sort of
-- 'T usᵀ' (where 'default' is used as an upper bound).
valueOf : ∀ {n} → Ctx n → Syn n → Args n → Args n → ℕ → ℕ
valueOf _ (𝓤 _) (_ ∷ _) _ _ = 0 -- '𝓤 usᴷ' is not a correct kind
valueOf _ (𝓤 _) [] (_ ∷ _) _ = 0 -- if 'usᵀ' is nonempty, '𝓤' cannot be a kind of 'T'
valueOf _ (𝓤 r) [] [] _ = r
valueOf _ (Π _ _) (_ ∷ _) _ _ = 0 -- 'Π usᴷ' is not a correct kind
valueOf _ (Π _ _) [] [] _ = 0 -- here, 'T' is a function which is not a type.
valueOf Γ (Π T U) [] (t ∷ us) = valueOf (Γ ,x:= t ∷ T) U [] (shift us)
valueOf (_ ,x: _) (` zero) _ _ _ = 0 -- an unknown variable is not a correct sort
valueOf (Γ ,x:= t ∷ _) (` zero) us us' default = default
    -- "valueOf Γ t (subst t us) (subst t us')" is correct, but isn't ER
    -- (and Agda doesn't even consider this case to be terminating).
    -- We need some upper bound, so to account for this case we can take all
    -- '𝓤 r' which occur in the term as possibly appearing as such 't'.
valueOf (Γ ,x: _) (` (suc i)) us us' =
    valueOf Γ (` i) (subst (𝓤 0) us) (subst (𝓤 0) us')
    -- choice of substitution doesn't matter
    -- since the result in Var case doesn't depend on it anyway
valueOf (Γ ,x:= t ∷ _) (` (suc i)) us us' =
    valueOf Γ (` i) (subst t us) (subst t us')
valueOf _ (λ' _ _) [] _ _ = 0 -- 'λ' is not a correct kind
valueOf Γ (λ' U t) (u ∷ us) us' =
    valueOf (Γ ,x:= u ∷ U) t (shift us) (shift us')
valueOf Γ (t $ u) us us' = valueOf Γ t (u ∷ us) us'

-- Simplified definition of 'valueOf' truly assuming well-typedness.
valueOf' : ∀ {n} → Syn n → ℕ → ℕ
valueOf' (𝓤 r) _ = r
valueOf' (Π _ U) = valueOf' U
valueOf' (` _) default = default
valueOf' (λ' _ t) = valueOf' t
valueOf' (t $ _) = valueOf' t

-- 'rankOf Γ T us default' assumes that 'T us' is a type
-- and computes overapproximation of its sort
-- (where 'default' is some upper bound for rank of variables).
rankOf : ∀ {n} → Ctx n → Syn n → Args n → ℕ → ℕ
rankOf _ (𝓤 _) _ _ = 0 -- either '𝓤 r : 𝓤 0' or incorrect type
rankOf Γ (Π T U) _ d = suc (rankOf Γ T [] d) ⊔ rankOf (Γ ,x: T) U [] d
rankOf (Γ ,x: T) (` zero) us = valueOf Γ T [] (subst (𝓤 0) us)
    -- choice of substitution doesn't matter
    -- since values of arguments aren't used in 'valueOf' anyway
rankOf (Γ ,x:= t ∷ T) (` zero) us = valueOf Γ T [] (subst t us)
rankOf (Γ ,x: _) (` (suc i)) us = rankOf Γ (` i) (subst (𝓤 0) us)
    -- choice of substitution doesn't matter
    -- since values of arguments aren't used in 'valueOf' anyway
rankOf (Γ ,x:= t ∷ _) (` (suc i)) us = rankOf Γ (` i) (subst t us)
rankOf Γ (λ' U t) [] _ = 0 -- 'λ' is not a type
rankOf Γ (λ' U t) (u ∷ us) = rankOf (Γ ,x:= u ∷ U) t (shift us)
rankOf Γ (t $ u) us = rankOf Γ t (u ∷ us)

-- Simplified definition of 'rankOf' truly assuming well-typedness.
rankOf' : ∀ {n} → Ctx n → Syn n → ℕ → ℕ
rankOf' _ (𝓤 _) _ = 0
rankOf' Γ (Π T U) d = suc (rankOf' Γ T d) ⊔ rankOf' (Γ ,x: T) U d
rankOf' (_ ,x: T) (` zero) = valueOf' T
rankOf' (_ ,x:= _ ∷ T) (` zero) = valueOf' T
rankOf' (Γ ,x: _) (` (suc x)) = rankOf' Γ (` x)
rankOf' (Γ ,x:= _ ∷ _) (` (suc x)) = rankOf' Γ (` x)
rankOf' Γ (λ' T t) = rankOf' (Γ ,x: T) t
rankOf' Γ (t $ t₁) = rankOf' Γ t

-- 'maxAbsRank Γ t us default' assumes that 't us' is a well-typed term and
-- computes overapproximation of a maximal rank of abstractions present in 't'
-- (where 'default' is some upper bound for rank of variables)
maxAbsRank : ∀ {n} → Ctx n → Syn n → Args n → ℕ → ℕ
maxAbsRank _ (𝓤 r) _ _ = 0 -- '𝓤' doesn't contain any abstractions
maxAbsRank Γ (Π T U) [] d = maxAbsRank Γ T [] d ⊔ maxAbsRank (Γ ,x: T) U [] d
maxAbsRank _ (Π T U) (_ ∷ _) _ = 0 -- 'Π us' is not a correct term
maxAbsRank _ (` _) _ _ = 0 -- variable doesn't contain any abstractions
maxAbsRank Γ (λ' U t) [] d =
  rankOf Γ U [] d ⊔ maxAbsRank Γ U [] d ⊔ maxAbsRank (Γ ,x: U) t [] d
maxAbsRank Γ (λ' U t) (u ∷ us) d =
  rankOf Γ U [] d ⊔ maxAbsRank Γ U [] d
  ⊔ maxAbsRank (Γ ,x:= u ∷ U) t (shift us) d
maxAbsRank Γ (t $ u) us d = maxAbsRank Γ t (u ∷ us) d ⊔ maxAbsRank Γ u [] d

-- Simplified definition of 'maxAbsRank' truly assuming well-typedness.
maxAbsRank' : ∀ {n} → Ctx n → Syn n → ℕ → ℕ
maxAbsRank' _ (𝓤 _) _ = 0
maxAbsRank' Γ (Π T U) d = maxAbsRank' Γ T d ⊔ maxAbsRank' (Γ ,x: T) U d
maxAbsRank' _ (` _) _ = 0
maxAbsRank' Γ (λ' T t) d =
    rankOf' Γ T d ⊔ maxAbsRank' Γ T d ⊔ maxAbsRank' (Γ ,x: T) t d
maxAbsRank' Γ (t $ u) d = maxAbsRank' Γ t d ⊔ maxAbsRank' Γ u d

-- rankOf' + maxAbsRank' in a single traversal
rankOf'' : ∀ {n} → Ctx n → Syn n → ℕ → ℕ × ℕ
rankOf'' _ (𝓤 _) _ = 0 , 0
rankOf'' Γ (Π T U) d =
    let (rᵀ , aᵀ) = rankOf'' Γ T d
        (rᵁ , aᵁ) = rankOf'' (Γ ,x: T) U d
     in (suc rᵀ ⊔ rᵁ , aᵀ ⊔ aᵁ)
rankOf'' Γ (` x) d = (rankOf' Γ (` x) d , 0)
rankOf'' Γ (λ' T t) d =
    let (rᵀ , aᵀ) = rankOf'' Γ T d
        (rᵗ , aᵗ) = rankOf'' (Γ ,x: T) t d
     in (rᵗ , rᵀ ⊔ aᵀ ⊔ aᵗ)
rankOf'' Γ (t $ u) d =
    let (rᵗ , aᵗ) = rankOf'' Γ t d
        (_  , aᵘ) = rankOf'' Γ u d
     in (rᵗ , aᵗ ⊔ aᵘ)

-- rankOf'' where ranks in context are precomputed
rankOf''' : ∀ {n} → Vec ℕ n → Syn n → ℕ → ℕ × ℕ
rankOf''' _ (𝓤 _) _ = 0 , 0
rankOf''' Γ (Π T U) d =
    let (rᵀ , aᵀ) = rankOf''' Γ T d
        (rᵁ , aᵁ) = rankOf''' (valueOf' T d ∷ Γ) U d
     in (suc rᵀ ⊔ rᵁ , aᵀ ⊔ aᵁ)
rankOf''' Γ (` x) d = (lookup Γ x , 0)
rankOf''' Γ (λ' T t) d =
    let (rᵀ , aᵀ) = rankOf''' Γ T d
        (rᵗ , aᵗ) = rankOf''' (valueOf' T d ∷ Γ) t d
     in (rᵗ , rᵀ ⊔ aᵀ ⊔ aᵗ)
rankOf''' Γ (t $ u) d =
    let (rᵗ , aᵗ) = rankOf''' Γ t d
        (_  , aᵘ) = rankOf''' Γ u d
     in (rᵗ , aᵗ ⊔ aᵘ)

-- rankOf'''+valueOf' in a single traversal
traversal : ∀ {n} → Vec ℕ n → Syn n → ℕ → ℕ × ℕ × ℕ
traversal _ (𝓤 r) _ = r , 0 , 0
traversal Γ (Π T U) d =
    let (vᵀ , rᵀ , aᵀ) = traversal Γ T d
        (vᵁ , rᵁ , aᵁ) = traversal (vᵀ ∷ Γ) U d
     in (vᵁ , suc rᵀ ⊔ rᵁ , aᵀ ⊔ aᵁ)
traversal Γ (` x) d = (d , lookup Γ x , 0)
traversal Γ (λ' T t) d =
    let (vᵀ , rᵀ , aᵀ) = traversal Γ T d
        (vᵗ , rᵗ , aᵗ) = traversal (vᵀ ∷ Γ) t d
     in (vᵗ , rᵗ , rᵀ ⊔ aᵀ ⊔ aᵗ)
traversal Γ (t $ u) d =
    let (vᵗ , rᵗ , aᵗ) = traversal Γ t d
        (_  , _  , aᵘ) = traversal Γ u d
     in (vᵗ , rᵗ , aᵗ ⊔ aᵘ)

maxRankLiteral : ∀ {n} → Syn n → ℕ
maxRankLiteral (𝓤 x) = x
maxRankLiteral (Π t t₁) = maxRankLiteral t ⊔ maxRankLiteral t₁
maxRankLiteral (` _) = 0
maxRankLiteral (λ' t t₁) = maxRankLiteral t ⊔ maxRankLiteral t₁
maxRankLiteral (t $ t₁) = maxRankLiteral t ⊔ maxRankLiteral t₁

approxSteps : Syn 0 → ℕ
approxSteps t = maxAbsRank ε t [] (maxRankLiteral t)

-- optimized version: two linear traversals
approxSteps' : Syn 0 → ℕ
approxSteps' t = let (_ , _ , aᵗ) = traversal [] t (maxRankLiteral t) in aᵗ
