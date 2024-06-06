```agda
module test where
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤?_; _<?_; _≟_; pred)
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ; suc-injective; <-cmp)
-- open import Data.Fin using (Fin; zero; suc; _≟_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.List using (List; []; _∷_; _++_; [_])
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; cong; subst; sym; _≢_; cong₂)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary using (Decidable)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤)


open import Agda.Primitive using (Level; lsuc; _⊔_)
-- variable 


deterministic : ∀ {A : Set} → (A → A → Set) → Set
deterministic {A} _~>_ = ∀ (a a₁ a₂ : A) → a ~> a₁ → a ~> a₂ → a₁ ≡ a₂

rel-normal : ∀ {A : Set} → (A → A → Set) → A → Set
rel-normal {A} _~>_ a = ¬ (Σ[ a' ∈ A ] (a ~> a'))

record evaluation-system (A : Set) (_~>_ : A → A → Set) (normal neutral abs : A → Set) : Set where
  field 
    det-rel : deterministic _~>_
    rel-normal→normal : ∀ (a : A) → rel-normal _~>_ a → normal a
    normal→rel-normal : ∀ (a : A) → normal a → rel-normal _~>_ a
    normal∧¬abs→neutral : ∀ (a : A) → (normal a × ¬ abs a) → neutral a
    neutral→normal∧¬abs : ∀ (a : A) → neutral a → (normal a × ¬ abs a)


infixl 20 _·_
infix 40 `_
data term : Set where
  `_  : ℕ → term 
  ƛ   : term → term
  _·_ : term → term → term

-- shift : ℕ → ℕ → term → term

-- shift n k (` x)  with x ≤? k 
-- ... | yes x≤k = ` x
-- ... | no x>k = ` (x + n)
-- shift n k (ƛ t) = ƛ (shift n (k + 1) t)
-- shift n k (t₁ · t₂) = shift n k t₁ · shift n k t₂


-- _[_<-_] : term → ℕ → term → term 
-- (` x) [ n <- s ] with x ≟ n 
-- ... | yes x=n = shift n 0 s
-- ... | no x≠n = ` x
-- ƛ t [ n <- s ] = ƛ (t [ suc n <- s ])
-- (t₁ · t₂) [ n <- s ] = (t₁ [ n <- s ]) · (t₂ [ n <- s ])

-- _↓_ : term → ℕ → term 
-- (` x) ↓ n with x ≤? n 
-- ... | yes x≤n = ` x
-- ... | no x>n = ` pred x
-- ƛ t ↓ n = ƛ (t ↓ (suc n))
-- (t₁ · t₂) ↓ n = (t₁ ↓ n) · (t₂ ↓ n)

-- _ : (ƛ ((` 0) · (` 1)))[ 0 <- (ƛ (` 0)) ] ≡ ƛ ((` 0) · (ƛ (` 0)))
-- _ = refl

-- _ : (ƛ ((` 0) · (` 1)))[ 0 <- (ƛ (` 1)) ] ≡ ƛ ((` 0) · (ƛ (` 2)))
-- _ = refl



data neutral : term -> Set where
  neutral-var : ∀ (n : ℕ) → neutral (` n)
  neutral-app : ∀ (t₁ t₂ : term) → neutral t₁ → neutral (t₁ · t₂) 

data normal : term → Set where 
  normal-neutral : ∀ (t : term) → neutral t → normal t 
  normal-abs : ∀ (t : term) → normal t → normal (ƛ t) 


abs : term → Set 
abs (ƛ t) = ⊤
abs _ = ⊥

data _~>_ : term → term → Set where 
-- TODO : Step


  
size : term → ℕ 
size (` x) = 0
size (ƛ t) = suc (size t)
size (t · _) = suc (size t)



head-red-eval-system : evaluation-system term (_~>_) normal neutral abs
head-red-eval-system = record
  { det-rel = det-rel
  ; rel-normal→normal = rel-normal→normal
  ; normal→rel-normal = normal→rel-normal
  ; normal∧¬abs→neutral = normal×¬abs→neutral
  ; neutral→normal∧¬abs = neutral→normal∧¬abs
  }
  where 
    postulate
      det-rel : deterministic _~>_ 
    -- det-rel t t₁ t₂ t~>t₁ t~>t₂ = {!   !}

      rel-normal→normal : ∀ (t : term) → rel-normal (_~>_) t → normal t 
    -- rel-normal→normal t rel-normal-t = {!   !}

    postulate
      normal→rel-normal : ∀ (t : term) → normal t → rel-normal (_~>_) t 
    -- normal→rel-normal t = {!   !}

    normal×¬abs→neutral : ∀ (t : term) → normal t × ¬ abs t → neutral t 
    normal×¬abs→neutral (` x) (normal-t , ¬abs-t) = neutral-var x
    normal×¬abs→neutral (ƛ t) (normal-t , ¬abs-t) = ⊥-elim (¬abs-t Data.Unit.tt)
    normal×¬abs→neutral (t₁ · t₂) (normal-neutral _ (neutral-app _ _ neutral-t₁) , ¬abs-t) = neutral-app t₁ t₂ neutral-t₁
  
    neutral→normal∧¬abs : ∀ (t : term) → neutral t → normal t × ¬ abs t
    neutral→normal∧¬abs (` n) (neutral-var n) = normal-neutral (` n) (neutral-var n) , λ z → z
    neutral→normal∧¬abs (t₁ · t₂) (neutral-app t₁ t₂ neutral-t) = normal-neutral (t₁ · t₂) (neutral-app t₁ t₂ neutral-t) , (λ x → x)  

postulate 
  AtomicType :  Set
  valid :  AtomicType → Set
  _≡ₐ_ : AtomicType  → AtomicType → Set
postulate 
  ≡ₐ-dec :  Decidable (_≡ₐ_)

data tightConstant {ℓ : Level} : Set  (lsuc ℓ) where
  TCNeutral : tightConstant
  TCAbs : tightConstant
  
data type {ℓ : Level} : Set (lsuc ℓ)
data multitype {ℓ : Level} : Set  (lsuc ℓ)

data type {ℓ} where 
    TyTight : tightConstant {ℓ} -> type
    TyAtomic : ∀ (t : AtomicType) → valid t → type 
    TyFun : multitype {ℓ} -> type {ℓ} -> type {ℓ}

data multitype {ℓ} where 
    mtEmpty : multitype
    mtCons : type {ℓ} -> multitype {ℓ} -> multitype
    
_≡ₜ_ : ∀ {ℓ : Level} → type {ℓ} -> type {ℓ} -> Bool 
_#_  : ∀ {ℓ : Level} → multitype {ℓ} -> type {ℓ} -> ℕ
_⊆_  : ∀ {ℓ : Level} → multitype {ℓ} -> multitype {ℓ} -> Bool
_≡ₘ_ : ∀ {ℓ : Level} → multitype {ℓ} -> multitype {ℓ} -> Bool 
(TyTight TCNeutral) ≡ₜ (TyTight TCNeutral) = true
(TyTight TCNeutral) ≡ₜ (TyTight TCAbs)     = false
(TyTight TCAbs)     ≡ₜ (TyTight TCNeutral) = false
(TyTight TCAbs)     ≡ₜ (TyTight TCAbs)     = true
(TyTight _)         ≡ₜ (TyAtomic _ _)        = false
(TyTight _)         ≡ₜ (TyFun _ _)         = false
(TyAtomic t₁ _)     ≡ₜ (TyTight x)         = false
(TyAtomic t₁ _)     ≡ₜ (TyAtomic t₂ _) with ≡ₐ-dec t₁ t₂ 
... | yes _ = true
... | no _ = false
(TyAtomic t₁ _)     ≡ₜ (TyFun x t)         = false
(TyFun _ _)         ≡ₜ (TyTight x₁)        = false
(TyFun _ _)         ≡ₜ (TyAtomic _ _)        = false
(TyFun mt₁ t₁)      ≡ₜ (TyFun mt₂ t₂)      = (mt₁ ≡ₘ mt₂) ∧ (t₁ ≡ₜ t₂)

mtEmpty       # t = zero
(mtCons t' m) # t with t ≡ₜ t' 
... | true = suc (m # t)
... | false = m # t

mtEmpty         ⊆ mt₂ = true
(mtCons x mt₁)  ⊆ mt₂ with (mt₁ # x) <? (mt₂ # x)
... | yes _ = mt₁ ⊆ mt₂
... | no _ = false

mt₁ ≡ₘ mt₂ = (mt₁ ⊆ mt₂) ∧ (mt₂ ⊆ mt₁)

-- postulate 
--   _⊎_ : multitype → multitype → multitype

-- data ctx : ℕ → Set where 
--   [] : ctx zero
--   _::_ : ∀ {n} → multitype → ctx n → ctx (S n)


-- _⊎c_ : ∀ {n} → ctx n → ctx n → ctx n 
-- [] ⊎c [] = []
-- (t₁ :: Γ₁) ⊎c (t₂ :: Γ₂) = (t₁ ⊎ t₂) :: (Γ₁ ⊎c Γ₂)


-- postulate
--   _⊎_ : multitype {ℓ} → multitype {ℓ} → multitype
--   ⊎-assoc : ∀ (mt1 mt2 mt3 : multitype) → ((mt1 ⊎ mt2) ⊎ mt3) ≡ (mt1 ⊎ (mt2 ⊎ mt3))

-- data ctx : ℕ → Set₁ where 
--   [] : ctx zero
--   _::_ : ∀ {n} → multitype → ctx n → ctx (suc n)


-- _⊎c_ : ∀ {n} → ctx n → ctx n → ctx n 
-- [] ⊎c [] = []
-- (t₁ :: Γ₁) ⊎c (t₂ :: Γ₂) = (t₁ ⊎ t₂) :: (Γ₁ ⊎c Γ₂)


-- ⊎c-assoc : ∀ {n : ℕ} (c1 c2 c3 : ctx n) → (c1 ⊎c c2) ⊎c c3 ≡ c1 ⊎c (c2 ⊎c c3)
-- ⊎c-assoc [] [] [] = refl
-- ⊎c-assoc (x1 :: c1) (x2 :: c2) (x3 :: c3) rewrite ⊎-assoc x1 x2 x3 | ⊎c-assoc c1 c2 c3 =  refl






-- -- mutual
-- --   data env : ℕ → Set where
-- --     nil  : env zero
-- --     _,-_ : ∀ {n} → env n → clo → env (suc n)

-- --   clo = Σ[ n ∈ ℕ ] env n × term n

-- -- data stk : Set where
-- --   emp  : stk
-- --   _-,_ : clo → stk → stk

-- -- infixr 10 _-,_

-- -- record configuration : Set where
-- --   constructor ⟨_⋆_⟩
-- --   field
-- --     closure : clo
-- --     stack   : stk

-- -- infix  20 ⟨_⋆_⟩

-- -- data _⇒_ : configuration → configuration → Set where
-- --   grab : ∀ {n η c π}   → ⟨ suc n , η ,- c , ` zero    ⋆ π ⟩      ⇒ ⟨ c                      ⋆ π ⟩
-- --   skip : ∀ {n η c i π} → ⟨ suc n , η ,- c , ` (suc i) ⋆ π ⟩      ⇒ ⟨ n ,     η        , ` i ⋆ π ⟩
-- --   push : ∀ {n η t s π} → ⟨     n , η      , t · s     ⋆ π ⟩      ⇒ ⟨ n ,     η        , t   ⋆ (n , η , s) -, π ⟩
-- --   pop  : ∀ {n η t c π} → ⟨     n , η      , ƛ t       ⋆ c -, π ⟩ ⇒ ⟨ suc n , (η ,- c) , t   ⋆ π ⟩

-- -- infixr 10 _⇒_

-- -- init : term 0 → configuration
-- -- init t = ⟨ 0 , nil , t ⋆ emp ⟩

-- -- data reduces : ℕ → configuration → Set where
-- --   stop : ∀ {n} η t → reduces 0 ⟨ n , η , ƛ t ⋆ emp ⟩
-- --   step : ∀ {n p q} → p ⇒ q → reduces n q → reduces (suc n) p

-- -- deterministic : ∀ {p q q'} → p ⇒ q → p ⇒ q' → q ≡ q'
-- -- deterministic grab grab = refl
-- -- deterministic skip skip = refl
-- -- deterministic push push = refl
-- -- deterministic pop pop = refl

-- -- reduces-det : ∀ {p m n} → reduces m p → reduces n p → m ≡ n
-- -- reduces-det (stop η t)   (stop .η .t) = refl
-- -- reduces-det (step s1 r1) (step s2 r2) with deterministic s1 s2
-- -- ... | refl = cong suc (reduces-det r1 r2)


-- -- data type : Set where
-- --   ⋆    : type
-- --   _↦_ : List type → type → type

-- -- infixr 30 _↦_

-- -- data ctx : ℕ → Set where
-- --   nil : ctx zero
-- --   _,-_ : ∀ {n} → ctx n → List type → ctx (suc n)

  
-- -- empty : ∀{n} → ctx n
-- -- empty {zero}  = nil
-- -- empty {suc n} = empty {n} ,- []

-- -- _+++_ : ∀{n} → ctx n → ctx n → ctx n
-- -- nil        +++ nil       = nil
-- -- (Γ₁ ,- σ₁) +++ (Γ₂ ,- σ₂) = (Γ₁ +++ Γ₂) ,- (σ₁ ++ σ₂)

-- -- module permutations {X : Set} where
-- --   data _⋈_ : List X -> List X -> Set where
-- --     nil     : [] ⋈ []
-- --     skip    : ∀ {x l₁ l₂}  -> l₁ ⋈ l₂ -> (x ∷ l₁) ⋈ (x ∷ l₂)
-- --     swap    : ∀ {x y l}    ->           (x ∷ y ∷ l) ⋈ (y ∷ x ∷ l)
-- --     ⋈-trans : ∀ {l₁ l₂ l₃} -> l₁ ⋈ l₂ -> l₂ ⋈ l₃ -> l₁ ⋈ l₃

-- --   ⋈-refl : ∀ {l} -> l ⋈ l
-- --   ⋈-refl {[]}    = nil
-- --   ⋈-refl {x ∷ l} = skip ⋈-refl
-- -- open permutations

-- -- data _⋈ctx_ : ∀ {n} → ctx n → ctx n → Set where
-- --   nil : nil ⋈ctx nil
-- --   _,-_ : ∀ {n}{Γ₁ Γ₂ : ctx n}{σ₁ σ₂} → Γ₁ ⋈ctx Γ₂ → σ₁ ⋈ σ₂ → (Γ₁ ,- σ₁) ⋈ctx (Γ₂ ,- σ₂)

-- -- ⋈ctx-refl : ∀ {n}{Γ : ctx n} → Γ ⋈ctx Γ
-- -- ⋈ctx-refl {Γ = nil}    = nil
-- -- ⋈ctx-refl {Γ = Γ ,- σ} = ⋈ctx-refl ,- ⋈-refl

-- -- data _⊢v_⦂_ : ∀ {n} → ctx n → Fin n → type → Set where
-- --   zero : ∀ {n τ} → (empty {n} ,- [ τ ]) ⊢v zero ⦂ τ
-- --   suc  : ∀ {n τ i}{Γ : ctx n} → Γ ⊢v i ⦂ τ → (Γ ,- []) ⊢v (suc i) ⦂ τ


-- -- mutual
-- --   data _⊢_⦂_ : ∀ {n} → ctx n → term n → type → Set where
-- --     var : ∀ {n τ i}{Γ : ctx n} →
-- --           Γ ⊢v i ⦂ τ →
-- --           Γ ⊢ ` i ⦂ τ
-- --     lam : ∀ {n σ τ t}{Γ : ctx n} →
-- --           (Γ ,- σ) ⊢ t ⦂ τ →
-- --           Γ ⊢ ƛ t ⦂ (σ ↦ τ)
-- --     app : ∀ {n σ τ s t}{Γ Γ₁ Γ₂ : ctx n} →
-- --           Γ₁ ⊢ s ⦂ (σ ↦ τ) →
-- --           Γ₂ ⊢ t ⦂' σ →
-- --           (Γ₁ +++ Γ₂) ⋈ctx Γ →
-- --           Γ ⊢ (s · t) ⦂ τ
-- --     lam⋆ : ∀ {n t} →
-- --           empty {n} ⊢ ƛ t ⦂ ⋆

-- --   data _⊢_⦂'_ : ∀ {n} → ctx n → term n → List type → Set where
-- --     nil : ∀ {n}{t : term n} →
-- --           empty ⊢ t ⦂' []
-- --     _,~_∷_ : ∀ {n t σ τ}{Γ₁ Γ₂ Γ : ctx n} →
-- --           Γ₁ ⊢ t ⦂ τ →
-- --           (Γ₁ +++ Γ₂) ⋈ctx Γ →
-- --           Γ₂ ⊢ t ⦂' σ →
-- --           Γ ⊢ t ⦂' (τ ∷ σ)


``` 

```agda
-- module test where
-- open import Relation.Nullary
-- open import Data.Bool using (Bool; true; false; _∧_)
-- open import Data.Nat using (ℕ; zero; suc; _+_; _≤?_; _≟_)
-- open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ; suc-injective)
-- open import Data.Fin using (Fin; zero; suc; _≟_; toℕ; fromℕ; raise; cast; inject+)
-- open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
-- open import Data.List using (List; []; _∷_; _++_; [_])
-- import Relation.Binary.PropositionalEquality as Eq
-- open Eq using (_≡_; refl; trans; cong; subst; sym; _≢_; cong₂)
-- open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)



-- data term : ℕ → Set where
--   `_  : ∀ {n} → Fin n → term n
--   ƛ   : ∀ {n} → term (suc n) → term n
--   _·_ : ∀ {n} → term n → term n → term n



-- shift : ∀ {lvl : ℕ} (n : ℕ) → ℕ → term lvl → term (lvl + n) 
-- shift {lvl} zero k (` x) = ` cast (+-comm zero lvl) x
-- shift {lvl} (suc n) k (` x) with (toℕ x) ≤? k 
-- ... | yes x≤k = ` cast (+-comm (suc n) lvl) (raise (suc n) x)
-- ... | no x>k = ` cast 
--                   prf
--                   (suc (inject+ n x))
--               where 
--                 prf : suc (lvl + n) ≡ lvl + suc n
--                 prf rewrite +-comm lvl (suc n) | +-comm n lvl = refl
-- shift {lvl} n k (ƛ t) = ƛ (shift n (suc k) t)
-- shift {lvl} n k (t₁ · t₂) = (shift n k t₁) · (shift n k t₂)


-- substλ : ∀ {lvl : ℕ} → term lvl → ∀ (n : ℕ) → term lvl → term (lvl + n) 
-- substλ {lvl} (` x) n s with (toℕ x) Data.Nat.≟ n 
-- ... | res = {!   !}
-- substλ {lvl} (ƛ t) n s = {!   !}
-- substλ {lvl} (t · t₁) n s = {!   !}



```


-- ```agda
-- module test where
-- open import Relation.Nullary
-- open import Data.Bool using (Bool; true; false; _∧_)
-- open import Data.Nat using (ℕ; zero; suc; _+_; _<?_)
-- open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ; suc-injective)
-- open import Data.Fin using (Fin; zero; suc; _≟_)
-- open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
-- open import Data.List using (List; []; _∷_; _++_; [_])
-- import Relation.Binary.PropositionalEquality as Eq
-- open Eq using (_≡_; refl; trans; cong; subst; sym; _≢_; cong₂)
-- open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

-- data term : ℕ → Set where
--   `_  : ∀ {n} → Fin n → term n
--   ƛ   : ∀ {n} → term (suc n) → term n
--   _·_ : ∀ {n} → term n → term n → term n

-- infixl 20 _·_
-- infix 40 `_

-- mutual
--   data env : ℕ → Set where
--     nil  : env zero
--     _,-_ : ∀ {n} → env n → clo → env (suc n)

--   clo = Σ[ n ∈ ℕ ] env n × term n

-- data stk : Set where
--   emp  : stk
--   _-,_ : clo → stk → stk

-- infixr 10 _-,_

-- record configuration : Set where
--   constructor ⟨_⋆_⟩
--   field
--     closure : clo
--     stack   : stk

-- infix  20 ⟨_⋆_⟩


-- data _⇒_ : configuration → configuration → Set where
--   grab : ∀ {n : ℕ} {η : env n} {c} {π : stk}              → ⟨ suc n , η ,- c , ` zero    ⋆ π ⟩      ⇒ ⟨ c                      ⋆ π ⟩
--   skip : ∀ {n : ℕ} {η : env n} {c} {i : Fin n} {π : stk}  → ⟨ suc n , η ,- c , ` (suc i) ⋆ π ⟩      ⇒ ⟨ n ,     η        , ` i ⋆ π ⟩
--   push : ∀ {n : ℕ} {η : env n} {t} {s} {π : stk}          → ⟨     n , η      , t · s     ⋆ π ⟩      ⇒ ⟨ n ,     η        , t   ⋆ (n , η , s) -, π ⟩
--   pop  : ∀ {n : ℕ} {η : env n} {t} {c} {π : stk}          → ⟨     n , η      , ƛ t       ⋆ c -, π ⟩ ⇒ ⟨ suc n , (η ,- c) , t   ⋆ π ⟩

-- infixr 10 _⇒_

-- init : term 0 → configuration
-- init t = ⟨ 0 , nil , t ⋆ emp ⟩

-- data reduces : ℕ → configuration → Set where
--   stop : ∀ {n} η t → reduces 0 ⟨ n , η , ƛ t ⋆ emp ⟩
--   step : ∀ {n p q} → p ⇒ q → reduces n q → reduces (suc n) p

-- deterministic : ∀ {p q q'} → p ⇒ q → p ⇒ q' → q ≡ q'
-- deterministic grab grab = refl
-- deterministic skip skip = refl
-- deterministic push push = refl
-- deterministic pop pop = refl 


-- reduces-det : ∀ {p m n} → reduces m p → reduces n p → m ≡ n
-- reduces-det (stop η t) (stop .η .t) = refl
-- reduces-det (step p⇒q rmp) (step p⇒q₁ rnp) with deterministic p⇒q p⇒q₁ 
-- ... | refl = cong suc (reduces-det rmp rnp)


-- data type : Set where
--   ⋆    : type
--   _↦_ : List type → type → type

-- infixr 30 _↦_

-- data ctx : ℕ → Set where
--   nil : ctx zero
--   _,-_ : ∀ {n} → ctx n → List type → ctx (suc n)

-- empty : ∀{n} → ctx n
-- empty {zero}  = nil
-- empty {suc n} = empty {n} ,- []

-- _+++_ : ∀{n} → ctx n → ctx n → ctx n
-- nil        +++ nil       = nil
-- (Γ₁ ,- σ₁) +++ (Γ₂ ,- σ₂) = (Γ₁ +++ Γ₂) ,- (σ₁ ++ σ₂)


-- _≡ₜ_ : type -> type -> Bool
-- _≡ₘ_ : List type -> List type -> Bool
-- _⊆_ : List type -> List type -> Bool
-- _#_ : List type -> type -> ℕ
-- ⋆ ≡ₜ ⋆ = true
-- ⋆ ≡ₜ (x ↦ t2) = false
-- (x ↦ t1) ≡ₜ ⋆ = false
-- (l₁ ↦ t₁) ≡ₜ (l₂ ↦ t₂) = l₁ ≡ₘ l₂ ∧ t₁ ≡ₜ t₂

-- l₁ ≡ₘ l₂ = l₁ ⊆ l₂ ∧ l₂ ⊆ l₁

-- [] ⊆ l2 = true
-- (x ∷ l₁) ⊆ l₂ with (l₁ # x) <? (l₂ # x)
-- ... | yes _ = true
-- ... | no _ = false

-- [] # x = 0
-- (x₁ ∷ l) # x with x₁ ≡ₜ x 
-- ... | false = l # x
-- ... | true = suc (l # x)


-- _≡ctx_ : ∀ {n} → ctx n → ctx n → Bool 
-- nil ≡ctx nil = true
-- (ctx₁ ,- t₁) ≡ctx (ctx₂ ,- t₂) = t₁ ≡ₘ t₂ ∧ ctx₁ ≡ctx ctx₂





-- ```
   
     