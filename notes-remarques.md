
```agda
  
data tightConstant : Set where
  TCNeutral : tightConstant
  TCAbs : tightConstant
  
data type : Set
data multitype : Set

data type where 
    TyTight : tightConstant -> type
    TyFun : multitype -> type -> type

data multitype where 
    mtEmpty : multitype
    mtCons : type -> multitype -> multitype
    

_≡ₜ_ : type -> type -> Bool 
_#_ : multitype -> type -> ℕ
_⊆_ : multitype -> multitype -> Bool
_≡ₘ_ : multitype -> multitype -> Bool 
(TyTight TCNeutral) ≡ₜ (TyTight TCNeutral) = true
(TyTight TCNeutral) ≡ₜ (TyTight TCAbs)     = false
(TyTight TCAbs)     ≡ₜ (TyTight TCNeutral) = false
(TyTight TCAbs)     ≡ₜ (TyTight TCAbs)     = true
(TyTight x)         ≡ₜ (TyFun x₁ t₂)       = false
(TyFun x t₁)        ≡ₜ (TyTight x₁)        = false
(TyFun mt₁ t₁)      ≡ₜ (TyFun mt₂ t₂)      = (mt₁ ≡ₘ mt₂) && (t₁ ≡ₜ t₂)

mtEmpty       # t = O
(mtCons t' m) # t with t ≡ₜ t' 
... | true = S (m # t)
... | false = m # t

mtEmpty         ⊆ mt₂ = true
(mtCons x mt₁)  ⊆ mt₂ = (mt₁ ⊆ mt₂) && ((S (mt₁ # x)) ≤? (mt₂ # x))  

mt₁ ≡ₘ mt₂ = (mt₁ ⊆ mt₂) && (mt₂ ⊆ mt₁)
```
Accepté en Agda, équivalent en coq refusé