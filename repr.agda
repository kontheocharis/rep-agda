open import Data.String using (String)
open import Data.List using (List; _∷_; []; length; _++_; lookup; map)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Unit using (⊤)

Label : Set
Label = String


data LTy : Set where

-- data STyOrSVar : Set where
--   ty : STy -> STyOrSVar
--   var : STyOrSVar

data STyCtx : Set where
  ∅ : STyCtx
  _,type : STyCtx -> STyCtx

data STyVar : STyCtx -> Set where
  z : ∀ {Γ} -> STyVar (Γ ,type)
  s : ∀ {Γ} -> STyVar Γ -> STyVar (Γ ,type)

eq : ∀ {Ξ} -> STyVar Ξ -> STyVar Ξ -> Bool
eq z z = true
eq (s x) (s y) = eq x y
eq _ _ = false

interleaved mutual

  data STy : STyCtx -> Set


  record SField : Set where
    inductive
    constructor fld
    field
      label : Label
      ty : List (STy (∅ ,type))

  record SFunc : Set where
    inductive
    constructor func
    field
      label : Label
      variants : List (SField)

  VariantIdx : SFunc -> Set
  VariantIdx F = Fin (length (SFunc.variants F))

  FieldIdx : ∀ {F} -> VariantIdx F -> Set
  FieldIdx {F} i = Fin (length (SField.ty (lookup (SFunc.variants F) i)))

  variantTys : ∀ {F} -> VariantIdx F -> List (STy (∅ ,type))
  variantTys {F} i = SField.ty (lookup (SFunc.variants F) i)

  data STy where
    _=>_ : ∀ {Ξ} -> STy Ξ -> STy Ξ -> STy Ξ
    μ : ∀ {Ξ} -> SFunc -> STy Ξ
    _⦅_⦆ : ∀ {Ξ} -> SFunc -> STy Ξ -> STy Ξ
    Q : ∀ {Ξ} -> LTy -> STy Ξ
    V : ∀ {Ξ} -> STyVar Ξ -> STy Ξ

weakenTy : ∀ {Ξ} -> STy Ξ -> STy (Ξ ,type)
weakenTy (A => B) = (weakenTy A) => (weakenTy B)
weakenTy (μ F) = μ F
weakenTy (F ⦅ A ⦆) = F ⦅ (weakenTy A) ⦆
weakenTy (Q L) = Q L
weakenTy (V Z) = V (s Z)

_[_] : ∀ {Ξ} -> STy (Ξ ,type) -> STy Ξ -> STy Ξ
(A => B) [ M ] = (A [ M ]) => (B [ M ])
(μ F) [ M ] = μ F
(F ⦅ A ⦆) [ M ] = F ⦅ A [ M ] ⦆
(Q L) [ M ] = Q L
(V z) [ M ] = M
(V (s v)) [ M ] = V v

Product : List Set -> Set
Product [] = ⊤
Product (A ∷ As) = A × Product As

data SCtx : Set where
  ∅ : SCtx
  _,_ : SCtx -> STy ∅ -> SCtx

data SVar : SCtx -> Set where
  z : ∀ {Γ A} -> SVar (Γ , A)
  s : ∀ {Γ A} -> SVar Γ -> SVar (Γ , A)

data STm : SCtx -> STy ∅ -> Set where
  lam : ∀ {Γ A B} -> STm (Γ , A) B -> STm Γ (A => B)
  app : ∀ {Γ A B} -> STm Γ (A => B) -> STm Γ B -> STm Γ A
  _/_ : ∀ {Γ A} -> (F : SFunc) -> (i : VariantIdx F) -> (t : Product (map (λ t -> STm Γ (t [ A ])) (variantTys i))) -> STm Γ (F ⦅ A ⦆)
