{-# OPTIONS --large-indices --no-positivity-check #-}
open import Data.String using (String)
open import Data.List using (List; _∷_; []; length; _++_; lookup; map; foldl)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Unit using (⊤)
open import Data.Vec using (Vec; _∷_; [])
open import Agda.Builtin.Nat using (Nat; suc; zero; _==_)

Label : Set
Label = String

data LTyCtx : Set where

data LTy : LTyCtx -> Set where

data LTm : ∀ {Ξ} -> LTy Ξ -> Set where

-- data STyOrSVar : Set where
--   ty : STy -> STyOrSVar
--   var : STyOrSVar

data STyCtx : Set where
  ∅ : STyCtx
  _,type : STyCtx -> STyCtx

data STyVar : STyCtx -> Set where
  z : ∀ {Γ} -> STyVar (Γ ,type)
  s : ∀ {Γ} -> STyVar Γ -> STyVar (Γ ,type)

Product : List Set -> Set
Product [] = ⊤
Product (A ∷ As) = A × Product As

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

  variant-tys : ∀ {F} -> VariantIdx F -> List (STy (∅ ,type))
  variant-tys {F} i = SField.ty (lookup (SFunc.variants F) i)

  data STy where
    _=>_ : ∀ {Ξ} -> STy Ξ -> STy Ξ -> STy Ξ
    μ : ∀ {Ξ} -> SFunc -> STy Ξ
    _⦅_⦆ : ∀ {Ξ} -> SFunc -> STy Ξ -> STy Ξ
    Q : ∀ {Ψ Ξ} -> LTy Ψ -> STy Ξ -- ψ should be derived from Ξ
    V : ∀ {Ξ} -> STyVar Ξ -> STy Ξ

weaken-ty : ∀ {Ξ} -> STy Ξ -> STy (Ξ ,type)
weaken-ty (A => B) = (weaken-ty A) => (weaken-ty B)
weaken-ty (μ F) = μ F
weaken-ty (F ⦅ A ⦆) = F ⦅ (weaken-ty A) ⦆
weaken-ty (Q L) = Q L
weaken-ty (V Z) = V (s Z)

_[_] : ∀ {Ξ} -> STy (Ξ ,type) -> STy Ξ -> STy Ξ
(A => B) [ M ] = (A [ M ]) => (B [ M ])
(μ F) [ M ] = μ F
(F ⦅ A ⦆) [ M ] = F ⦅ A [ M ] ⦆
(Q L) [ M ] = Q L
(V z) [ M ] = M
(V (s v)) [ M ] = V v

data SCtx : Set where
  ∅ : SCtx
  _,_ : SCtx -> STy ∅ -> SCtx

data SVar : SCtx -> Set where
  z : ∀ {Γ A} -> SVar (Γ , A)
  s : ∀ {Γ A} -> SVar Γ -> SVar (Γ , A)

interleaved mutual

  data STm : SCtx -> STy ∅ -> Set

  data STms : SCtx -> List (STy ∅) -> Set

  data STms where
    [] : ∀ {Γ} -> STms Γ []
    _,_ : ∀ {Γ A As} -> STm Γ A -> STms Γ As -> STms Γ (A ∷ As)

  extend-ctx : SCtx -> List (STy ∅) -> SCtx
  extend-ctx Γ [] = Γ
  extend-ctx Γ (A ∷ As) = extend-ctx (Γ , A) As

  data DepVec : List Set -> Set where
    [] : DepVec []
    _,_ : ∀ {A As} -> A -> DepVec As -> DepVec (A ∷ As)

  VariantTerms : ∀ {F} -> SCtx -> VariantIdx F -> STy ∅ -> Set
  VariantTerms {F} Γ i A = STms Γ (map (λ T -> T [ A ]) (variant-tys {F} i))

  VariantElims : SFunc -> SCtx -> STy ∅ -> STy ∅ -> Set
  VariantElims F Γ A B = DepVec (map (λ f -> STm (extend-ctx Γ (map (λ l -> l [ A ]) (SField.ty f)))  B) (SFunc.variants F))

  data STm where
    lam : ∀ {Γ A B} -> STm (Γ , A) B -> STm Γ (A => B)
    app : ∀ {Γ A B} -> STm Γ (A => B) -> STm Γ A -> STm Γ B
    _/_ : ∀ {Γ A} -> (F : SFunc) -> (i : VariantIdx F) -> (δ : VariantTerms {F} Γ i A) -> STm Γ (F ⦅ A ⦆)
    v : ∀ {Γ A} -> SVar Γ -> STm Γ A
    letin : ∀ {Γ A B} -> STm Γ A -> STm (Γ , A) B -> STm Γ B
    q : ∀ {Ψ Γ} {C : LTy Ψ} -> LTm C -> STm Γ (Q C)
    caseof : ∀ {Γ A B F} -> STm Γ (F ⦅ A ⦆) -> (δ : VariantElims F Γ A B) -> STm Γ B
    unwrap : ∀ {Γ F} -> STm Γ (μ F) -> STm Γ (F ⦅ μ F ⦆)
    wrap : ∀ {Γ F} -> STm Γ (F ⦅ μ F ⦆) -> STm Γ (μ F)
    fold : ∀ {Γ F A} -> STm Γ ((F ⦅ A ⦆) => A) -> STm Γ ((μ F) => A)
    unfold : ∀ {Γ F A} -> STm Γ (A => (F ⦅ A ⦆)) -> STm Γ (A => (μ F))


  NatF : SFunc
  NatF = func "Nat" ( fld "zero" [] ∷ fld "suc" ( V z ∷ [] ) ∷ [])

  Prod : STy ∅ -> STy ∅ -> STy ∅
  Prod A B = μ (func "Prod" ( fld "pair" ( weaken-ty A ∷ weaken-ty B ∷ [] ) ∷ []))

  NatT : STy ∅
  NatT = μ NatF

  -- add : STm ∅ (NatT => (NatT => NatT))
  -- add = lam (fold (lam (caseof {F = NatF} (v (s z)) ( (v z) , ( (NatF / zero) ()  , [] ) ))))

    -- where
    --   elim : ∀ {Γ} -> (i : VariantIdx NatF) -> STm (variant-ctx {NatF} (Γ , Nat) i Nat) Nat
    --   elim zero = {!   !}
    --   elim (suc zero) = {!   !}




