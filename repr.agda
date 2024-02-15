{-# OPTIONS --large-indices --no-positivity-check #-}
open import Data.String using (String)
open import Data.List using (List; _∷_; []; length; _++_; lookup; map; foldl; replicate)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; Σ; _,_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec; _∷_; [])
open import Agda.Builtin.Nat using (Nat; suc; zero; _==_)
open import Agda.Primitive

data LTy : Set where

data LTm : LTy -> Set where

Product : List Set -> Set
Product [] = ⊤
Product (A ∷ As) = A × Product As

record Poly (S : Set) : Set where
  constructor poly
  field
    sh : Nat
    pos : Fin sh -> Nat
    coe : Fin sh -> S

data STy : Set where
  _=>_ : STy -> STy -> STy
  μ : Poly STy -> STy
  _⦅_⦆ : Poly STy -> STy -> STy
  Q : LTy -> STy

data SCtx : Set where
  ∅ : SCtx
  _,_ : SCtx -> STy -> SCtx

data SVar : SCtx -> Set where
  z : ∀ {Γ A} -> SVar (Γ , A)
  s : ∀ {Γ A} -> SVar Γ -> SVar (Γ , A)

fin-zero : ∀ {l : Level} {A : Set l} -> Fin zero -> A
fin-zero ()

DepVec : (n : Nat) -> (Fin n -> Set) -> Set
DepVec zero _ = ⊤
DepVec (suc n) P = Σ (P zero) (λ x -> DepVec n (λ i -> P (suc i)))

extend-ctx : SCtx -> List STy -> SCtx
extend-ctx Γ [] = Γ
extend-ctx Γ (A ∷ As) = extend-ctx (Γ , A) As

data STm : SCtx -> STy -> Set where
  lam : ∀ {Γ A B} -> STm (Γ , A) B -> STm Γ (A => B)
  app : ∀ {Γ A B} -> STm Γ (A => B) -> STm Γ A -> STm Γ B
  _/_ : ∀ {Γ A} -> (P : Poly STy) -> (i : Fin (Poly.sh P)) -> STm Γ (Poly.coe P i) -> Vec (STm Γ (P ⦅ A ⦆)) (Poly.pos P i) -> STm Γ (P ⦅ A ⦆)
  v : ∀ {Γ A} -> SVar Γ -> STm Γ A
  letin : ∀ {Γ A B} -> STm Γ A -> STm (Γ , A) B -> STm Γ B
  q : ∀ {Γ} {C : LTy} -> LTm C -> STm Γ (Q C)
  caseof : ∀ {Γ A B P} -> STm Γ (P ⦅ A ⦆) -> DepVec (Poly.sh P) (λ i -> STm (extend-ctx (Γ , Poly.coe P i) (replicate (Poly.pos P i) (P ⦅ A ⦆))) B) -> STm Γ B
  unwrap : ∀ {Γ F} -> STm Γ (μ F) -> STm Γ (F ⦅ μ F ⦆)
  wrap : ∀ {Γ F} -> STm Γ (F ⦅ μ F ⦆) -> STm Γ (μ F)
  -- fold : ∀ {Γ F A} -> STm Γ ((F ⦅ A ⦆) => A) -> STm Γ ((μ F) => A)
  -- unfold : ∀ {Γ F A} -> STm Γ (A => (F ⦅ A ⦆)) -> STm Γ (A => (μ F))

  -- data STms : SCtx -> List STy -> Set

  -- data STms where
  --   [] : ∀ {Γ} -> STms Γ []
  --   _,_ : ∀ {Γ A As} -> STm Γ A -> STms Γ As -> STms Γ (A ∷ As)

  -- extend-ctx : SCtx -> List STy -> SCtx
  -- extend-ctx Γ [] = Γ
  -- extend-ctx Γ (A ∷ As) = extend-ctx (Γ , A) As

  -- data DepVec : List Set -> Set where
  --   [] : DepVec []
  --   _,_ : ∀ {A As} -> A -> DepVec As -> DepVec (A ∷ As)

  -- VariantTerms : ∀ {F} -> SCtx -> VariantIdx F -> STy ∅ -> Set
  -- VariantTerms {F} Γ i A = STms Γ (map (λ T -> T [ A ]) (variant-tys {F} i))

  -- VariantElims : SFunc -> SCtx -> STy ∅ -> STy ∅ -> Set
  -- VariantElims F Γ A B = DepVec (map (λ f -> STm (extend-ctx Γ (map (λ l -> l [ A ]) (SField.ty f)))  B) (SFunc.variants F))


  -- NatF : SFunc
  -- NatF = func "Nat" ( fld "zero" [] ∷ fld "suc" ( V z ∷ [] ) ∷ [])

  -- Prod : STy ∅ -> STy ∅ -> STy ∅
  -- Prod A B = μ (func "Prod" ( fld "pair" ( weaken-ty A ∷ weaken-ty B ∷ [] ) ∷ []))

  -- NatT : STy ∅
  -- NatT = μ NatF

  -- add : STm ∅ (NatT => (NatT => NatT))
  -- add = lam (fold (lam (caseof {F = NatF} (v (s z)) ({!   !}))))

    -- where
    --   elim : ∀ {Γ} -> (i : VariantIdx NatF) -> STm (variant-ctx {NatF} (Γ , Nat) i Nat) Nat
    --   elim zero = {!   !}
    --   elim (suc zero) = {!   !}




