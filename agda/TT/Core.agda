{-# OPTIONS --prop #-}
module TT.Core where

open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; subst)

-- Type theory
record TT : Set1 where
  field
    Ty : Set
    Tm : Ty → Set
    
  coe-Tm : ∀ {A A'} → A ≡ A' → Tm A → Tm A'
  coe-Tm refl t = t
  
-- Morphism of type theories
record _~>_ (a : TT) (b : TT) : Set1 where
  open TT
  field
    Ty~> : a .Ty → b .Ty
    Tm~> : ∀ {A} → a .Tm A → b .Tm (Ty~> A)
    
  