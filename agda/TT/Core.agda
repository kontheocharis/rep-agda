{-# OPTIONS --prop #-}
module TT.Core where

open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; subst)

record TT : Set1 where
  field
    Ty : Set
    Tm : Ty → Set
    
  coe-Tm : ∀ {A A'} → A ≡ A' → Tm A → Tm A'
  coe-Tm refl t = t