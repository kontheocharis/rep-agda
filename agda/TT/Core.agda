{-# OPTIONS --rewriting #-}

module TT.Core where

import TT.Utils

open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; subst)

-- Type theory
record TT : Set1 where
  field
    Ty : Set
    Tm : Ty → Set
    
  coe-Tm : ∀ {A A'} → A ≡ A' → Tm A → Tm A'
  coe-Tm refl t = t
  
  coh-Tm : ∀ {A} → (p : A ≡ A) → (t : Tm A) → coe-Tm p t ≡ t
  coh-Tm refl t = refl
  
  {-# REWRITE coh-Tm #-}
  
-- Morphism of type theories
record _~>_ (a : TT) (b : TT) : Set1 where
  open TT
  field
    Ty~> : a .Ty → b .Ty
    Tm~> : ∀ {A} → a .Tm A → b .Tm (Ty~> A)
    
  