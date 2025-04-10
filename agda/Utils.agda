{-# OPTIONS --prop #-}
module Utils where

open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; subst; sym)
        
substProp : ∀ {A : Set} {a a' : A} (P : A → Prop) → P a → a ≡ a' → P a'
substProp P p refl = p