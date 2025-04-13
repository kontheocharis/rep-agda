module TT.Utils where

open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; subst; sym)
open import Axiom.Extensionality.Propositional
        
postulate
  -- Useful sometimes when working with HOAS
  funext : ∀ {a b} → Extensionality a b
  
-- Fibered equality
_≡_by_ : ∀ {i} {A B : Set i} → (a : A) → (b : B) → A ≡ B → Set i
_≡_by_ a b refl = a ≡ b

coe : ∀ {i} {A B : Set i} → A ≡ B → (a : A) → B
coe refl a = a