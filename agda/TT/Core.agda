{-# OPTIONS --prop #-}
module TT.Core where

open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; subst)

record TT : Set1 where
  field
    Ty : Set
    Tm : Ty → Set
    Ty~ : Ty → Ty → Prop
    Tm~ : ∀ {A A'} → Ty~ A A' → Tm A → Tm A' → Prop
    
    refl-Ty : ∀ {A} → Ty~ A A
    sym-Ty : ∀ {A B} → Ty~ A B → Ty~ B A
    trans-Ty : ∀ {A B C} → Ty~ A B → Ty~ B C → Ty~ A C

    refl-Tm : ∀ {A} {t : Tm A} → Tm~ refl-Ty t t
    sym-Tm : ∀ {A A~} {t u : Tm A} → Tm~ A~ t u → Tm~ (sym-Ty A~) u t
    trans-Tm : ∀ {A B C} {AB : Ty~ A B} {BC : Ty~ B C} {t u v} → Tm~ AB t u → Tm~ BC u v → Tm~ (trans-Ty AB BC) t v

    coe : ∀ {A A'} → Ty~ A A' → Tm A → Tm A'
    coe-unique : ∀ {A A'} {A~ : Ty~ A A'} {t : Tm A} → Tm~ A~ t (coe A~ t)
    
    

  lift-Ty : ∀ {A A'} → A ≡ A' → Ty~ A A'
  lift-Ty refl = refl-Ty

  transp-Ty : ∀ {A A'} → A ≡ A' → Tm A → Tm A'
  transp-Ty refl t = t