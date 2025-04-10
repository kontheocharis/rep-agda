{-# OPTIONS --prop #-}
module TT.Tel where

open import Data.Product.Base using (_,_) renaming (Σ to Pair)
open import TT.Core

module Tel-construction (T : TT) where
  open TT T

  data Tel : Set
  data Spine : Tel → Set
  
  data Tel~ : Tel → Tel → Prop
  data Spine~ : ∀ {Δ Δ'} → Tel~ Δ Δ' → Spine Δ → Spine Δ' → Prop

  variable
    Δ Δ' : Tel
    X X' Y Y' : Spine _ → Ty
    δ δ' α β : Spine _

  data Tel where
    ∙ : Tel
    ext : (A : Ty) → (Tm A → Tel) → Tel
  

  data Tel~ where
    
    ∙~ : Tel~ ∙ ∙
    ext~ : ∀ {A A'} → (A~ : Ty~ A A')
      → {Δ : Tm A → Tel} → {Δ' : Tm A' → Tel}
      → (Δ~ : ∀ {a a'} → Tm~ A~ a a' → Tel~ (Δ a) (Δ' a'))
      → Tel~ (ext A Δ) (ext A' Δ')

  postulate 
    refl-Tel : Tel~ Δ Δ
    sym-Tel : ∀ {Δ Δ'} → Tel~ Δ Δ' → Tel~ Δ' Δ
    trans-Tel : ∀ {Δ Δ' Δ''} → Tel~ Δ Δ' → Tel~ Δ' Δ'' → Tel~ Δ Δ''

  data Spine where
    [] : Spine ∙
    _,_ : ∀ {A Δ} → (a : Tm A) → Spine (Δ a) → Spine (ext A Δ)

  data Spine~ where

    []~ : Spine~ ∙~ [] []
    _,~_ : ∀ {A} {A'} {A~ : Ty~ A A'} {a : Tm A} {a' : Tm A'}
      → {Δ : Tm A → Tel} {Δ' : Tm A' → Tel}
      → {Δ~ : ∀ {a : Tm A} {a' : Tm A'} → Tm~ A~ a a' → Tel~ (Δ a) (Δ' a')}
      → (a~ : Tm~ A~ a a')
      → {v : Spine (Δ a)}
      → {v' : Spine (Δ' a')}
      → Spine~ (Δ~ a~) v v'
      → Spine~ (ext~ A~ Δ~) (a , v) (a' , v')
    
  infixr 4 _,_

  postulate 
    refl-Spine : ∀ {Δ δ} → Spine~ {Δ = Δ} refl-Tel δ δ
    
  syntax ext A (λ a → Δ) = a ∶ A , Δ

  extN : (Δ : Tel) → (Spine Δ → Tel) → Tel
  extN ∙ Δ' = Δ' []
  extN (ext A Δ) Δ' = ext A (λ a → extN (Δ a) (λ δ → Δ' (a , δ)))

  syntax extN Δ (λ δ → Δ') = δ ∷ Δ , Δ'

  _,,_ : ∀ {Δ'} → (δ : Spine Δ) → Spine (Δ' δ) → Spine (extN Δ Δ')
  _,,_ {Δ = ∙} [] v = v
  _,,_ {Δ = ext A Δ} (a , δ) v = (a , δ ,, v)

  _▷_ : (Δ : Tel) → (Spine Δ → Ty) → Tel
  Δ ▷ X = δ ∷ Δ , _ ∶ X δ , ∙

  _⨾_ : (δ : Spine Δ) → Tm (X δ) → Spine (Δ ▷ X)
  δ ⨾ t = δ ,, (t , [])

  split : ∀ {Δ Δ'} → Spine (extN Δ Δ') → Pair (Spine Δ) (λ δ → Spine (Δ' δ))
  split {Δ = ∙} v = [] , v
  split {Δ = ext A Δ} (a , v) = let (v' , v'') = split v in ((a , v') , v'') 

  init : ∀ {Δ Δ'} → Spine (extN Δ Δ') → Spine Δ
  init sp = let (a , b) = split sp in a

  tail : ∀ {Δ Δ'} → (v : Spine (extN Δ Δ')) → Spine (Δ' (init v))
  tail {Δ' = Δ'} sp = let (a , b) = split {Δ' = Δ'} sp in b