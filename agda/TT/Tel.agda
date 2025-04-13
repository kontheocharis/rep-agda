
module TT.Tel where

open import Data.Product.Base using (_,_) renaming (Σ to Pair)
open import TT.Core

open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; subst; sym; cong; trans; cong₂; cong-app)

module Tel-construction (T : TT) where
  open TT T

  data Tel : Set
  data Spine : Tel → Set

  variable
    Δ Δ' : Tel
    X X' Y Y' : Spine _ → Ty
    δ δ' α β : Spine _

  data Tel where
    ∙ : Tel
    ext : (A : Ty) → (Tm A → Tel) → Tel

  data Spine where
    [] : Spine ∙
    _,_ : ∀ {A Δ} → (a : Tm A) → Spine (Δ a) → Spine (ext A Δ)
    
  infixr 4 _,_
    
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
  
  take : ∀ {A} → Spine (a ∶ A , ∙) → Tm A
  take (a , []) = a
  
  curry : ∀ {x : Set} {Δ} {A : Spine Δ → Ty} → (f : (δ : Spine Δ) → Tm (A δ) → x) → Spine (Δ ▷ A) → x
  curry f sp = let (δ , t) = split sp in f δ (take t)
  
  uncurry : ∀ {x : Set} {Δ} {A : Spine Δ → Ty} → (f : Spine (Δ ▷ A) → x) → (δ : Spine Δ) → Tm (A δ) → x
  uncurry f δ t = f (δ ⨾ t)