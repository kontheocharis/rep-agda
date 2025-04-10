{-# OPTIONS --prop #-}
module TT.Data where

open import Utils
open import TT.Core
open import TT.Base
open import TT.Tel 
open import TT.Sig

open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; subst; sym)
open import Data.Product.Base using (_,_) renaming (Σ to Pair)

record Data-structure (T : TT)
  {{T-U : U-structure T}}
  {{T-Π : Π-structure T}} 
  {{T-Σ : Σ-structure T}}
  {{T-Id : Id-structure T}}
  {{T-⊤ : ⊤-structure T}} : Set1
  where
  open TT T
  open Tel-construction T
  open Π-structure T-Π
  open Sig-construction T

  field
    Data : ∀ {Δ} → (S : Sig Δ) → Spine (ind-alg S) → Spine Δ → Ty
    ctor : ∀ {Δ} {O : Op Δ} {S γ} → O ∈ S → (v : Spine (input O (Data S γ))) → Tm (Data S γ (output v))

  ctors : ∀ {Δ} → (S : Sig Δ) → (γ : Spine (ind-alg S)) → Spine (alg S (Data S γ))
  ctors S γ = sig-spine S (λ p → lams (ctor p))
  
  field
    elim : ∀ {Δ} {S : Sig Δ} {γ} → (M : Spine (Δ ▷ Data S γ) → Ty)
      → (β : Spine (disp-alg (ctors S γ) M))
      → (δx : Spine (Δ ▷ Data S γ)) → Tm (M δx)

    Data-β : ∀ {Δ} {S : Sig Δ} {O γ} → (M : Spine (Δ ▷ Data S γ) → Ty)
      → (β : Spine (disp-alg (ctors S γ) M))
      → (o : O ∈ S) → (v : Spine (input O (Data S γ))) 
      → Tm~ (sym-Ty (lift-Ty (sec-coh-Ty (elim M β) O _ _)))
        (elim M β (output v ⨾ apps (at o (ctors S γ)) v)) (apps (at o β) (elim M β $ v))
  
  ctors-at-ctor : ∀ {Δ} {O : Op Δ} {S γ} → (o : O ∈ S) → (v : Spine (input O (Data S γ)))
    → Tm~ refl-Ty (apps (at o (ctors S γ)) v) (ctor o v)
  ctors-at-ctor {Δ} {O} {S} {γ} o v =
    substProp
      {a = lams (ctor o)}
      {a' = at o (ctors S γ)}
      (λ t → Tm~ refl-Ty (apps t v) (ctor o v))
      (Πs-β {f = ctor o})
      (sym (sig-spine-at o))
  