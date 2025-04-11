{-# OPTIONS --prop #-}
module TT.Data where

open import Utils
open import TT.Core
open import TT.Base
open import TT.Tel 
open import TT.Sig

open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; subst; sym; cong)
open import Data.Product.Base using (_,_) renaming (Σ to Pair)

record Data-structure (T : TT)
  (T-MLTT : MLTT-structure T) : Set1
  where
  open TT T
  open MLTT-structure T-MLTT
  open Tel-construction T
  open Π-structure T-Π
  open Sig-construction T T-MLTT

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
      → elim M β (output v ⨾ apps (at o (ctors S γ)) v) ≡ apps (at o β) (elim M β $ v)
        by (cong Tm (sym (sec-coh-Ty (elim M β) O _ _)))

  ctors-at-ctor : ∀ {Δ} {O : Op Δ} {S γ} → (o : O ∈ S) → (v : Spine (input O (Data S γ)))
    → apps (at o (ctors S γ)) v ≡ ctor o v
  ctors-at-ctor {Δ} {O} {S} {γ} o v = subst
      (λ t → apps t v ≡ ctor o v)
      (sym (sig-spine-at o))
      (Πs-β {f = ctor o})
  