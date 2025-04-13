
module TT.Data where

open import TT.Utils
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
  open Sig-construction T-MLTT
  open IndAlg public

  field
    Data : ∀ {Δ} → (S : Sig Δ) → IndAlg S → Spine Δ → Ty
    ctor : ∀ {Δ} {O : Op Δ} {S} {γ : IndAlg S} → O ∈ S → (v : Spine (input O (Data S γ))) → Tm (Data S γ (output v))

    -- Define this as an element of the language rather than
    -- a function to make Agda happy
    ctors : ∀ {Δ} → (S : Sig Δ) → (γ : IndAlg S) → Spine (alg S (Data S γ))
    -- η rule uniquely determines its value, so it's the same
    ctors-η : ∀ {Δ} → (S : Sig Δ) → (γ : IndAlg S) → ctors S γ ≡ sig-spine S (λ p → lams (ctor p))
  
  field
    elim : ∀ {Δ} {S : Sig Δ} {γ} → (M : Spine (Δ ▷ Data S γ) → Ty)
      → (β : Spine (disp-alg (ctors S γ) M))
      → (δx : Spine (Δ ▷ Data S γ)) → Tm (M δx)

    Data-β : ∀ {Δ} {S : Sig Δ} {O γ} → (M : Spine (Δ ▷ Data S γ) → Ty)
      → (β : Spine (disp-alg (ctors S γ) M))
      → (o : O ∈ S) → (v : Spine (input O (Data S γ))) 
      → elim M β (output v ⨾ apps (at o (ctors S γ)) v) ≡ (coe-Tm (sec-coh-Ty (elim M β) O _ _) (apps (at o β) (elim M β $ v)))
      
  