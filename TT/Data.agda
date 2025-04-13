{-# OPTIONS --rewriting #-}
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
    -- Data type for a signature. Also need an inductive algebra
    Data : ∀ {Δ} → (S : Sig Δ) → IndAlg S → Spine Δ → Ty

    -- A constructor for a data type is associated with an algebra operation O ∈ S
    -- and the inputs at O.
    ctor : ∀ {Δ} {O : Op Δ} {S} {γ : IndAlg S} → O ∈ S → (v : Spine (input O (Data S γ))) → Tm (Data S γ (output v))

    -- <Helpers>
    -- Define this as an element of the language rather than
    -- a function to make Agda happy
    ctors : ∀ {Δ} → (S : Sig Δ) → (γ : IndAlg S) → Spine (alg S (Data S γ))
    -- This rule uniquely determines its value, so it's the same
    ctors-def : ∀ {Δ} → (S : Sig Δ) → (γ : IndAlg S) → ctors S γ ≡ sig-spine S (λ p → lams (ctor p))
    -- </Helpers>
  
  field
    elim : ∀ {Δ} {S : Sig Δ} {γ} → (M : Spine (Δ ▷ Data S γ) → Ty)
      → (β : Spine (disp-alg (ctors S γ) M))
      → (δx : Spine (Δ ▷ Data S γ)) → Tm (M δx)

    Data-β : ∀ {Δ} {S : Sig Δ} {O γ} → (M : Spine (Δ ▷ Data S γ) → Ty)
      → (β : Spine (disp-alg (ctors S γ) M))
      → (o : O ∈ S) → (v : Spine (input O (Data S γ))) 
      → elim M β (output v ⨾ apps (at o (ctors S γ)) v) ≡ (coe-Tm (sec-coh-Ty (elim M β) O _ _) (apps (at o β) (elim M β $ v)))
      
  