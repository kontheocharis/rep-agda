module TT.Data where

open import TT.Core
open import TT.Base
open import TT.Tel 
 

record Sig-system (T : TT)
  {{T-U : U-structure T}}
  {{T-Π : Π-structure T}}
  {{T-Σ : Σ-structure T}}
  {{T-⊤ : ⊤-structure T}} : Set1
  where

  open TT T
  open Telescopes T
  open U-structure T-U
  open Π-structure T-Π
  open Σ-structure T-Σ
  open ⊤-structure T-⊤
  open Σs-notation T T-Σ T-⊤

  field
    Sig : Tel → Set
    Op : Tel → Set
    _∈_ : ∀ {Δ} → Op Δ → Sig Δ → Set
    input : ∀ {Δ} → Op Δ → (Spine Δ → Ty) → Tel
    output : ∀ {Δ X} {O : Op Δ} → Spine (input O X) → Spine Δ
    alg : ∀ {Δ} → (S : Sig Δ) → (X : Spine Δ → Ty) → Tel
    dispAlg : ∀ {Δ X} {S : Sig Δ} → Spine (alg S X) → (Y : Spine (Δ ▷ X) → Ty) → Tel
    coh : ∀ {Δ X Y} {S : Sig Δ} → {α : Spine (alg S X)} → Spine (dispAlg α Y) → ((δ : Spine (Δ ▷ X)) → Tm (Y δ)) → Tel

  ind : {S : Sig Δ} → (α : Spine (alg S X)) → Ty
  ind {Δ = Δ} {X = X} {S} α =
    [ Y ∶ [ _ ∷ Δ ▷ X ] ⇒ U ]
    ⇒ [ β ∷ dispAlg α (λ δx → El (apps Y δx)) ]
    ⇒ Σs (σ ∶ [ δx ∷ Δ ▷ X ] ⇒ El (apps Y δx) , coh β (apps σ))

  indAlg : (S : Sig Δ) → Tel
  indAlg {Δ = Δ} S = (X ∶ [ δ ∷ Δ ] ⇒ U , α ∷ alg S (λ δ → El (apps X δ)) , κ ∶ ind α , ∙)
    

record Data-structure (T : TT)
  {{T-U : U-structure T}}
  {{T-Π : Π-structure T}} 
  {{T-Σ : Σ-structure T}}
  {{T-⊤ : ⊤-structure T}} 
  {{T-Sig : Sig-system T}} : Set1
  where

  open TT T
  open Telescopes T
  open Sig-system T-Sig

  field
    Data : ∀ {Δ} → (S : Sig Δ) → Spine (indAlg S) → Spine Δ → Ty
  