{-# OPTIONS --prop #-}
module TT.Sig where

open import TT.Core
open import TT.Base
open import TT.Tel 

open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; subst)
open import Data.Product.Base using (_,_) renaming (Σ to Pair)
 

module Sig-construction (T : TT)
  {{T-U : U-structure T}}
  {{T-Π : Π-structure T}}
  {{T-Σ : Σ-structure T}}
  {{T-Id : Id-structure T}}
  {{T-⊤ : ⊤-structure T}} 
  where

  open TT T
  open Tel-construction T
  open U-structure T-U
  open Π-structure T-Π
  open Σ-structure T-Σ
  open Id-structure T-Id
  open ⊤-structure T-⊤
  open Σs-notation T

  data Op : Tel → Set

  data Sig : Tel → Set

  data Sig where
    ε : Sig Δ
    _◁_ : Op Δ → Sig Δ → Sig Δ
    
  data Op where
    Πext : (A : Ty) → (Tm A → Op Δ) → Op Δ
    Πι : Spine Δ → Op Δ → Op Δ
    ι : Spine Δ → Op Δ

  variable
    S S' : Sig _
    O O' : Op _

  data _∈_ : Op Δ → Sig Δ → Set where
    here : O ∈ (O ◁ S)
    there : O ∈ S → O ∈ (O' ◁ S)
    
  sig-tel : (S : Sig Δ) → (∀ {O} → O ∈ S → Ty) → Tel
  sig-tel ε f = ∙
  sig-tel (O ◁ S) f = _ ∶ f here , sig-tel S (λ p → f (there p))

  sig-spine : (S : Sig Δ) → ∀ {P : ∀ {O} → O ∈ S → Ty} → (∀ {O} → (p : O ∈ S) → Tm (P p)) → Spine (sig-tel S P) 
  sig-spine ε f = []
  sig-spine (O ◁ S) f = f here , sig-spine S (λ p → f (there p))
  
  at : ∀ {Δ} {S : Sig Δ} {P : ∀ {O} → O ∈ S → Ty} {O} → (o : O ∈ S) → Spine (sig-tel S P) → Tm (P o)
  at {S = O ◁ S} here (αO , _) = αO
  at {S = O ◁ S} (there q) (_ , α) = at q α
  
  sig-spine-at : ∀ {Δ} {S : Sig Δ} {P : ∀ {O} → O ∈ S → Ty} {O}
    → (o : O ∈ S)
    → {f : ∀ {O} → (p : O ∈ S) → Tm (P p)}
    → at o (sig-spine S f) ≡ f o
  sig-spine-at {S = O ◁ S} here = refl
  sig-spine-at {S = O ◁ S} {P = P} (there o') = sig-spine-at {P = λ o' → P (there o')} o'
    
  input : (O : Op Δ) → (Spine Δ → Ty) → Tel
  input (Πext A O') X = a ∶ A , input (O' a) X
  input (Πι δ O') X = _ ∶ X δ , input O' X
  input (ι δ) X = ∙

  output : {O : Op Δ} → Spine (input O X) → Spine Δ
  output {O = Πext A O'} (a , ν) = output ν
  output {O = Πι δ O'} (x , ν) = output ν
  output {O = ι δ} [] = δ

  alg : (S : Sig Δ) → (Spine Δ → Ty) → Tel
  alg S X = sig-tel S (λ {O} _ → [ ν ∷ input O X ] ⇒ X (output ν))

  disp-input : ∀ {X} → (O : Op Δ) → (Spine (Δ ▷ X) → Ty) → Tel
  disp-input {X = X} (Πext A O') Y = a ∶ A , disp-input (O' a) Y
  disp-input {X = X} (Πι δ O') Y = x ∶ X δ , _ ∶ Y (δ ⨾ x) , disp-input O' Y
  disp-input {X = X} (ι δ) Y = ∙

  disp-output : ∀ {Y} → {O : Op Δ} → Spine (disp-input {X = X} O Y) → Spine (alg (O ◁ ε) X) → Spine (Δ ▷ X)
  disp-output {Y = Y} {O = Πext A O'} (a , μ) (α , []) = disp-output μ (app α a , [])
  disp-output {Y = Y} {O = Πι δ O'} (x , y , μ) (α , []) = disp-output μ (app α x , [])
  disp-output {Y = Y} {O = ι δ} [] (α , []) = (δ ⨾ α)

  disp-alg : {S : Sig Δ} → Spine (alg S X) → (Spine (Δ ▷ X) → Ty) → Tel
  disp-alg {S = S} α Y = sig-tel S (λ {O} o → [ μ ∷ disp-input O Y ] ⇒ Y (disp-output μ (at o α , [])))

  Sec : (Y : Spine Δ → Ty) → Set
  Sec {Δ = Δ} Y = (δ : Spine Δ) → Tm (Y δ)

  _$_ : {Y : Spine (Δ ▷ X) → Ty} → Sec Y → Spine (input O X) → Spine (disp-input O Y)
  _$_ {O = Πext A O'} σ (a , v) = (a , σ $ v)
  _$_ {O = Πι δ O'} σ (x , v) = (x , σ (δ ⨾ x) , σ $ v)
  _$_ {O = ι δ} σ [] = []
    
  sec-coh-Ty : ∀ {X : Spine Δ → Ty} {Y : Spine (Δ ▷ X) → Ty}
      → (σ : Sec Y) → (O : Op Δ) → (v : Spine (input O X)) → (αO : Tm ([ ν ∷ input O X ] ⇒ X (output ν)))
      → Y (disp-output (σ $ v) (αO , [])) ≡ Y (output v ⨾ apps αO v)
  sec-coh-Ty σ (Πext A O') (a , v) αO = sec-coh-Ty σ (O' a) v (app αO a)
  sec-coh-Ty σ (Πι δ O') (x , v) αO = sec-coh-Ty σ O' v (app αO x)
  sec-coh-Ty σ (ι δ) [] αO = refl

  coh : {S : Sig Δ} → {α : Spine (alg S X)} → Spine (disp-alg α Y) → Sec Y → Tel
  coh {S = ε} [] σ = ∙
  coh {X = X} {S = (O ◁ S)} {α = αO , α} (βO , β) σ =
    _ ∶ [ v ∷ input O X ]
      ⇒ Id (σ (output v ⨾ apps αO v)) (coe-Tm (sec-coh-Ty σ O v αO) (apps βO (σ $ v)))
    , coh β σ

  ind : {S : Sig Δ} → (α : Spine (alg S X)) → Ty
  ind {Δ = Δ} {X = X} {S} α =
    [ Y ∶ [ _ ∷ Δ ▷ X ] ⇒ U ]
    ⇒ [ β ∷ disp-alg α (λ δx → El (apps Y δx)) ]
    ⇒ Σs (σ ∶ [ δx ∷ Δ ▷ X ] ⇒ El (apps Y δx) , coh β (apps σ))

  ind-alg : (S : Sig Δ) → Tel
  ind-alg {Δ = Δ} S = (X ∶ [ δ ∷ Δ ] ⇒ U , α ∷ alg S (λ δ → El (apps X δ)) , κ ∶ ind α , ∙)

  _-X:_ : (S : Sig Δ) → Spine (ind-alg S) → Tm ([ δ ∷ Δ ] ⇒ U)
  S -X: (X , _) = X

  _-α:_ : ∀ (S : Sig Δ) → (γ : Spine (ind-alg S)) → Spine (alg S (λ δ → El (apps (S -X: γ) δ)))
  S -α: (X , ακ) with split {Δ = alg S (λ δ → El (apps X δ))} ακ
  ... | (α , κ) = α

  _-κ:-_ : (S : Sig Δ) → (γ : Spine (ind-alg S)) → Tm (ind {S = S} (S -α: γ))
  S -κ:- (X , ακ) with split {Δ = alg S (λ δ → El (apps X δ))} ακ
  ... | (_ , κ , []) = κ
