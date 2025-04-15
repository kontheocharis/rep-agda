{-# OPTIONS --rewriting #-}
module TT.Sig where

open import TT.Utils
open import TT.Core
open import TT.Base
open import TT.Tel 

open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; subst; cong; cong₂; sym)
open import Data.Product.Base using (_,_) renaming (Σ to Pair)

-- Formalisation of first order algebraic signatures with a carrier
-- indexed by a telescope in some MLTT theory T.

module Sig-construction {T : TT} (T-MLTT : MLTT-structure T) where
  open TT T
  open MLTT-structure T-MLTT
  open Us-notation T T-Π T-U

  data Op : Tel → Set

  data Sig : Tel → Set

  data Sig where
    ε : ∀ {Δ} → Sig Δ
    _◁_ : ∀ {Δ} → Op Δ → Sig Δ → Sig Δ
    
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
  
  sig-spine-η : ∀ {Δ S} {Γ : ∀ {O} → O ∈ S → Tel}
    {Q : ∀ {O} → (o : O ∈ S) → Spine (Γ o) → Ty} {α : Spine (sig-tel {Δ = Δ} S (λ o → [ δ ∷ Γ o ] ⇒ Q o δ))}
    → sig-spine S {P = λ o → [ δ ∷ Γ o ] ⇒ Q o δ} (λ o → lams (λ v → apps {Δ = Γ o} (at o α) v)) ≡ α
  sig-spine-η {S = ε} {α = []} = refl
  sig-spine-η {S = O ◁ S} {Γ = Γ} {Q = Q} {α = (αO , α)} rewrite sig-spine-η {S = S} {Q = λ o → Q (there o)} {α = α}
    = cong (λ q → (q , α)) (Πs-η {Δ = Γ here})
  
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

  output : ∀ {X} → {O : Op Δ} → Spine (input O X) → Spine Δ
  output {O = Πext A O'} (a , ν) = output ν
  output {O = Πι δ O'} (x , ν) = output ν
  output {O = ι δ} [] = δ

  alg : (S : Sig Δ) → (Spine Δ → Ty) → Tel
  alg S X = sig-tel S (λ {O} _ → [ ν ∷ input O X ] ⇒ X (output ν))
  
  record _≈_ {Δ : Tel} (X : Spine Δ → Ty) (Y : Spine Δ → Ty) : Set where
    constructor reversible
    field
      forward : (δ : Spine Δ) → Tm (X δ) → Tm (Y δ)
      backward : (δ : Spine Δ) → Tm (Y δ) → Tm (X δ)
    
  open _≈_ public
  
  input-map : ∀ {X Y} {O : Op Δ} → (f : (δ : Spine Δ) → Tm (X δ) → Tm (Y δ)) → (v : Spine (input O X)) → Spine (input O Y)
  input-map {O = Πext A O'} f (a , v') = (a , input-map f v')
  input-map {O = Πι δ O'} f (x , v') = (f _ x , input-map f v')
  input-map {O = ι δ'} f [] = []
  
  input-map-id : ∀ {X} {O : Op Δ}
    → (v : Spine (input O X))
    → input-map (λ δ x → x) v ≡ v
  input-map-id {X = X} {O = Πext A O'} (a , v) rewrite input-map-id {X = X} {O = O' a} v = refl
  input-map-id {X = X} {O = Πι δ O'} (x , v) rewrite input-map-id {X = X} {O = O'} v = refl
  input-map-id {X = X} {O = ι δ'} [] = refl
  
  {-# REWRITE input-map-id #-}
  
  output-input-id : ∀ {X} {Y : (δ : Spine Δ) → Ty} {O : Op Δ} → (f : (δ : Spine Δ) → Tm (X δ) → Tm (Y δ)) → (v : Spine (input O X)) → output (input-map f v) ≡ output v
  output-input-id {X = X} {Y = Y} {O = Πext A O'} f (a , v) = output-input-id f v
  output-input-id {X = X} {Y = Y} {O = Πι δ O'} f (x , v) = output-input-id f v
  output-input-id {X = X} {Y = Y} {O = ι δ'} f [] = refl

  disp-input : ∀ {X} → (O : Op Δ) → (Spine (Δ ▷ X) → Ty) → Tel
  disp-input {X = X} (Πext A O') Y = a ∶ A , disp-input (O' a) Y
  disp-input {X = X} (Πι δ O') Y = x ∶ X δ , _ ∶ Y (δ ⨾ x) , disp-input O' Y
  disp-input {X = X} (ι δ) Y = ∙

  disp-output : ∀ {X Y} → {O : Op Δ} → Spine (disp-input {X = X} O Y) → Spine (alg (O ◁ ε) X) → Spine (Δ ▷ X)
  disp-output {Y = Y} {O = Πext A O'} (a , μ) (α , []) = disp-output μ (app α a , [])
  disp-output {Y = Y} {O = Πι δ O'} (x , y , μ) (α , []) = disp-output μ (app α x , [])
  disp-output {Y = Y} {O = ι δ} [] (α , []) = (δ ⨾ α)
  
  disp-input-map : ∀ {X} {Y Y'} {O : Op Δ}
    → (f : (δ : Spine (Δ ▷ X)) → Tm (Y δ) → Tm (Y' δ))
    → (v : Spine (disp-input O Y)) → Spine (disp-input O Y')
  disp-input-map {O = Πext A O'} f (a , v') = (a , disp-input-map f v')
  disp-input-map {O = Πι δ O'} f (x , y , v') = (x , f (δ ⨾ x) y , disp-input-map f v')
  disp-input-map {O = ι δ'} f [] = []
  
  disp-input-map-id : ∀ {X} {Y} {O : Op Δ}
    → (v : Spine (disp-input O Y))
    → disp-input-map {X = X} {Y = Y} {Y' = Y} {O = O} (λ δ x → x) v ≡ v
  disp-input-map-id {O = Πext A O'} (a , v) rewrite (disp-input-map-id {O = O' a} v) = refl
  disp-input-map-id {O = Πι δ O'} (x , y , v) rewrite (disp-input-map-id {O = O'} v) = refl
  disp-input-map-id {O = ι δ'} [] = refl
  
  {-# REWRITE disp-input-map-id #-}
  
  disp-output-disp-input-id : ∀ {X} {Y} {Y' : Spine (Δ ▷ X) → Ty} {O : Op Δ}
    → (f : (δ : Spine (Δ ▷ X)) → Tm (Y δ) → Tm (Y' δ))
    → (v : Spine (disp-input O Y))
    → (α : Spine (alg (O ◁ ε) X))
    → disp-output (disp-input-map f v) α ≡ disp-output v α
  disp-output-disp-input-id {X = X} {Y = Y} {O = Πext A O'} f (a , v) (α , []) = disp-output-disp-input-id f v (app α a , [])
  disp-output-disp-input-id {X = X} {Y = Y} {O = Πι δ O'} f (x , y , v) (α , []) = disp-output-disp-input-id f v (app α x , [])
  disp-output-disp-input-id {X = X} {Y = Y} {O = ι δ'} f [] (α , []) = refl
  
  {-# REWRITE disp-output-disp-input-id #-}

  disp-alg : ∀ {X} {S : Sig Δ} → Spine (alg S X) → (Spine (Δ ▷ X) → Ty) → Tel
  disp-alg {S = S} α Y = sig-tel S (λ {O} o → [ μ ∷ disp-input O Y ] ⇒ Y (disp-output μ (at o α , [])))

  disp-alg-map : ∀ {X} {S : Sig Δ} {α : Spine (alg S X)}
    → ∀ {Y Y'}
    → (f : (δ : Spine (Δ ▷ X)) → Tm (Y δ) → Tm (Y' δ))
    → (f-inv : (δ : Spine (Δ ▷ X)) → Tm (Y' δ) → Tm (Y δ))
    → Spine (disp-alg α Y)
    → Spine (disp-alg α Y')
  disp-alg-map {S = S} {α = α} {Y = Y} {Y' = Y'} f f-inv β
    = sig-spine S (λ {O} o → lams {Δ = disp-input O Y'} λ v →
      let x = at o β in
      let z = apps x (disp-input-map f-inv v) in
      f _ (apps x (disp-input-map f-inv v)))

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
  coh {X = X} {S = S} {α = α} β σ = sig-tel S (λ {O} o →
    let αO = at o α in
    let βO = at o β in
    [ v ∷ input O X ] ⇒ Id (σ (output v ⨾ apps αO v)) (coe-Tm (sec-coh-Ty σ O v αO) (apps βO (σ $ v))))

  ind : {S : Sig Δ} → (α : Spine (alg S X)) → Ty
  ind {Δ = Δ} {X = X} {S} α =
    [ Y ∶ [ _ ∷ Δ ▷ X ] ⇒ U ]
    ⇒ [ β ∷ disp-alg α (λ δx → El (apps Y δx)) ]
    ⇒ Σs (σ ∶ [ δx ∷ Δ ▷ X ] ⇒ dEls Y δx , coh β (apps σ))
    
  -- An inductive algebra packages the carrier, the algebra and the induction
  -- principle This is what we will add to the syntax.
  --
  -- Notice that there are no negative occurrences of any members of T in here,
  -- so the resulting syntax after adding IndAlg is still just second-order.
  record IndAlg {Δ : Tel} (S : Sig Δ) : Set where
    field
      Carrier : Tm ([ δ ∷ Δ ] ⇒ U)
      algebra : Spine (alg S (λ δ → El (apps Carrier δ)))
      induction : Tm (ind algebra)
      
  open IndAlg
  
  apply-ind : ∀ {Δ} {S : Sig Δ}
    → (γ : IndAlg S)
    → (P : Spine (Δ ▷ (dEls (γ .Carrier))) → Ty)
    → (β : Spine (disp-alg (γ .algebra) P))
    → Spine (σ ∶ [ δx ∷ Δ ▷ (λ δ → El (apps (γ .Carrier) δ)) ] ⇒ P δx , coh β (apps σ))
  apply-ind {Δ} {S} γ P β rewrite funext (λ δ → sym (dEls-dcodes-β {P = P} δ)) =
    let induction-on-P = app (γ .induction) (lams (λ δx → code (P δx))) in
    let section-coh = apps induction-on-P β in
    let section-coh-spine = get-spine section-coh in
    section-coh-spine
  
  apply-ind-sec : ∀ {Δ} {S : Sig Δ}
    → (γ : IndAlg S)
    → (P : Spine (Δ ▷ dEls (γ .Carrier)) → Ty)
    → (β : Spine (disp-alg (γ .algebra) P))
    → (δx : Spine (Δ ▷ dEls (γ .Carrier)))
    → Tm (P δx)
  apply-ind-sec {Δ} {S} γ P β δx with (apply-ind γ P β)
  apply-ind-sec {Δ} {S} γ P β δx | (σ , _) = apps σ δx
  
  apply-ind-coh : ∀ {Δ} {S : Sig Δ}
    → (γ : IndAlg S)
    → (P : Spine (Δ ▷ dEls (γ .Carrier)) → Ty)
    → (β : Spine (disp-alg (γ .algebra) P))
    → {O : Op Δ} → (o : O ∈ S) → (v : Spine (input O (dEls (γ .Carrier))) )
    → Tm (Id (apply-ind-sec γ P β (output v ⨾ apps (at o (γ .algebra)) v))
        ((coe-Tm (sec-coh-Ty (apply-ind-sec γ P β) O v (at o (γ .algebra))) (apps (at o β) (apply-ind-sec γ P β $ v)))))
  apply-ind-coh {Δ} {S} γ P β o v with (apply-ind γ P β)
  apply-ind-coh {Δ} {S} γ P β o v | (σ , coh) = apps (at o coh) v