{-# OPTIONS --rewriting #-}
module DataTT where

open import Agda.Builtin.Nat using (Nat; suc; zero)
open import Data.Fin.Base using (Fin; suc; zero)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Data.Product.Base using (_,_) renaming (Σ to Pair)

{-# BUILTIN REWRITE _≡_ #-}

data Ty : Set

data Tm : Ty → Set

data Tel : Set

data Spine : Tel → Set

data Op : Tel → Set

data Sig : Tel → Set

variable
  Any : Set _
  A A' : Ty
  B B' : Tm _ → Ty
  t t' u u' : Tm _
  v v' w w' : Tm _ → Tm _
  Δ Δ' : Tel
  X X' Y Y' : Spine _ → Ty
  δ δ' α β : Spine _
  S S' : Sig _
  O O' : Op _
  
-- data Ty≈ : Ty → Ty → Set
  
-- data Tm≈ : (T : Ty≈ A A') → Tm A → Tm A' → Set

-- variable
--   A≈ A≈' : Ty≈ _ _
--   B≈ B≈' : Tm≈ _ _ _ → Ty≈ _ _
--   t≈ t≈' u≈ u≈' : Tm≈ _ _ _
--   v≈ v≈' w≈ w≈' : Tm≈ _ _ _ → Tm≈ _ _ _

data Tel where
  ∙ : Tel
  ext : (A : Ty) → (Tm A → Tel) → Tel

data Spine where
  [] : Spine ∙
  _,_ : ∀ {Δ} → (a : Tm A) → Spine (Δ a) → Spine (ext A Δ)
  
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


-- init : ∀ {Δ Δ'} → Spine (extN Δ Δ') → Spine Δ
-- init {Δ = ∙} v = []
-- init {Δ = ext A Δ} (a , v) = a , init v

-- tail : ∀ {Δ Δ'} → (v : Spine (extN Δ Δ')) → Spine (Δ' (init v))
-- tail {Δ = ∙} v = v
-- tail {Δ = ext A Δ} (a , v) = tail {Δ = Δ a} v

split : ∀ {Δ Δ'} → Spine (extN Δ Δ') → Pair (Spine Δ) (λ δ → Spine (Δ' δ))
split {Δ = ∙} v = [] , v
split {Δ = ext A Δ} (a , v) = let (v' , v'') = split v in ((a , v') , v'')
  
data Sig where
  ε : Sig Δ
  _◁_ : Op Δ → Sig Δ → Sig Δ
  
data Op where
  Π : (A : Ty) → (Tm A → Op Δ) → Op Δ
  Πι : Spine Δ → Op Δ → Op Δ
  ι : Spine Δ → Op Δ

data _∈_ : Op Δ → Sig Δ → Set where
  here : O ∈ (O ◁ S)
  there : O ∈ S → O ∈ (O' ◁ S)
  
sigTel : (S : Sig Δ) → (∀ {O} → O ∈ S → Ty) → Tel
sigTel ε f = ∙
sigTel (O ◁ S) f = _ ∶ f here , sigTel S (λ p → f (there p))

sigSpine : (S : Sig Δ) → ∀ {P : ∀ {O} → O ∈ S → Ty} → (∀ {O} → (p : O ∈ S) → Tm (P p)) → Spine (sigTel S P) 
sigSpine ε f = []
sigSpine (O ◁ S) f = f here , sigSpine S (λ p → f (there p))
  
alg : (S : Sig Δ) → (Spine Δ → Ty) → Tel
input : (O : Op Δ) → (Spine Δ → Ty) → Tel
output : {O : Op Δ} → Spine (input O X) → Spine Δ

dispAlg : {S : Sig Δ} → Spine (alg S X) → (Spine (Δ ▷ X) → Ty) → Tel
dispInput : ∀ {X} → (O : Op Δ) → (Spine (Δ ▷ X) → Ty) → Tel
dispOutput : ∀ {Y} → {O : Op Δ} → Spine (dispInput {X = X} O Y) → Spine (alg (O ◁ ε) X) → Spine (Δ ▷ X)

Sec : (Y : Spine Δ → Ty) → Set
coh : {S : Sig Δ} → {α : Spine (alg S X)} → Spine (dispAlg α Y) → Sec Y → Tel
_$_ : {Y : Spine (Δ ▷ X) → Ty} → Sec Y → Spine (input O X) → Spine (dispInput O Y)

ind : {S : Sig Δ} → (α : Spine (alg S X)) → Ty
indAlg : (S : Sig Δ) → Tel
  
{-# NO_POSITIVITY_CHECK #-}
data Ty where
  U : Ty
  ⊤ : Ty
  El : Tm U → Ty
  Π : (A : Ty) → (Tm A → Ty) → Ty
  Σ : (A : Ty) → (Tm A → Ty) → Ty
  Id : {A : Ty} → Tm A → Tm A → Ty
  Data : (S : Sig Δ) → Spine (indAlg S) → Spine Δ → Ty
  Repr : Ty → Ty
  
syntax Π A (λ x → B) = [ x ∶ A ] ⇒ B
syntax Σ A (λ x → B) = [ x ∶ A ] × B

_⇒_ : Ty → Ty → Ty
A ⇒ B = [ x ∶ A ] ⇒ B

Πs : (Δ : Tel) → (Spine Δ → Ty) → Ty
Πs ∙ t = t []
Πs (ext A Δ) t = [ a ∶ A ] ⇒ Πs (Δ a) (λ δ → t (a , δ))

Σs : Tel → Ty
Σs ∙ = ⊤
Σs (ext A Δ) = Σ A (λ a → Σs (Δ a))

syntax Πs Δ (λ δ → B) = [ δ ∷ Δ ] ⇒ B

ctors : (S : Sig Δ) → (γ : Spine (indAlg S)) → Spine (alg S (Data S γ))

data Tm where
  lam : ((a : Tm A) → Tm (B a)) → Tm (Π A B)
  app : Tm (Π A B) → (a : Tm A) → Tm (B a)
  pair : (a : Tm A) → Tm (B a) → Tm (Σ A B)
  fst : Tm (Σ A B) → Tm A
  tt : Tm ⊤
  snd : (p : Tm (Σ A B)) → Tm (B (fst p))
  refl : {a : Tm A} → Tm (Id a a)
  J : (P : (a : Tm A) → (b : Tm A) → Tm (Id a b) → Ty)
    → ((a : Tm A) → Tm (P a a refl))
    → {a : Tm A} → {b : Tm A} → (p : Tm (Id a b)) → Tm (P a b p)

  ctor : ∀ {γ} → O ∈ S → (v : Spine (input O (Data S γ))) → Tm (Data S γ (output v))

  elim : ∀ {γ} → (M : Spine (Δ ▷ Data S γ) → Ty)
    → (β : Spine (dispAlg (ctors S γ) M))
    → (δx : Spine (Δ ▷ Data S γ)) → Tm (M δx)

  repr : ∀ {A} → Tm A → Tm (Repr A)
  unrepr : ∀ {A} → Tm (Repr A) → Tm A
    
apps : Tm (Πs Δ Y) → (δ : Spine Δ) → Tm (Y δ)
apps {Δ = ∙} t [] = t
apps {Δ = ext A Δ} t (a , δ) = apps (app t a) δ

lams : ((δ : Spine Δ) → Tm (Y δ)) → Tm (Πs Δ Y)
lams {Δ = ∙} f = f []
lams {Δ = ext A Δ} f = lam (λ a → lams (λ δ → f (a , δ)))

alg S X = sigTel S (λ {O} _ → [ ν ∷ input O X ] ⇒ X (output ν))

ctors S γ = sigSpine S (λ p → lams (ctor p))

input (Π A O') X = a ∶ A , input (O' a) X
input (Πι δ O') X = _ ∶ X δ , input O' X
input (ι δ) X = ∙

output {O = Π A O'} (a , ν) = output ν
output {O = Πι δ O'} (x , ν) = output ν
output {O = ι δ} [] = δ

dispAlg {S = ε} α Y = ∙
dispAlg {S = (O ◁ S)} (αO , α) Y = _ ∶ [ μ ∷ dispInput O Y ] ⇒ Y (dispOutput μ (αO , [])) , dispAlg α Y

dispInput {X = X} (Π A O') Y = a ∶ A , dispInput (O' a) Y
dispInput {X = X} (Πι δ O') Y = x ∶ X δ , _ ∶ Y (δ ⨾ x) , dispInput O' Y
dispInput {X = X} (ι δ) Y = ∙

dispOutput {Y = Y} {O = Π A O'} (a , μ) (α , []) = dispOutput μ (app α a , [])
dispOutput {Y = Y} {O = Πι δ O'} (x , y , μ) (α , []) = dispOutput μ (app α x , [])
dispOutput {Y = Y} {O = ι δ} [] (α , []) = (δ ⨾ α)
  
Sec {Δ = Δ} Y = (δ : Spine Δ) → Tm (Y δ)

_$_ {O = Π A O'} σ (a , v) = (a , σ $ v)
_$_ {O = Πι δ O'} σ (x , v) = (x , σ (δ ⨾ x) , σ $ v)
_$_ {O = ι δ} σ [] = []

secProducesDispOutput : ∀ {X : Spine Δ → Ty} {Y : Spine (Δ ▷ X) → Ty}
    → (σ : Sec Y) → (O : Op Δ) → (v : Spine (input O X)) → (αO : Tm ([ ν ∷ input O X ] ⇒ X (output ν)))
    → Y (dispOutput (σ $ v) (αO , [])) ≡ Y (output v ⨾ apps αO v)
secProducesDispOutput σ (Π A O') (a , v) αO = secProducesDispOutput σ (O' a) v (app αO a)
secProducesDispOutput σ (Πι δ O') (x , v) αO = secProducesDispOutput σ O' v (app αO x)
secProducesDispOutput σ (ι δ) [] αO = refl

metaCoeTm : A ≡ A' → Tm A → Tm A'
metaCoeTm refl t = t

coh {S = ε} [] σ = ∙
coh {X = X} {S = (O ◁ S)} {α = αO , α} (βO , β) σ =
  _ ∶ [ v ∷ input O X ]
    ⇒ Id (σ (output v ⨾ apps αO v)) (metaCoeTm (secProducesDispOutput σ O v αO) (apps βO (σ $ v)))
  , coh β σ
  
ind {Δ = Δ} {X = X} {S} α =
  [ Y ∶ [ _ ∷ Δ ▷ X ] ⇒ U ]
  ⇒ [ β ∷ dispAlg α (λ δx → El (apps Y δx)) ]
  ⇒ Σs (σ ∶ [ δx ∷ Δ ▷ X ] ⇒ El (apps Y δx) , coh β (apps σ))
  
indAlg {Δ = Δ} S = (X ∶ [ δ ∷ Δ ] ⇒ U , α ∷ alg S (λ δ → El (apps X δ)) , κ ∶ ind α , ∙)