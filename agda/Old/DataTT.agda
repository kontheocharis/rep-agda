{-# OPTIONS --prop --allow-unsolved-metas #-}
module DataTT where

open import Agda.Builtin.Nat using (Nat; suc; zero)
open import Data.Fin.Base using (Fin; suc; zero)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Data.Product.Base using (_,_) renaming (Σ to Pair)
import Tel

data Ty : Set

data Tm : Ty → Set

open Tel.ForTheory Ty Tm

data Op : Tel → Set

data Sig : Tel → Set

variable
  Any : Set _
  A A' : Ty
  B B' : Tm _ → Ty
  t t' u u' : Tm _
  v v' w w' : Tm _ → Tm _
  S S' : Sig _
  O O' : Op _
  
-- data Ty≈ : Ty → Ty → Set
  
-- data Tm≈ : (T : Ty≈ A A') → Tm A → Tm A' → Set

-- variable
--   A≈ A≈' : Ty≈ _ _
--   B≈ B≈' : Tm≈ _ _ _ → Ty≈ _ _
--   t≈ t≈' u≈ u≈' : Tm≈ _ _ _
--   v≈ v≈' w≈ w≈' : Tm≈ _ _ _ → Tm≈ _ _ _
  
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
  El : Tm U → Ty
  ⊤ : Ty
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

record SigSystem : Set1 where
  field
    Sigₛ : Tel → Set
    Opₛ : Tel → Set
    _∈ₛ_ : Opₛ Δ → Sigₛ Δ → Set
    inputₛ : Opₛ Δ → (Spine Δ → Ty) → Tel
    outputₛ : {O : Opₛ Δ} → Spine (inputₛ O X) → Spine Δ
    algₛ : (S : Sigₛ Δ) → (X : Spine Δ → Ty) → Tel
    dispAlgₛ : {S : Sigₛ Δ} → Spine (algₛ S X) → (Y : Spine (Δ ▷ X) → Ty) → Tel
    

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

_-X:_ : (S : Sig Δ) → Spine (indAlg S) → Tm ([ δ ∷ Δ ] ⇒ U)
S -X: (X , _) = X

_-α:_ : ∀ (S : Sig Δ) → (γ : Spine (indAlg S)) → Spine (alg S (λ δ → El (apps (S -X: γ) δ)))
S -α: (X , ακ) with split {Δ = alg S (λ δ → El (apps X δ))} ακ
... | (α , κ) = α

_-κ:-_ : (S : Sig Δ) → (γ : Spine (indAlg S)) → Tm (ind {S = S} (S -α: γ))
S -κ:- (X , ακ) with split {Δ = alg S (λ δ → El (apps X δ))} ακ
... | (_ , κ , []) = κ
  
record DataTT-model : Set1 where
  field
    -- Type interpretation
    Ty∘ : Set
    Tm∘ : Ty∘ → Set
    
    -- Universe
    U∘ : Ty∘
    El∘ : Tm∘ U∘ → Ty∘
    
    -- Unit type
    ⊤∘ : Ty∘
    tt∘ : Tm∘ ⊤∘
    
    -- Dependent function type (Π)
    Π∘ : (A : Ty∘) → (Tm∘ A → Ty∘) → Ty∘
    lam∘ : {A : Ty∘} → {B : Tm∘ A → Ty∘}
          → ((a : Tm∘ A) → Tm∘ (B a))
          → Tm∘ (Π∘ A B)
    app∘ : {A : Ty∘} → {B : Tm∘ A → Ty∘}
          → Tm∘ (Π∘ A B)
          → (a : Tm∘ A)
          → Tm∘ (B a)
    
    -- Dependent pair type (Σ)
    Σ∘ : (A : Ty∘) → (Tm∘ A → Ty∘) → Ty∘
    pair∘ : {A : Ty∘} → {B : Tm∘ A → Ty∘}
           → (a : Tm∘ A)
           → (b : Tm∘ (B a))
           → Tm∘ (Σ∘ A B)
    fst∘ : {A : Ty∘} → {B : Tm∘ A → Ty∘}
          → Tm∘ (Σ∘ A B)
          → Tm∘ A
    snd∘ : {A : Ty∘} → {B : Tm∘ A → Ty∘}
          → (p : Tm∘ (Σ∘ A B))
          → Tm∘ (B (fst∘ p))
    
    -- Identity type
    Id∘ : {A : Ty∘} → Tm∘ A → Tm∘ A → Ty∘
    refl∘ : {A : Ty∘} → {a : Tm∘ A} → Tm∘ (Id∘ a a)
    J∘ : {A : Ty∘}
        → (P : (a : Tm∘ A) → (b : Tm∘ A) → Tm∘ (Id∘ a b) → Ty∘)
        → ((a : Tm∘ A) → Tm∘ (P a a refl∘))
        → {a : Tm∘ A} → {b : Tm∘ A} → (p : Tm∘ (Id∘ a b))
        → Tm∘ (P a b p)
        
    -- Repr
    Repr∘ : Ty∘ → Ty∘
    unrepr∘ : {A : Ty∘} → Tm∘ (Repr∘ A) → Tm∘ A
    repr∘ : {A : Ty∘} → Tm∘ A → Tm∘ (Repr∘ A)

  
record DataTT-displayed-model : Set1 where
  field
    -- Type interpretation
    Ty∙ : Ty → Set
    Tm∙ : Ty∙ A → Tm A → Set
    
    -- Universe
    U∙ : Ty∙ U
    El∙ : (t : Tm U) → Tm∙ U∙ t → Ty∙ (El t)
    
    -- Unit type
    ⊤∙ : Ty∙ ⊤
    tt∙ : Tm∙ ⊤∙ tt
    
    -- Dependent function type (Π)
    Π∙ : (A∙ : Ty∙ A) → ((a : Tm A) → Tm∙ A∙ a → Ty∙ (B a)) → Ty∙ (Π A B)
    lam∙ : {A∙ : Ty∙ A} → {B∙ : (a : Tm A) → Tm∙ A∙ a → Ty∙ (B a)}
          → (f : (a : Tm A) → Tm (B a))
          → ((a : Tm A) → (a∙ : Tm∙ A∙ a) → Tm∙ (B∙ a a∙) (f a))
          → Tm∙ (Π∙ A∙ B∙) (lam f)
    app∙ : {A∙ : Ty∙ A} → {B∙ : (a : Tm A) → Tm∙ A∙ a → Ty∙ (B a)}
          → {f : Tm (Π A B)} → Tm∙ (Π∙ A∙ B∙) f
          → (a : Tm A) → (a∙ : Tm∙ A∙ a)
          → Tm∙ (B∙ a a∙) (app f a)
    
    -- Dependent pair type (Σ)
    Σ∙ : (A∙ : Ty∙ A) → ((a : Tm A) → Tm∙ A∙ a → Ty∙ (B a)) → Ty∙ (Σ A B)
    pair∙ : {A∙ : Ty∙ A} → {B∙ : (a : Tm A) → Tm∙ A∙ a → Ty∙ (B a)}
           → {a : Tm A} → (a∙ : Tm∙ A∙ a)
           → {b : Tm (B a)} → (b∙ : Tm∙ (B∙ a a∙) b)
           → Tm∙ (Σ∙ A∙ B∙) (pair a b)
    fst∙ : {A∙ : Ty∙ A} → {B∙ : (a : Tm A) → Tm∙ A∙ a → Ty∙ (B a)}
          → {p : Tm (Σ A B)} → (p∙ : Tm∙ (Σ∙ A∙ B∙) p)
          → Tm∙ A∙ (fst p)
    snd∙ : {A∙ : Ty∙ A} → {B∙ : (a : Tm A) → Tm∙ A∙ a → Ty∙ (B a)}
          → {p : Tm (Σ A B)} → (p∙ : Tm∙ (Σ∙ A∙ B∙) p)
          → Tm∙ (B∙ (fst p) (fst∙ p∙)) (snd p)
    
    -- Identity type
    Id∙ : {A∙ : Ty∙ A} → {a b : Tm A} 
         → Tm∙ A∙ a → Tm∙ A∙ b 
         → Ty∙ (Id a b)
    refl∙ : {A∙ : Ty∙ A} → {a : Tm A} → (a∙ : Tm∙ A∙ a)
           → Tm∙ (Id∙ a∙ a∙) refl
    J∙ : {A∙ : Ty∙ A}
        → (P : (a : Tm A) → (b : Tm A) → Tm (Id a b) → Ty)
        → (P∙ : (a : Tm A) → (a∙ : Tm∙ A∙ a)
                → (b : Tm A) → (b∙ : Tm∙ A∙ b)
                → (p : Tm (Id a b)) → (p∙ : Tm∙ (Id∙ a∙ b∙) p)
                → Ty∙ (P a b p))
        → (reflP : (a : Tm A) → Tm (P a a refl))
        → ((a : Tm A) → (a∙ : Tm∙ A∙ a) → Tm∙ (P∙ a a∙ a a∙ refl (refl∙ a∙)) (J P reflP refl))
        → {a : Tm A} → (a∙ : Tm∙ A∙ a)
        → {b : Tm A} → (b∙ : Tm∙ A∙ b)
        → {p : Tm (Id a b)} → (p∙ : Tm∙ (Id∙ a∙ b∙) p)
        → Tm∙ (P∙ a a∙ b b∙ p p∙) (J P reflP p)
        
record DataTT-section (m : DataTT-displayed-model) : Set1 where
  open DataTT-displayed-model m
  field
    σTy : (A : Ty) → Ty∙ A
    σTm : (A : Ty) → (t : Tm A) → Tm∙ (σTy A) t
        
open DataTT-displayed-model
open DataTT-section 

{-# TERMINATING #-}
DataTT-induction : (m : DataTT-displayed-model) → DataTT-section m
DataTT-induction = {!   !}
        
record DataTT-transformation (m : DataTT-model) : Set1 where
  open DataTT-model m
  field
    τTy : Ty → Ty∘
    τTm : (A : Ty) → Tm A → Tm∘ (τTy A)

{-# TERMINATING #-}
DataTT-rec : (m : DataTT-model) → DataTT-transformation m
DataTT-rec = {!   !}

-- DataTT-induction m .σTy U = m .U∙
-- DataTT-induction m .σTy (El t) = m .El∙ t (DataTT-induction m .σTm U t)
-- DataTT-induction m .σTy (Π A B) = m .Π∙ (DataTT-induction m .σTy A) (λ a a' → DataTT-induction m .σTy (B a))
-- DataTT-induction m .σTy (Σ A B) = m .Σ∙ (DataTT-induction m .σTy A) (λ a a' → DataTT-induction m .σTy (B a))
-- DataTT-induction m .σTy (Id a b) = m .Id∙ (DataTT-induction m .σTm _ a) (DataTT-induction m .σTm _ b)
-- DataTT-induction m .σTy ⊤ = m .⊤∙
-- DataTT-induction m 