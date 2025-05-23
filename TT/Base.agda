{-# OPTIONS --rewriting #-}
module TT.Base where

open import TT.Core
open import TT.Tel
open import TT.Utils

open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; subst; sym; trans; cong)

-- Base type formers for a shallow embedding of
-- Martin-Löf Type Theory in Agda. (AKA SOGAT form)
--
-- Definitional equality of these structures
-- is given by the propositional equality of Agda _≡_.

-- Universes
record U-structure (T : TT) : Set1 where
  open TT T
  field
    U : Ty

    El : Tm U → Ty
    code : Ty → Tm U

    U-η-1 : ∀ {A} → El (code A) ≡ A
    U-η-2 : ∀ {t} → code (El t) ≡ t
    
-- Functions
record Π-structure (T : TT) : Set1 where
  open TT T
  field
    Π : (A : Ty) → (Tm A → Ty) → Ty

    lam : ∀ {A} {B : Tm A → Ty}
      → ((a : Tm A) → Tm (B a)) → Tm (Π A B)

    app : ∀ {A} {B : Tm A → Ty}
      → Tm (Π A B) → (a : Tm A) → Tm (B a)

    Π-β : ∀ {A} {B : Tm A → Ty} {f : (a : Tm A) → Tm (B a)} {t : Tm A}
      → app (lam f) t ≡ f t
    Π-η : ∀ {A} {B : Tm A → Ty} {f : Tm (Π A B)}
      → lam (λ t → app f t) ≡ f
      

  syntax Π A (λ x → B) = [ x ∶ A ] ⇒ B
      
  open Tel-construction T

  -- Telescopic versions of Π

  Πs : (Δ : Tel) → (Spine Δ → Ty) → Ty
  Πs ∙ t = t []
  Πs (ext A Δ) t = [ a ∶ A ] ⇒ Πs (Δ a) (λ δ → t (a , δ))

  syntax Πs Δ (λ δ → B) = [ δ ∷ Δ ] ⇒ B

  lams : ∀ {Δ Y} → ((δ : Spine Δ) → Tm (Y δ)) → Tm (Πs Δ Y)
  lams {Δ = ∙} f = f []
  lams {Δ = ext A Δ} f = lam (λ a → lams (λ δ → f (a , δ)))

  apps : ∀ {Δ Y} → Tm (Πs Δ Y) → (δ : Spine Δ) → Tm (Y δ)
  apps {Δ = ∙} t [] = t
  apps {Δ = ext A Δ} t (a , δ) = apps (app t a) δ

  Πs-β : ∀ {Δ} {B : Spine Δ → Ty} {f : (δ : Spine Δ) → Tm (B δ)} {δ : Spine Δ}
    → apps {Δ = Δ} (lams f) δ ≡ f δ
  Πs-β {Δ = ∙} {B} {f} {δ = []} = refl
  Πs-β {Δ = ext A Δ} {B} {f} {δ = (a , δ)} = trans (cong (λ f → apps f δ) Π-β) (Πs-β {δ = δ})
  
  Πs-η : ∀ {Δ} {B : Spine Δ → Ty} {f : Tm (Πs Δ B)}
    → lams (λ δ → apps {Δ = Δ} f δ) ≡ f
  Πs-η {Δ = ∙} {B} {f} = refl
  Πs-η {Δ = ext A Δ} {B} {f} = trans (cong lam (funext (λ x → Πs-η {Δ = Δ x}))) Π-η
  
  
record ⊤-structure (T : TT) : Set1 where
  open TT T
  field
    ⊤ : Ty

    tt : Tm ⊤

    ⊤-η : ∀ {t} → tt ≡ t

record Σ-structure (T : TT) : Set1 where
  open TT T
  field
    Σ : (A : Ty) → (Tm A → Ty) → Ty

    pair : {A : Ty} → {B : Tm A → Ty}
      → (a : Tm A)
      → (b : Tm (B a))
      → Tm (Σ A B)
    fst : {A : Ty} → {B : Tm A → Ty}
      → Tm (Σ A B)
      → Tm A
    snd : {A : Ty} → {B : Tm A → Ty}
      → (p : Tm (Σ A B))
      → Tm (B (fst p))

    Σ-β-fst : ∀ {A} {B : Tm A → Ty} {a : Tm A} {b : Tm (B a)}
      → fst (pair {B = B} a b) ≡ a
    Σ-β-snd : ∀ {A} {B : Tm A → Ty} {a : Tm A} {b : Tm (B a)}
      → snd (pair a b) ≡ b
    Σ-η : ∀ {A} {B : Tm A → Ty} {p : Tm (Σ A B)}
      → pair (fst p) (snd p) ≡ p

  syntax Σ A (λ x → B) = [ x ∶ A ] × B


module Σs-notation (T : TT) (T-Σ : Σ-structure T) (T-⊤ : ⊤-structure T) where
  open TT T
  open Σ-structure T-Σ
  open ⊤-structure T-⊤
  open Tel-construction T

  Σs : Tel → Ty
  Σs ∙ = ⊤
  Σs (ext A Δ) = Σ A (λ a → Σs (Δ a))
  
  get-spine : Tm (Σs Δ) → Spine Δ
  get-spine {Δ = ∙} tt = []
  get-spine {Δ = ext A Δ} q = fst q , get-spine (snd q)
      
module Us-notation (T : TT) (T-Π : Π-structure T) (T-U : U-structure T) where
  open TT T
  open Π-structure T-Π
  open U-structure T-U
  open Tel-construction T

  dcodes : (Spine Δ → Ty) → Tm ([ δ ∷ Δ ] ⇒ U)
  dcodes x = lams (λ δ → code (x δ))

  dEls : Tm ([ δ ∷ Δ ] ⇒ U) → (Spine Δ → Ty)
  dEls x = (λ δ → El (apps x δ))
  
  cong-dEls : ∀ {Δ : Tel} {δ δ'} → (P : Tm ([ δ ∷ Δ ] ⇒ U)) → δ ≡ δ' → dEls {Δ = Δ} P δ ≡ dEls {Δ = Δ} P δ'
  cong-dEls P refl = refl

  dEls-dcodes-β : ∀ {Δ : Tel} {P : Spine Δ → Ty} (δ : Spine Δ) → dEls (dcodes P) δ ≡ P δ
  dEls-dcodes-β {P = P} δ = trans (cong (λ t → El t) (Πs-β {f = λ δx → code (P δx)})) U-η-1

    
record Id-structure (T : TT) : Set1 where
  open TT T
  field
    Id : {A : Ty} → Tm A → Tm A → Ty

    rfl : {A : Ty} → (a : Tm A) → Tm (Id a a)
    J : {A : Ty}
        → (P : (a : Tm A) → (b : Tm A) → Tm (Id a b) → Ty)
        → ((a : Tm A) → Tm (P a a (rfl a)))
        → {a : Tm A} → {b : Tm A} → (p : Tm (Id a b))
        → Tm (P a b p)
        
    Id-β : ∀ {A} {P} {a} {r : (a : Tm A) → Tm (P a a (rfl a))}
      → J P r (rfl a) ≡ r a

  Id-uip-right : ∀ {A} {a b : Tm A} (p : A ≡ A) → Tm (Id a b) → Tm (Id a (coe-Tm p b))
  Id-uip-right {A = A} {a = a} {b = b} refl p = p

  Id-uip-left : ∀ {A} {a b : Tm A} (p : A ≡ A) → Tm (Id a b) → Tm (Id (coe-Tm p a) b)
  Id-uip-left {A = A} {a = a} {b = b} refl p = p
  
  Id-cong-defn : ∀ {A} {a a' b b' : Tm A} (p : a ≡ a') → (q : b ≡ b') → Id a b ≡ Id a' b'
  Id-cong-defn {A = A} {a = a} {b = b} refl refl = refl
  
  Id-lift : ∀ {A} {a b : Tm A} → a ≡ b → Tm (Id a b)
  Id-lift {A = A} {a = a} {b = b} refl = rfl _
      
record Id-extensional (T : TT) (T-Id : Id-structure T) : Set1 where
  open TT T
  open Id-structure T-Id
  field
    reflect : ∀ {A} {x y : Tm A} → Tm (Id x y) → x ≡ y
  
record MLTT-structure (T : TT) : Set1 where
  field
    T-U : U-structure T
    T-Π : Π-structure T
    T-Σ : Σ-structure T
    T-Id : Id-structure T
    T-⊤ : ⊤-structure T

  open U-structure T-U public
  open Π-structure T-Π public
  open Σ-structure T-Σ public
  open Id-structure T-Id public
  open ⊤-structure T-⊤ public

  open Tel-construction T public
  open Σs-notation T T-Σ T-⊤ public