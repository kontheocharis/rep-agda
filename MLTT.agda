module MLTT where

open import Agda.Builtin.Nat using (Nat; suc; zero)
open import Data.Fin.Base using (Fin; suc; zero)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)


data Ty : Set

data Tm : Ty → Set

variable
  Any : Set _
  A A' : Ty
  B B' : Tm _ → Ty
  t t' u u' : Tm _
  v v' w w' : Tm _ → Tm _
  
-- data Ty≈ : Ty → Ty → Set
  
-- data Tm≈ : (T : Ty≈ A A') → Tm A → Tm A' → Set

-- variable
--   A≈ A≈' : Ty≈ _ _
--   B≈ B≈' : Tm≈ _ _ _ → Ty≈ _ _
--   t≈ t≈' u≈ u≈' : Tm≈ _ _ _
--   v≈ v≈' w≈ w≈' : Tm≈ _ _ _ → Tm≈ _ _ _

{-# NO_POSITIVITY_CHECK #-}
data Ty where
  U : Ty
  El : Tm U → Ty
  ⊤ : Ty
  Π : (A : Ty) → (Tm A → Ty) → Ty
  Σ : (A : Ty) → (Tm A → Ty) → Ty
  Id : {A : Ty} → Tm A → Tm A → Ty

syntax Π A (λ x → B) = [ x ∶ A ] ⇒ B
syntax Σ A (λ x → B) = [ x ∶ A ] × B

data Tm where
  lam : ((a : Tm A) → Tm (B a)) → Tm (Π A B)
  app : Tm (Π A B) → (a : Tm A) → Tm (B a)
  pair : (a : Tm A) → Tm (B a) → Tm (Σ A B)
  tt : Tm ⊤
  fst : Tm (Σ A B) → Tm A
  snd : (p : Tm (Σ A B)) → Tm (B (fst p))
  refl : {a : Tm A} → Tm (Id a a)
  J : (P : (a : Tm A) → (b : Tm A) → Tm (Id a b) → Ty)
    → ((a : Tm A) → Tm (P a a refl))
    → {a : Tm A} → {b : Tm A} → (p : Tm (Id a b)) → Tm (P a b p)
  
-- data Ty≈ where
--   Refl : Ty≈ A A
--   Sym : Ty≈ A A' → Ty≈ A' A
--   Trans : ∀ {A'' A'''} → Ty≈ A A' → Ty≈ A'' A''' → Ty≈ A A'''
  
--   U≈ : Ty≈ U U
--   El≈ : Tm≈ A≈ t t' → Ty≈ (El t) (El t')
--   Π≈ : (T : Ty≈ A A') → (Tm≈ A≈ t t' → Ty≈ (B t) (B' t')) → Ty≈ (Π A B) (Π A' B')
--   Σ≈ : (T : Ty≈ A A') → (Tm≈ A≈ t t' → Ty≈ (B t) (B' t')) → Ty≈ (Σ A B) (Σ A' B')
--   Id≈ : Tm≈ A≈ t t' → Tm≈ A≈ u u' → Ty≈ (Id t u) (Id t' u')

-- data Tm≈ where
--   Refl : Tm≈ Refl t t
--   Sym : Tm≈ A≈ t t' → Tm≈ (Sym A≈) t' t
--   Trans : ∀ {A'' A'''} {t'' t'''} → Tm≈ A≈ t t' → Tm≈ A≈' t'' t''' 
--         → Tm≈ (Trans A≈ A≈') t t'''
--   lam≈ : ∀ {v v'} → ((a≈ : Tm≈ A≈ t t') → Tm≈ (B≈ a≈) (v t) (v' t')) → Tm≈ (Π≈ A≈ B≈) (lam v) (lam v')