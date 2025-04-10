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
    