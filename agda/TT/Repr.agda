{-# OPTIONS --prop #-}
module TT.Repr where

open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; subst; sym; cong)

open import Utils
open import TT.Core
open import TT.Base

record Repr-structure (T : TT) : Set1 where
  open TT T
  field
    Repr : Ty → Ty

    repr : ∀ {A} → Tm A → Tm (Repr A)
    unrepr : ∀ {A} → Tm (Repr A) → Tm A

    Repr-η-1 : ∀ {A} {t : Tm A} → unrepr (repr t) ≡ t
    Repr-η-2 : ∀ {A} {t : Tm (Repr A)} → repr (unrepr t) ≡ t
    
    
record Repr-compat-Π (T : TT) (T-Π : Π-structure T) (T-R : Repr-structure T) : Set1 where
  open TT T
  open Π-structure T-Π
  open Repr-structure T-R

  field
    Repr-Π : ∀ {A} {B : Tm A → Ty} → Repr (Π A B) ≡ Π A (λ a → Repr (B a))
    repr-lam : ∀ {A} {B : Tm A → Ty} {f : (a : Tm A) → Tm (B a)}
      → repr (lam f) ≡ lam (λ a → repr (f a)) by (cong Tm Repr-Π)
    unrepr-lam : ∀ {A} {B : Tm A → Ty} {f : (a : Tm A) → Tm (Repr (B a))}
      → unrepr (coe-Tm (sym Repr-Π) (lam f)) ≡ lam (λ a → unrepr (f a))
      
    repr-app : ∀ {A} {B : Tm A → Ty} {f : Tm (Π A B)} {a : Tm A}
      → repr (app f a) ≡ app (coe-Tm Repr-Π (repr f)) a
    unrepr-app : ∀ {A} {B : Tm A → Ty} {f : Tm (Repr (Π A B))} {a : Tm A}
      → unrepr ((app (coe-Tm Repr-Π f) a)) ≡ app (unrepr f) a