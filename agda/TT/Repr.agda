{-# OPTIONS --prop #-}
module TT.Repr where

open import TT.Core
open import TT.Base

record Repr-structure (T : TT) : Set1 where
  open TT T
  field
    Repr : Ty → Ty

    repr : ∀ {A} → Tm A → Tm (Repr A)
    unrepr : ∀ {A} → Tm (Repr A) → Tm A

    Repr-η-1 : ∀ {A} {t : Tm A} → Tm~ refl-Ty (unrepr (repr t)) t
    Repr-η-2 : ∀ {A} {t : Tm (Repr A)} → Tm~ refl-Ty (repr (unrepr t)) t
    
    
record Repr-compat-Π (T : TT) (T-Π : Π-structure T) (T-R : Repr-structure T) : Set1 where
  open TT T
  open Π-structure T-Π
  open Repr-structure T-R

  field
    Repr-Π : ∀ {A} {B : Tm A → Ty} → Ty~ (Repr (Π A B)) (Π A (λ a → Repr (B a)))
    repr-lam : ∀ {A} {B : Tm A → Ty} {f : (a : Tm A) → Tm (B a)}
      → Tm~ Repr-Π (repr (lam f)) (lam (λ a → repr (f a)))
    unrepr-lam : ∀ {A} {B : Tm A → Ty} {f : (a : Tm A) → Tm (Repr (B a))}
      → Tm~ refl-Ty (unrepr (coe (sym-Ty Repr-Π) (lam f))) (lam (λ a → unrepr (f a)))
      
    repr-app : ∀ {A} {B : Tm A → Ty} {f : Tm (Π A B)} {a : Tm A}
      → Tm~ refl-Ty (repr (app f a)) (app (coe Repr-Π (repr f)) a)
    unrepr-app : ∀ {A} {B : Tm A → Ty} {f : Tm (Repr (Π A B))} {a : Tm A}
      → Tm~ refl-Ty (unrepr ((app (coe Repr-Π f) a))) (app (unrepr f) a)