{-# OPTIONS --prop #-}
module TT.Repr where

open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; subst; sym; cong; trans; cong₂)

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
    
    
record Repr-compat-Π (T : TT)
  {{T-R : Repr-structure T}}
  {{T-Π : Π-structure T}} : Set1 where
  open TT T
  open Repr-structure T-R
  open Π-structure T-Π

   -- you can also make an alternative version of this with the rule
   -- Repr (Π A B) ≡ Π (Repr A) (λ a → Repr (B (unrepr a)))
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
    
record Repr-compat-Σ (T : TT)
  {{T-R : Repr-structure T}}
  {{T-Σ : Σ-structure T}} : Set1 where
  open TT T
  open Repr-structure T-R
  open Σ-structure T-Σ

  field
    Repr-Σ : ∀ {A} {B : Tm A → Ty} → Repr (Σ A B) ≡ Σ (Repr A) (λ a → Repr (B (unrepr a)))

    repr-fst : ∀ {A} {B : Tm A → Ty} {t : Tm (Σ A B)}
      → repr (fst t) ≡ fst (coe-Tm Repr-Σ (repr t))
    unrepr-fst : ∀ {A} {B : Tm A → Ty} {t : Tm (Repr (Σ A B))}
      → unrepr (fst (coe-Tm Repr-Σ t)) ≡ fst (unrepr t)

    repr-snd : ∀ {A} {B : Tm A → Ty} {t : Tm (Σ A B)}
      → repr (snd t) ≡ snd (coe-Tm Repr-Σ (repr t))
        by (cong (λ t → Tm (Repr (B t))) (trans (cong fst (sym Repr-η-1)) (sym unrepr-fst)))
    unrepr-snd : ∀ {A} {B : Tm A → Ty} {t : Tm (Repr (Σ A B))}
      → unrepr (snd (coe-Tm Repr-Σ t)) ≡ snd (unrepr t)
        by (cong (λ t → Tm (B t)) unrepr-fst)

    repr-pair : ∀ {A} {B : Tm A → Ty} {a : Tm A} {b : Tm (B a)}
      → repr (pair {A = A} {B = B} a b)
          ≡ pair {A = Repr A} {B = λ a → Repr (B (unrepr a))}
            (repr a)
            (repr (coe-Tm (cong B (sym Repr-η-1)) b))
        by (cong Tm Repr-Σ)
    unrepr-pair : ∀ {A} {B : Tm A → Ty} {a : Tm (Repr A)} {b : Tm (Repr (B (unrepr a)))}
      → unrepr (coe-Tm (sym (Repr-Σ {A = A} {B = B}))
            (pair {A = Repr A} {B = λ a → Repr (B (unrepr a))} a b))
          ≡ pair {A = A} {B = B} (unrepr a) (unrepr b) 
          
record Repr-compat-⊤ (T : TT)
  {{T-R : Repr-structure T}}
  {{T-⊤ : ⊤-structure T}} : Set1 where
  open TT T
  open Repr-structure T-R
  open ⊤-structure T-⊤

  field
    Repr-⊤ : Repr ⊤ ≡ ⊤
    repr-tt : repr tt ≡ tt by (cong Tm Repr-⊤)
    unrepr-tt : unrepr (coe-Tm (sym Repr-⊤) tt) ≡ tt
    
record Repr-compat-Id (T : TT)
  {{T-R : Repr-structure T}}
  {{T-Id : Id-structure T}} : Set1 where
  open TT T
  open Repr-structure T-R
  open Id-structure T-Id

  field
    Repr-Id : ∀ {A} {x y : Tm A} → Repr (Id x y) ≡ Id (repr x) (repr y)
    repr-rfl : ∀ {A} {x : Tm A} → repr (rfl x) ≡ rfl (repr x) by (cong Tm Repr-Id)
    unrepr-rfl : ∀ {A} {x : Tm (Repr A)} →
      unrepr (coe-Tm (sym (trans Repr-Id (cong₂ Id Repr-η-2 Repr-η-2))) (rfl x)) ≡ rfl (unrepr x) 

    repr-J : {A : Ty}
        → (P : (a : Tm A) → (b : Tm A) → Tm (Id a b) → Ty)
        → (r : (a : Tm A) → Tm (P a a (rfl a)))
        → {a : Tm A} → {b : Tm A} → (p : Tm (Id a b))
        → repr (J P r p) ≡ J (λ a b p → Repr (P a b p)) (λ a → repr (r a)) p

    unrepr-J : {A : Ty}
        → (P : (a : Tm A) → (b : Tm A) → Tm (Id a b) → Ty)
        → (r : (a : Tm A) → Tm (Repr (P a a (rfl a))))
        → {a : Tm A} → {b : Tm A} → (p : Tm (Id a b))
        → unrepr (J (λ a b p → Repr (P a b p)) r p) ≡ J P (λ a → unrepr (r a)) p