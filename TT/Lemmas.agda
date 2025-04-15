{-# OPTIONS --rewriting #-}
module TT.Lemmas where 
  
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; subst; sym; cong; trans; cong₂; cong-app)

open import Relation.Binary.PropositionalEquality.Properties
  using (dcong)

open import TT.Utils
open import TT.Core
open import TT.Tel
open import TT.Base
open import TT.Data
open import TT.Sig
open import TT.Repr
open import Data.Product.Base using (_,_) renaming (Σ to Pair)

module Repr-lemmas
  (T : TT)
  (T-R : Repr-structure T)
  (T-MLTT : MLTT-structure T)
  (T-Data : Data-structure T T-MLTT)
  (T-Repr-Data : Repr-Data-structure T T-R T-MLTT T-Data) where
  
  open TT T
  open Repr-structure T-R
  open MLTT-structure T-MLTT
  open Data-structure T-Data
  open Repr-Data-structure T-Repr-Data
  
    
  -- Let's make these rewriting rules to not go crazy.
  abstract
    El' : Tm U → Ty
    El' = El

    code' : Ty → Tm U
    code' = code

    U-η-1' : ∀ {A} → El' (code' A) ≡ A
    U-η-1' = U-η-1

    U-η-2' : ∀ {t} → code' (El' t) ≡ t
    U-η-2' = U-η-2

    lam' : ∀ {A} {B : Tm A → Ty}
      → ((a : Tm A) → Tm (B a)) → Tm (Π A B)
    lam' = lam

    app' : ∀ {A} {B : Tm A → Ty}
      → Tm (Π A B) → (a : Tm A) → Tm (B a)
    app' = app

    Π-β' : ∀ {A} {B : Tm A → Ty} {f : (a : Tm A) → Tm (B a)} {t : Tm A}
      → app' (lam' f) t ≡ f t
    Π-β' = Π-β

    Π-η' : ∀ {A} {B : Tm A → Ty} {f : Tm (Π A B)}
      → lam' (λ t → app' f t) ≡ f
    Π-η' = Π-η

    rfl' : {A : Ty} → (a : Tm A) → Tm (Id a a)
    rfl' = rfl

    J' : {A : Ty}
        → (P : (a : Tm A) → (b : Tm A) → Tm (Id a b) → Ty)
        → ((a : Tm A) → Tm (P a a (rfl' a)))
        → {a : Tm A} → {b : Tm A} → (p : Tm (Id a b))
        → Tm (P a b p)
    J' = J
        
    Id-β' : ∀ {A} {P} {a} {r : (a : Tm A) → Tm (P a a (rfl' a))}
      → J' P r (rfl' a) ≡ r a
    Id-β' = Id-β

    repr' : ∀ {A} → Tm A → Tm (Repr A)
    repr' = repr

    unrepr' : ∀ {A} → Tm (Repr A) → Tm A
    unrepr' = unrepr

    Repr-η-1' : ∀ {A} {t : Tm A} → unrepr' (repr' t) ≡ t
    Repr-η-1' = Repr-η-1

    Repr-η-2' : ∀ {A} {t : Tm (Repr A)} → repr' (unrepr' t) ≡ t
    Repr-η-2' = Repr-η-2
  
  {-# REWRITE U-η-1' U-η-2' Π-β' Π-η' Id-β' Repr-η-1' Repr-η-2' #-}
  
  -- Internal isomorphism
  _≃_ : (A : Ty) → (B : Ty) → Ty
  _≃_ A B = [ f ∶ [ _ ∶ A ] ⇒ B ]
    × [ g ∶ [ _ ∶ B ] ⇒ A ]
    × [ _ ∶ [ a ∶ A ] ⇒ Id (app' g (app' f a)) a ]
    × ([ b ∶ B ] ⇒ Id (app' f (app' g b)) b)
    
  Id-coe : ∀ {A B : Ty}
    → Tm (Id (code' A) (code' B))
    → Tm A
    → Tm B
  Id-coe p a = (app' (J' (λ a' b' p → [ _ ∶ El' a' ] ⇒ El' b') (λ a → lam' (λ x → x)) p) a)
      
  Id-sym : ∀ {A} {a b : Tm A}
    → Tm (Id a b)
    → Tm (Id b a)
  Id-sym p = J' (λ a b p → Id b a) (λ t → rfl' t) p
  
  Id-trans : ∀ {A} {a b c : Tm A}
    → Tm (Id a b)
    → Tm (Id b c)
    → Tm (Id a c)
  Id-trans {A} {a} {b} {c} p q = app'
    (J' (λ a b p → [ _ ∶ Id b c ] ⇒ Id a c)
    (λ _ → lam' (λ y → y)) p) q
    
  J-Ty : (P : (A : Ty) → (B : Ty) → Tm (Id (code' A) (code' B)) → Ty)
      → ((A : Ty) → Tm (P A A (rfl' _)))
      → {A : Ty} → {B : Ty} → (p : Tm (Id (code' A) (code' B)))
      → Tm (P A B p)
  J-Ty P rflP {A} {B} p = J' {A = U} (λ a b p → P (El' a) (El' b) p)
          (λ t → (rflP (El' t))) p
    
  Id-cong : ∀ {A B} {a b : Tm A}
    → (f : Tm A → Tm B) 
    → Tm (Id a b)
    → Tm (Id (f a) (f b))
  Id-cong {A} {a} {b} f p = 
    J' (λ a b p → Id (f a) (f b))
      (λ t → rfl' _) p
      
  Id-coe-sym-id-1 : ∀ {A B : Ty} {x : Tm A}
    → (p : Tm (Id (code' B) (code' A)))
    → Tm (Id (Id-coe {A = B} p (Id-coe (Id-sym p) x)) x)
  Id-coe-sym-id-1 {A} {B} {x} p =
      app' (J-Ty (λ B A p → [ x ∶ A ] ⇒ Id (Id-coe {A = B} p (Id-coe (Id-sym p) x)) x)
        (λ t → lam' (λ x → rfl _)) {A = B} {B = A} p) x

  Id-coe-sym-id-2 : ∀ {A B : Ty} {x : Tm B}
    → (p : Tm (Id (code' B) (code' A)))
    → Tm (Id (Id-coe {A = A} (Id-sym p) (Id-coe p x)) x)
  Id-coe-sym-id-2 {A} {B} {x} p =
      app' (J-Ty (λ B A p → [ x ∶ B ] ⇒ Id (Id-coe {A = A} (Id-sym p) (Id-coe p x)) x)
        (λ t → lam' (λ x → rfl _)) {A = B} {B = A} p) x

  -- Repr is injective up to internal isomorphism
  Repr-injective : ∀ {A B : Ty}
    → Tm (Id (code' (Repr A)) (code' (Repr B)))
    → Tm (A ≃ B)
  Repr-injective {A} {B} p =
    pair (lam' (λ a → unrepr' (Id-coe p (repr' a))))
      (pair (lam' (λ b → unrepr' (Id-coe (Id-sym p) (repr' b))))
        (pair
          (lam' (λ a' → Id-cong (λ x → unrepr' x) (Id-coe-sym-id-2 {A = Repr B} {B = Repr A} p) ))
          (lam' (λ b' → Id-cong (λ x → unrepr' x) (Id-coe-sym-id-1 {A = Repr B} {B = Repr A} p) ))))