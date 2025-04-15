{-# OPTIONS --rewriting #-}
module TT.Repr where

open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; subst; sym; cong; trans; cong₂; cong-app)

open import TT.Utils
open import TT.Core
open import TT.Tel
open import TT.Base
open import TT.Data
open import TT.Sig
open import Data.Product.Base using (_,_) renaming (Σ to Pair)

record Repr-structure (T : TT) : Set1 where
  open TT T
  field
    -- This introduces the Repr modality which is an idempotent
    -- up-to-isomorphism fibered modality with the property that Repr A ≃ A by
    -- the η rules Repr-η-1 and Repr-η-2.
    
    -- Its role is purely intensional: relate data types to their
    -- underlying inductive algebras, leaving everything else unchanged.
    --
    -- We need to be careful to not introduce any definitional equalities
    -- that conflict with eliminating data types.

    Repr : Ty → Ty

    repr : ∀ {A} → Tm A → Tm (Repr A)
    unrepr : ∀ {A} → Tm (Repr A) → Tm A

    Repr-η-1 : ∀ {A} {t : Tm A} → unrepr (repr t) ≡ t
    Repr-η-2 : ∀ {A} {t : Tm (Repr A)} → repr (unrepr t) ≡ t
    
-- Below are combatibility equations with the rest of the MLTT syntax
    
record Repr-compat-Π (T : TT)
  (T-R : Repr-structure T)
  (T-Π : Π-structure T) : Set1 where
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
  (T-R : Repr-structure T)
  (T-Σ : Σ-structure T) : Set1 where
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
  (T-R : Repr-structure T)
  (T-⊤ : ⊤-structure T) : Set1 where
  open TT T
  open Repr-structure T-R
  open ⊤-structure T-⊤

  field
    Repr-⊤ : Repr ⊤ ≡ ⊤
    repr-tt : repr tt ≡ tt by (cong Tm Repr-⊤)
    unrepr-tt : unrepr (coe-Tm (sym Repr-⊤) tt) ≡ tt
    
record Repr-compat-Id (T : TT)
  (T-R : Repr-structure T)
  (T-Id : Id-structure T) : Set1 where
  open TT T
  open Repr-structure T-R
  open Id-structure T-Id

  field
    Repr-Id : ∀ {A} {x y : Tm A} → Repr (Id x y) ≡ Id (repr x) (repr y)
    repr-rfl : ∀ {A} {x : Tm A} → repr (rfl x) ≡ rfl (repr x) by (cong Tm Repr-Id)
    unrepr-rfl : ∀ {A} {x : Tm (Repr A)} →
      unrepr (coe-Tm (sym (trans Repr-Id (cong₂ Id Repr-η-2 Repr-η-2))) (rfl x)) ≡ rfl (unrepr x) 

    repr-J : ∀ {A : Ty}
        → {P : (a : Tm A) → (b : Tm A) → Tm (Id a b) → Ty}
        → {r : (a : Tm A) → Tm (P a a (rfl a))}
        → {a : Tm A} → {b : Tm A} → {p : Tm (Id a b)}
        → repr (J P r p) ≡ J (λ a b p → Repr (P a b p)) (λ a → repr (r a)) p

    unrepr-J : {A : Ty}
        → {P : (a : Tm A) → (b : Tm A) → Tm (Id a b) → Ty}
        → {r : (a : Tm A) → Tm (Repr (P a a (rfl a)))}
        → {a : Tm A} → {b : Tm A} → {p : Tm (Id a b)}
        → unrepr (J (λ a b p → Repr (P a b p)) r p) ≡ J P (λ a → unrepr (r a)) p


-- This is the main bit: the action of Repr on data types

record Repr-Data-structure
  (T : TT)
  (T-R : Repr-structure T)
  (T-MLTT : MLTT-structure T)
  (T-Data : Data-structure T T-MLTT) : Set1 where
  open TT T
  open Repr-structure T-R
  open MLTT-structure T-MLTT
  open Data-structure T-Data
  open Us-notation T T-Π T-U
  open Sig-construction T-MLTT
  
  
  field
    -- Representing data types gives back the carrier for the inductive algebra
    Repr-Data : ∀ {Δ S γ} δ → Repr (Data {Δ = Δ} S γ δ) ≡ dEls (γ .Carrier) δ

  -- <Helpers>
  -- The following are telescopic helpers for Repr.
  -- Each of these are uniquely determined by their η rules but
  -- are easier to work with in Agda if they are part of the record rather
  -- than auxilliary definitions.
    
  dRepr : ∀ {Δ} → (Spine Δ → Ty) → (Spine Δ → Ty)
  dRepr f δ = Repr (f δ)

  field
    -- repr the total space of a term
    repr-total : ∀ {Δ} {S : Sig Δ} {γ : IndAlg S} → Spine (Δ ▷ Data S γ) → Spine (Δ ▷ dEls (γ .Carrier))

    -- unrepr the total space of a term
    unrepr-total : ∀ {Δ} {S : Sig Δ} {γ : IndAlg S}  → Spine (Δ ▷ dEls (γ .Carrier)) → Spine (Δ ▷ Data S γ)
    
    repr-total-def : ∀ {Δ} {S : Sig Δ} {γ : IndAlg S}
      → (δx : Spine (Δ ▷ Data S γ))
      → repr-total {γ = γ} δx ≡ map-last {Δ = Δ} ((λ δ x → coe-Tm (Repr-Data δ) (repr x))) δx
    
    unrepr-total-def : ∀ {Δ} {S : Sig Δ} {γ : IndAlg S}
      → (δx : Spine (Δ ▷ dEls (γ .Carrier)))
      → unrepr-total {γ = γ} δx ≡ map-last {Δ = Δ} (λ δ x → unrepr (coe-Tm (sym (Repr-Data δ)) x)) δx

    unrepr-total-repr-total : ∀ {Δ} {S : Sig Δ} {γ : IndAlg S} (δx : Spine (Δ ▷ Data S γ))
      → unrepr-total {Δ = Δ} (repr-total {Δ = Δ} δx) ≡ δx

  repr-input : ∀ {Δ} {O : Op Δ} {S} {γ : IndAlg S} → (v : Spine (input O (Data S γ)))
    → Spine (input O (dEls (γ .Carrier)))
  repr-input v = input-map (λ δ → λ x → coe-Tm (Repr-Data δ) (repr x)) v 
  
  El-apps-output-input-id : ∀ Δ (O : Op Δ) {S} (γ : IndAlg S) (o : O ∈ S) (v : Spine (input O (Data S γ)))
    → El (apps (γ .Carrier) (output (repr-input v))) ≡ El (apps (γ .Carrier) (output v))
  El-apps-output-input-id Δ O γ o v = cong (λ δ → El (apps {Δ = Δ} (γ .Carrier) δ)) (output-input-id _ v)
  
  unrepr-fam : ∀ {Δ} {S : Sig Δ} {γ : IndAlg S}
    → (Spine (Δ ▷ Data S γ) → Ty)
    → (Spine (Δ ▷ dEls (γ .Carrier)) → Ty)
  unrepr-fam {Δ} M δx = M (unrepr-total {Δ = Δ} δx)

  -- </Helpers>

  field
    -- Representing a constructor gives back the constructor (only propositionally otherwise
    -- this rule forms a critical pair with Data-β)
    repr-ctor : ∀ {Δ} {O : Op Δ} {S} {γ : IndAlg S} → (o : O ∈ S) → (v : Spine (input O (Data S γ)))
      → Tm (Id
        (repr (ctor o v))
          (coe-Tm (trans (El-apps-output-input-id Δ O γ o v) (sym (Repr-Data _)))
        (apps (at o (γ .algebra)) (repr-input v))))
      
  -- <Helpers>
    repr-disp-alg : ∀ {Δ} {S : Sig Δ} {γ : IndAlg S} (M : Spine (Δ ▷ Data S γ) → Ty)
      → (β : Spine (disp-alg (ctors S γ) M))
      → Spine (disp-alg (ctors S γ) (dRepr M))
    
    repr-disp-alg-def : ∀ {Δ} {S : Sig Δ} {γ : IndAlg S} (M : Spine (Δ ▷ Data S γ) → Ty)
      → (β : Spine (disp-alg (ctors S γ) M))
      → repr-disp-alg {γ = γ} M β ≡ disp-alg-map (λ δ → repr) (λ δ → unrepr) β
      
    unrepr-disp-alg : ∀ {Δ} {S : Sig Δ} {γ : IndAlg S} (M : Spine (Δ ▷ Data S γ) → Ty)
      → (β : Spine (disp-alg (ctors S γ) (dRepr M)))
      → Spine (disp-alg (ctors S γ) M)
    
    unrepr-disp-alg-def : ∀ {Δ} {S : Sig Δ} {γ : IndAlg S} (M : Spine (Δ ▷ Data S γ) → Ty)
      → (β : Spine (disp-alg (ctors S γ) (dRepr M)))
      → unrepr-disp-alg {γ = γ} M β ≡ disp-alg-map (λ δ → unrepr) (λ δ → repr) β
  -- </Helpers>
        
    -- Eliminators commute with repr/unrepr
    repr-elim : ∀ {Δ} {S : Sig Δ} {γ} → (M : Spine (Δ ▷ Data S γ) → Ty)
      → (β : Spine (disp-alg (ctors S γ) M))
      → (δx : Spine (Δ ▷ Data S γ))
      → repr (elim {γ = γ} M β δx) ≡ elim {γ = γ} (dRepr M) (repr-disp-alg {γ = γ} M β) δx
    unrepr-elim : ∀ {Δ} {S : Sig Δ} {γ} → (M : Spine (Δ ▷ Data S γ) → Ty)
      → (β : Spine (disp-alg (ctors S γ) (dRepr M)))
      → (δx : Spine (Δ ▷ Data S γ))
      → unrepr (elim {γ = γ} (dRepr M) β δx) ≡ elim {γ = γ} M (unrepr-disp-alg {γ = γ} M β) δx
      
    -- Here we could also postulate the equivalence of eliminating with elim vs γ.induction