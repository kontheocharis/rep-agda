module MLTTPar where

open import Agda.Builtin.Nat using (Nat; suc; zero)
open import Data.Fin.Base using (Fin; suc; zero)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

VarType = @+ Set -> Set

module PHOAS (Var : VarType) where

  data Ty : Set

  data Tm : Ty → Set

  data Tel : Set
  
  data Spine : Tel → Set

  variable
    Any : Set _
    A A' A'' : Ty
    B B' : Var _ → Ty
    t t' u u' : Tm _
    v v' w w' : Var _ → Tm _
    Δ Δ' : Tel
    δ δ' α β : Spine _
  
  <<_>> : Ty → Tel
  <_> : Tm A → Spine << A >>
    
  -- data Ty≈ : Ty → Ty → Set
    
  -- data Tm≈ : (T : Ty≈ A A') → Tm A → Tm A' → Set

  -- variable
  --   A≈ A≈' : Ty≈ _ _
  --   B≈ B≈' : Tm≈ _ _ _ → Ty≈ _ _
  --   t≈ t≈' u≈ u≈' : Tm≈ _ _ _
  --   v≈ v≈' w≈ w≈' : Tm≈ _ _ _ → Tm≈ _ _ _

  data Ty where
    _[_] : (Var Δ → Ty) → Spine Δ → Ty

    U : Ty
    El : Tm U → Ty
    ⊤ : Ty
    Π : (A : Ty) → (Var << A >> → Ty) → Ty
    Σ : (A : Ty) → (Var << A >> → Ty) → Ty
    Id : {A : Ty} → Tm A → Tm A → Ty

  
  data Tel where
    _[_] : (Var Δ → Tel) → Spine Δ → Tel
    ∙ : Tel
    ext : (A : Ty) → (Var A → Tel) → Tel

  syntax ext A (λ a → Δ) = a ∶ A , Δ

  data Spine where
    [] : Spine ∙
    _,_ : ∀ {A} {Δ : Var A → Spine Δ} → (a : Tm A) → Spine ({!   !}) → Spine {!   !}

  syntax Π A (λ x → B) = [ x ∶ A ] ⇒ B
  syntax Σ A (λ x → B) = [ x ∶ A ] × B

  data Tm where
    _[_] : ∀ {Δ} → (Var Δ → Tm A') → Spine Δ → Tm A'
    var : Var A → Tm A

    lam : ((a : Var << A >>) → Tm (B a)) → Tm (Π A B)
    app : Tm (Π A B) → (a : Tm A) → Tm (B [ < a > ])
    pair : (a : Tm A) → Tm (B [ < a > ]) → Tm (Σ A B)
    tt : Tm ⊤
    fst : Tm (Σ A B) → Tm A
    snd : (p : Tm (Σ A B)) → Tm (B [ < fst p > ])
    refl : {a : Tm A} → Tm (Id a a)
    -- J : (P : Var (a ∶ A , b ∶ A , p ∶ Id (var a) (var b) , ∙) → Ty) → {!   !}
      -- → ((a : Var A) → Tm (P [ var a , var a , refl , ∙ ]))
      -- → {a : Tm A} → {b : Tm A} → (p : Tm (Id a b)) → Tm (P a b [ p ])
  
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