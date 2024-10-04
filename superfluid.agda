module Superfluid where

open import Agda.Builtin.Unit
open import Agda.Builtin.Equality
open import Data.Product using (_×_; _,_; Σ)
open import Agda.Builtin.Sigma using (fst; snd)
open import Function.Base using (_∘_)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc; _+_; _<?_; _≥_; s≤s⁻¹)
open import Data.Nat.Properties using (≰⇒>)
open import Data.Fin using (Fin; zero; suc; toℕ; fromℕ; fromℕ<; splitAt)
open import Relation.Nullary using (yes; no)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.String using (String)

-- Used for global symbols
data Name : Set where
  name : String -> Name

-- All the syntactic categories
data Sig : Set
data Ctx : Sig -> Set
data Item : Sig -> Set
data Ty : {Σ : Sig} -> Ctx Σ -> Set
data Tel : {Σ : Sig} -> Ctx Σ -> Set
data Tm : {Σ : Sig} -> (Γ : Ctx Σ) -> Ty Γ -> Set

-- Signatures and contexts

data Sig where
  ∅ : Sig
  _,_ : (Σ : Sig) -> Item Σ -> Sig

data Ctx where
  ∅ : {Σ : Sig} -> Ctx Σ
  _,_ : {Σ : Sig} -> (Γ : Ctx Σ) -> Ty Γ -> Ctx Σ

_++_ : ∀ {Σ} -> (Γ : Ctx Σ) -> Tel Γ -> Ctx Σ

data Tel where
  ∅ : ∀ {Σ} {Γ : Ctx Σ} -> Tel Γ
  _,_ : ∀ {Σ} {Γ : Ctx Σ} -> (Δ : Tel Γ) -> Ty (Γ ++ Δ) -> Tel Γ

Γ ++ ∅ = ∅
Γ ++ (Δ , A) = Γ ++ Δ , A

_Tel++_ : ∀ {Σ} {Γ : Ctx Σ} {A : Tel Γ} -> (A : Tel Γ) -> Tel (Γ ++ A) -> Tel Γ

data Tms {Σ} (Γ : Ctx Σ) :  Tel Γ -> Set where
  ∅ : Tms Γ ∅
  _,_ : ∀ {Δ : Tel Γ} {T : Ty (Γ ++ Δ)} -> (ts : Tms Γ Δ) -> (t : Tm (Γ ++ Δ) T) -> Tms Γ (Δ , T)

record Dat (Σ : Sig) : Set where
  inductive
  constructor dat-item
  field
    F : Name
    Δₚ : Tel {Σ} ∅
    Δᵢ : Tel (∅ ++ Δₚ)

data Ctors {Σ : Sig} (D : Dat Σ) : Set

data ItemIn : (Σ : Sig) -> Item Σ -> Set

data Item where
  dat : ∀ {Σ} -> Dat Σ -> Item Σ
  ctors : ∀ {Σ} {D : Dat Σ} -> Ctors D -> Item (Σ , dat D)
  def : ∀ {Σ} -> (f : Name) -> (T : Ty {Σ} ∅) -> (t : Tm ∅ T) -> Item Σ

record Ctor {Σ : Sig} (D : Dat Σ) (cs : Ctors D) : Set

data Ctors {Σ} D where
  ∅ : Ctors D
  _,_ : (cs : Ctors D) -> (c : Ctor D cs) -> Ctors D

^Ctx : ∀ {Σ I} -> Ctx Σ -> Ctx (Σ , I)
^Ty : ∀ {Σ I} {Γ : Ctx Σ} -> Ty Γ -> Ty (^Ctx {Σ} {I} Γ)

^Ctx ∅ = ∅
^Ctx (Γ , A) = (^Ctx Γ) , (^Ty A)

~Ty : ∀ {Σ} {Γ : Ctx Σ} {A : Ty Γ} -> Ty Γ -> Ty (Γ , A)

~Tel : ∀ {Σ} {Γ : Ctx Σ} {A : Ty Γ} -> Tel Γ -> Tel (Γ , A)

^Item : ∀ {Σ} {J : Item Σ} -> Item Σ -> Item (Σ , J)

^Tel : ∀ {Σ I} {Γ : Ctx Σ} -> Tel {Σ} Γ -> Tel {Σ , I} (^Ctx Γ)

~~Ty : ∀ {Σ} {Γ : Ctx Σ} {A : Tel Γ} -> Ty Γ -> Ty (Γ ++ A)

~~Tel : ∀ {Σ} {Γ : Ctx Σ} {A : Tel Γ} -> Tel Γ -> Tel (Γ ++ A)

hoist-tel : ∀ {Σ} {Γ : Ctx Σ} -> Tel {Σ} ∅ -> Tel Γ

hoist-tel' : ∀ {Σ} {Γ : Ctx Σ} {A : Tel {Σ} ∅} -> Tel (∅ ++ A) -> Tel (Γ ++ hoist-tel A)

_Ty[_] : ∀ {Σ} {Γ : Ctx Σ} {A : Ty Γ} -> Ty (Γ , A) -> Tm Γ A -> Ty Γ

_Ty⟦_⟧ : ∀ {Σ} {Γ : Ctx Σ} {A : Tel Γ} -> Ty (Γ ++ A) -> Tms Γ A -> Ty Γ

_Tel[_] : ∀ {Σ} {Γ : Ctx Σ} {A : Tel Γ} -> Tel (Γ ++ A) -> Tms Γ A -> Tel Γ

_Tel⟦_⟧ : ∀ {Σ} {Γ : Ctx Σ} {A : Tel Γ} -> Tel (Γ ++ A) -> Tms Γ A -> Tel Γ

_Tm⟦_⟧ : ∀ {Σ} {Γ : Ctx Σ} {A : Tel Γ} {B : Ty (Γ ++ A)} -> Tm (Γ ++ A) B -> (a : Tms Γ A) -> Tm Γ (B Ty⟦ a ⟧)

_Tms[_] : ∀ {Σ} {Γ : Ctx Σ} {A : Tel Γ} {B : Tel (Γ ++ A)} -> Tms (Γ ++ A) B -> (a : Tms Γ A) -> Tms Γ (B Tel[ a ])

data ItemIn where
  here : ∀ {Σ}  -> (I : Item Σ) -> ItemIn (Σ , I) (^Item I)
  there : ∀ {Σ} {I J : Item Σ} -> (N : ItemIn Σ I) -> ItemIn (Σ , J) (^Item I)

record Ctor {Σ} D cs where
  inductive
  constructor ctor-item
  field
    k : Name
    Δₖ : {Γ : Ctx Σ} -> Tms Γ (hoist-tel (Dat.Δₚ D)) -> Tel Γ
    iₖ : {Γ : Ctx Σ} -> (pp : Tms Γ (hoist-tel (Dat.Δₚ D))) -> Tms (Γ ++ Δₖ pp) (hoist-tel ((Dat.Δᵢ D) Tel⟦ pp ⟧))

-- Locating items in contexts

data CtorIn {Σ : Sig} {D : Dat Σ} : (cs : Ctors D) -> Ctor D cs -> Set
  -- here : ∀ {Σ} {D : Dat Σ} {cs : Ctors D} -> (c : Ctor D cs) -> CtorIn (cs , c)

Πs : ∀ {Σ} {Γ : Ctx Σ} -> (A : Tel Γ) -> Ty (Γ ++ A) -> Ty Γ

apps : ∀ {Σ : Sig} {Γ : Ctx Σ} {A : Tel Γ} {B : Ty (Γ ++ A)} -> Tm Γ (Πs A B) -> Tm (Γ ++ A) B

data Var : ∀ {Σ} -> (Γ : Ctx Σ) -> Ty Γ -> Set where
  z : ∀ {Σ} {Γ : Ctx Σ} {A : Ty Γ} -> Var Γ A
  s : ∀ {Σ} {Γ : Ctx Σ} {A B : Ty Γ} -> Var Γ A -> Var (Γ , B) (~Ty A)

data Ty where
  Π : ∀ {Σ : Sig} {Γ : Ctx Σ} -> (A : Ty Γ) -> (B : Ty (Γ , A)) -> Ty Γ
  U : ∀ {Σ : Sig} {Γ : Ctx Σ} -> Ty Γ
  El : ∀ {Σ : Sig} {Γ : Ctx Σ} -> Tm {Σ} Γ U -> Ty Γ

~~Ty U = U

U Ty⟦ _ ⟧ = U

data Tm where
  lam : ∀ {Σ : Sig} {Γ : Ctx Σ} {A : Ty Γ} {B : Ty (Γ , A)} -> Tm (Γ , A) B -> Tm Γ (Π A B)
  app : ∀ {Σ : Sig} {Γ : Ctx Σ} {A : Ty Γ} {B : Ty (Γ , A)} -> Tm Γ (Π A B) -> Tm (Γ , A) B
  var : ∀ {Σ : Sig} {Γ : Ctx Σ} {T : Ty Γ} -> (x : Var Γ T) -> Tm Γ T
  ^_ : ∀ {Σ : Sig} {Γ : Ctx Σ} -> Ty Γ -> Tm Γ U
  -- dat : ∀ {Σ} {Γ : Ctx Σ} {D : Dat Σ} -> ItemIn Σ (dat D) -> Tms Γ (hoist-tel (Dat.Δₚ D)) -> Tm Γ U
  dat : ∀ {Σ} {Γ : Ctx Σ} {D : Dat Σ} -> ItemIn Σ (dat D) -> Tm Γ (Πs (hoist-tel (Dat.Δₚ D)) (Πs (hoist-tel' (Dat.Δᵢ D)) U))
  -- ctor : ∀ {Σ : Sig} {Γ : Ctx Σ} {A : Ty Γ} {D : Dat Σ} {cs : Ctors D} {c : Ctor D cs}
  --   -> (D' : ItemIn Σ (dat D)) -> CtorIn cs c
  --   -> (pp : Tms Γ (hoist-tel (Dat.Δₚ D)))
  --   -> (sp : Tms Γ ((hoist-tel' (Ctor.Δₖ c)) Tel[ pp ]))
  --   -> Tm Γ (El (dat D' pp))
  ctor : ∀ {Σ : Sig} {Γ : Ctx Σ} {A : Ty Γ} {D : Dat Σ} {cs : Ctors D} {c : Ctor D cs}
    -> (D' : ItemIn Σ (dat D)) -> CtorIn cs c
    -> (pp : Tms Γ (hoist-tel (Dat.Δₚ D)))
    -> Tm Γ (Πs ((hoist-tel' (Ctor.Δₖ c)) Tel⟦ pp ⟧) (El ((apps ((apps (dat D')) Tm⟦ pp ⟧ )) Tm⟦ ? ⟧)))
    -- -> Tm Γ (Πs (hoist-tel (Dat.Δₚ D)) (Πs ((hoist-tel' (Ctor.Δₖ c)) (El (dat D' pp))))
