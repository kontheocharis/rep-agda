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

-- Telescope extension
_++_ : ∀ {Σ} -> (Γ : Ctx Σ) -> Tel Γ -> Ctx Σ

-- Non-dependent context extension
_*_ : ∀ {Σ} -> Ctx Σ -> Ctx Σ -> Ctx Σ

-- Telescopes
data Tel where
  ∅ : ∀ {Σ} {Γ : Ctx Σ} -> Tel Γ
  _,_ : ∀ {Σ} {Γ : Ctx Σ} -> (Δ : Tel Γ) -> Ty (Γ ++ Δ) -> Tel Γ

-- Weakening for all syntactic categories
sig^ctx : ∀ {Σ} {I : Item Σ} -> Ctx Σ -> Ctx (Σ , I)
sig^ty : ∀ {Σ} {I : Item Σ} {Γ : Ctx Σ} -> Ty Γ -> Ty (sig^ctx {I = I} Γ)
sig^item : ∀ {Σ} {I : Item Σ} -> Item Σ -> Item (Σ , I)
sig^tel : ∀ {Σ} {I : Item Σ} {Γ : Ctx Σ} -> Tel {Σ} Γ -> Tel {Σ , I} (sig^ctx {I = I} Γ)

^*tel : ∀ {Σ} {Γ : Ctx Σ} {Γ' : Ctx Σ} -> Tel Γ -> Tel (Γ * Γ')
^ty* : ∀ {Σ} {Γ : Ctx Σ} {Γ' : Ctx Σ} -> Ty Γ -> Ty (Γ * Γ')
^*ty : ∀ {Σ} {Γ : Ctx Σ} {Γ' : Ctx Σ} -> Ty Γ -> Ty (Γ' * Γ)

^tm* : ∀ {Σ} {Γ : Ctx Σ} {Γ' : Ctx Σ} {T : Ty Γ} -> Tm Γ T -> Tm (Γ * Γ') (^ty* T)

-- Now we can define some operations on contexts and telescopes
Γ * ∅ = Γ
Γ * (Δ , A) = (Γ * Δ) , ^*ty A

Γ ++ ∅ = ∅
Γ ++ (Δ , A) = Γ ++ Δ , A

-- Tms is Tm what Tel is to Ty
data Tms {Σ} (Γ : Ctx Σ) :  Tel Γ -> Set where
  ∅ : Tms Γ ∅
  _,_ : ∀ {Δ : Tel Γ} {T : Ty (Γ ++ Δ)} -> (ts : Tms Γ Δ) -> (t : Tm (Γ ++ Δ) T) -> Tms Γ (Δ , T)

-- Information for a data type
record Dat (Σ : Sig) : Set where
  inductive
  constructor dat-item
  field
    F : Name
    Δₚ : Tel {Σ} ∅
    Δᵢ : Tel (∅ ++ Δₚ)

-- Defining constructors, item
data Ctors {Σ : Sig} (D : Dat Σ) : Set
data ItemIn : (Σ : Sig) -> Item Σ -> Set
record Ctor {Σ : Sig} (D : Dat Σ) (cs : Ctors D) : Set

data Item where
  dat : ∀ {Σ} -> Dat Σ -> Item Σ
  ctors : ∀ {Σ} {D : Dat Σ} -> Ctors D -> Item (Σ , dat D)
  def : ∀ {Σ} -> (f : Name) -> (T : Ty {Σ} ∅) -> (t : Tm ∅ T) -> Item Σ

data Ctors {Σ} D where
  ∅ : Ctors D

  _,_ : (cs : Ctors D) -> (c : Ctor D cs) -> Ctors D

sig^ctx ∅ = ∅
sig^ctx (Γ , A) = (sig^ctx Γ) , (sig^ty A)


-- ~~Ty : ∀ {Σ} {Γ : Ctx Σ} {A : Tel Γ} -> Ty Γ -> Ty (Γ ++ A)

-- ~~Tel : ∀ {Σ} {Γ : Ctx Σ} {A : Tel Γ} -> Tel Γ -> Tel (Γ ++ A)

-- hoist-ty : ∀ {Σ} {Γ : Ctx Σ} -> Ty {Σ} ∅ -> Ty Γ

-- hoist-ty' : ∀ {Σ} {Γ : Ctx Σ} {A : Tel {Σ} ∅} -> Ty {Σ} (∅ ++ A) -> Ty Γ

↑tel : ∀ {Σ} {Γ : Ctx Σ} -> Tel {Σ} ∅ -> Tel Γ
↑tel {Γ = ∅} Δ = Δ

↑²tel : ∀ {Σ} {Γ : Ctx Σ} {A : Tel {Σ} ∅} -> Tel (∅ ++ A) -> Tel (Γ ++ ↑tel A)
↑²tel {Γ = ∅} Δ = Δ

record CanSubst
  {ETy : ∀ {Σ} -> Ctx Σ -> Set}
  {ETm : ∀ {Σ} (Γ : Ctx Σ) -> ETy Γ -> Set}
  {ext : ∀ {Σ} (Γ : Ctx Σ) -> ETy Γ -> Ctx Σ}
  (RTy : ∀ {Σ} -> Ctx Σ -> Set) : Set where
  constructor can-subst
  field
    _[_] : ∀ {Σ} {Γ : Ctx Σ} {A : ETy Γ} -> RTy (ext Γ A) -> ETm Γ A -> RTy Γ
    ^_ : ∀ {Σ} {Γ : Ctx Σ} {A : ETy Γ} -> RTy Γ -> RTy (ext Γ A)

    ↑_ : ∀ {Σ} {Γ : Ctx Σ} {A : ETy Γ} -> RTy ∅ -> RTy Γ

    ↑²++_ : ∀ {Σ} {Γ : Ctx Σ} {A : ETy Γ} -> RTy (ext ∅ A) -> RTy (ext Γ (↑ A))

open CanSubst {{...}} public

instance
  ty-can-subst-ty : CanSubst {ETy = Ty} {ETm = Tm} {ext = _,_} Ty
  tel-can-subst-ty : CanSubst {ETy = Ty} {ETm = Tm} {ext = _,_} Tel
  ty-can-subst-tel : CanSubst {ETy = Tel} {ETm = Tms} {ext = _++_} Ty
  tel-can-subst-tel : CanSubst {ETy = Tel} {ETm = Tms} {ext = _++_} Tel

record CanSubstDisp
  {ETy : ∀ {Σ} -> Ctx Σ -> Set}
  {ETm : ∀ {Σ} (Γ : Ctx Σ) -> ETy Γ -> Set}
  {ext : ∀ {Σ} (Γ : Ctx Σ) -> ETy Γ -> Ctx Σ}
  {RTy : ∀ {Σ} -> Ctx Σ -> Set}
  {{_ : CanSubst {ETy} {ETm} {ext} RTy}}
  (RTm : ∀ {Σ} (Γ : Ctx Σ) -> RTy Γ -> Set) : Set where
  constructor can-subst-disp
  field
    _[_]ᴰ : ∀ {Σ} {Γ : Ctx Σ} {A : ETy Γ} {T : RTy (ext Γ A)}
      -> RTm (ext Γ A) T
      -> (a : ETm Γ A)
      -> RTm Γ (T [ a ])
    ^ᴰ_ : ∀ {Σ} {Γ : Ctx Σ} {A : ETy Γ} {T : RTy Γ} -> RTm Γ T -> RTm (ext Γ A) (^ T)

open CanSubstDisp {{...}} public

instance
  tm-can-subst-disp-ty : CanSubstDisp {ETy = Ty} {ETm = Tm} {ext = _,_} Tm
  tms-can-subst-disp-ty : CanSubstDisp {ETy = Ty} {ETm = Tm} {ext = _,_} Tms
  tm-can-subst-disp-tel : CanSubstDisp {ETy = Tel} {ETm = Tms} {ext = _++_} Tm
  tms-can-subst-disp-tel : CanSubstDisp {ETy = Tel} {ETm = Tms} {ext = _++_} Tms

data ItemIn where
  here : ∀ {Σ}  -> (I : Item Σ) -> ItemIn (Σ , I) (sig^item I)
  there : ∀ {Σ} {I J : Item Σ} -> (N : ItemIn Σ I) -> ItemIn (Σ , J) (sig^item I)

record Ctor {Σ} D cs where
  inductive
  constructor ctor-item
  field
    k : Name
    Δₖ : Tel (∅ ++ (Dat.Δₚ D))
    iₖ : Tms ((∅ ++ (Dat.Δₚ D)) ++ Δₖ) (^ (Dat.Δᵢ D))

-- Locating items in contexts

data CtorIn {Σ : Sig} {D : Dat Σ} : (cs : Ctors D) -> Ctor D cs -> Set
  -- here : ∀ {Σ} {D : Dat Σ} {cs : Ctors D} -> (c : Ctor D cs) -> CtorIn (cs , c)

Πs : ∀ {Σ} {Γ : Ctx Σ} -> (A : Tel Γ) -> Ty (Γ ++ A) -> Ty Γ

apps : ∀ {Σ : Sig} {Γ : Ctx Σ} {A : Tel Γ} {B : Ty (Γ ++ A)} -> Tm Γ (Πs A B) -> Tm (Γ ++ A) B

data Var : ∀ {Σ} -> (Γ : Ctx Σ) -> Ty Γ -> Set where
  z : ∀ {Σ} {Γ : Ctx Σ} {A : Ty Γ} -> Var Γ A
  s : ∀ {Σ} {Γ : Ctx Σ} {A B : Ty Γ} -> Var Γ A -> Var (Γ , B) (^ A)

weaken-ty : ∀ {Σ} {Γ : Ctx Σ} {A B : Tel Γ}
  -> Ty (Γ ++ A)
  -> Ty ((Γ ++ B) ++ (^ A))

-- Helper function to hoist a substitution
hoist-subst : ∀ {Σ} {Γ : Ctx Σ} {D : Tel {Σ} ∅} {A B : Tel (∅ ++ D)}
  -> Tms ((∅ ++ D) ++ B) (^ A)
  -> Tms ((Γ ++ ↑tel D) ++ ↑²tel B) (^ (↑²tel A))

-- -- hoist-tel'' : ∀ {Σ} {Γ : Ctx Σ} {D : Tel {Σ} ∅} {B : Tel (∅ ++ D)}
-- --   -> Tel ((∅ ++ D) ++ B)
-- --   -> Tel (((Γ ++ hoist-tel D) ++ hoist-tel' B))

-- -- -- Helper function similar to hoist-tel', but for double weakening
-- -- hoist-tel''' : ∀ {Σ} {Γ : Ctx Σ} {D : Tel {Σ} ∅} {B : Tel (∅ ++ D)} {A : Tel ((∅ ++ D) ++ B)}
-- --   -> Tel (((∅ ++ D) ++ B) ++ A)
-- --   -> Tel (((Γ ++ hoist-tel D) ++ hoist-tel' B) ++ hoist-tel'' A)


-- -- apps-weak : ∀ {Σ} {Γ : Ctx Σ} {D : Tel {Σ} ∅} {A : Tel (∅ ++ D)} {B : Tel (∅ ++ D)}
-- --   -> (T : Ty ((Γ ++ hoist-tel D) ++ hoist-tel' A))
-- --   -> (δ : Tms ((∅ ++ D) ++ B) (^ A))
-- --   -> Ty ((Γ ++ hoist-tel D) ++ hoist-tel' B)
-- -- apps-weak {Σ} {Γ} {D} {A} {B} T δ = (weaken-ty T) Ty⟦ hoist-subst δ ⟧

-- -- data Ty where
-- --   Π : ∀ {Σ : Sig} {Γ : Ctx Σ} -> (A : Ty Γ) -> (B : Ty (Γ , A)) -> Ty Γ
-- --   U : ∀ {Σ : Sig} {Γ : Ctx Σ} -> Ty Γ
-- --   El : ∀ {Σ : Sig} {Γ : Ctx Σ} -> Tm {Σ} Γ U -> Ty Γ
-- --   dat : ∀ {Σ} {Γ : Ctx Σ} {D : Dat Σ} -> ItemIn Σ (dat D) -> Ty ((Γ ++ (hoist-tel (Dat.Δₚ D))) ++ hoist-tel' (Dat.Δᵢ D))

-- -- data Tm where
-- --   lam : ∀ {Σ : Sig} {Γ : Ctx Σ} {A : Ty Γ} {B : Ty (Γ , A)} -> Tm (Γ , A) B -> Tm Γ (Π A B)
-- --   app : ∀ {Σ : Sig} {Γ : Ctx Σ} {A : Ty Γ} {B : Ty (Γ , A)} -> Tm Γ (Π A B) -> Tm (Γ , A) B
-- --   var : ∀ {Σ : Sig} {Γ : Ctx Σ} {T : Ty Γ} -> (x : Var Γ T) -> Tm Γ T
-- --   ^_ : ∀ {Σ : Sig} {Γ : Ctx Σ} -> Ty Γ -> Tm Γ U
-- --   ctor : ∀ {Σ : Sig} {Γ : Ctx Σ} {A : Ty Γ} {D : Dat Σ} {cs : Ctors D} {c : Ctor D cs}
-- --     -> (D' : ItemIn Σ (dat D)) -> CtorIn cs c
-- --     -> Tm ((Γ ++ (hoist-tel (Dat.Δₚ D))) ++ (hoist-tel' (Ctor.Δₖ c))) (apps-weak (dat D') (Ctor.iₖ c))
