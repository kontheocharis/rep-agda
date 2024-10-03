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
data Ty : ∀ {Σ} -> Ctx Σ -> Set
data Tel : ∀ {Σ} -> Ctx Σ -> Set
data Tm : ∀ {Σ} {Γ : Ctx Σ} -> Ty Γ -> Set

-- Locating items in a signature
data ItemIn : Sig -> Set

-- Signatures and contexts

data Sig where
  ∅ : Sig
  _,_ : (Σ : Sig) -> Item Σ -> Sig

data Ctx where
  ∅ : {Σ : Sig} -> Ctx Σ
  _,_ : (Σ : Sig) -> (Γ : Ctx Σ) -> Ty Γ -> Ctx Σ

-- Locating items in contexts

data ItemIn where
  here : ∀ {Σ}  -> (I : Item Σ) -> ItemIn (Σ , I)
  there : ∀ {Σ} -> (I : ItemIn Σ) -> (J : Item Σ) -> ItemIn (Σ , J)

⟨_⟩ : ∀ {Σ} -> ItemIn Σ -> Item Σ
⟨ here I ⟩ = {!   !}
⟨ there I J ⟩ = {!   !}

_++_ : ∀ {Σ} -> (Γ : Ctx Σ) -> Tel Γ -> Ctx Σ
Γ ++ e = {!   !}

data Tel where
  ∅ : ∀ {Σ} {Γ : Ctx Σ} -> Tel Γ
  _,_ : ∀ {Σ} {Γ : Ctx Σ} -> (Δ : Tel Γ) -> Ty (Γ ++ Δ) -> Tel Γ

data Tms {Σ} {Γ : Ctx Σ} : Tel Γ -> Set where
  ∅ : Tms ∅
  _,_ : ∀ {Δ : Tel Γ} {T : Ty (Γ ++ Δ)} -> (ts : Tms Δ) -> (t : Tm T) -> Tms (Δ , T)

dat-ty : ∀ {Σ} -> ItemIn Σ -> Ty {Σ} ∅

record Dat (Σ : Sig) : Set where
  inductive
  constructor dat-item
  field
    F : Name
    Δₚ : Tel {Σ} ∅
    Δᵢ : Tel (∅ ++ Δₚ)

data Ctors {Σ : Sig} (D : Dat Σ) : Set

record CtorItem {Σ : Sig} (D : Dat Σ) (cs : Ctors D) : Set

data Ctors {Σ} D where
  ∅ : Ctors D
  _,_ : (cs : Ctors D) -> (c : CtorItem D cs) -> Ctors D

data Item where
  dat : ∀ {Σ} -> Dat Σ -> Item Σ
  ctors : ∀ {Σ} {D : Dat Σ} -> Ctors D -> Item (Σ , dat D)
  def : ∀ {Σ} -> (f : Name) -> (T : Ty {Σ} ∅) -> (t : Tm T) -> Item Σ

~_ : ∀ {Σ I} -> Ctx Σ -> Ctx (Σ , I)

record CtorItem {Σ} D cs where
  inductive
  constructor ctor-item
  field
    k : Name
    Δₖ : Tel {(Σ , dat D) , ctors cs} (~ ~ (∅ ++ Dat.Δₚ D))
    iₖ : Tms (Dat.Δᵢ D)

