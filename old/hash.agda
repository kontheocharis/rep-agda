module Hash where

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


data Stage : Set where
  synax : Stage
  pre : Stage
  run : Stage

data ItemKind : Set where
  dat : ItemKind
  def : ItemKind
  ctor : ItemKind
  sig : ItemKind

mutual
  data Sig : Set
  data Ctx : Sig -> Set

  data Ty : ∀ {Σ} -> Ctx Σ -> Set
  data Item : Sig -> ItemKind -> Set

  data Sig where
    ∅ : Sig
    _/_ : (Σ : Sig) -> ∀ {k} -> Item Σ k -> Sig

  data ItemIn : Sig -> ItemKind -> Set where
    here : ∀ {Σ k} -> (I : Item Σ k) -> ItemIn (Σ / I) k
    there : ∀ {Σ k k'} -> (I : ItemIn Σ k) -> (J : Item Σ k') -> ItemIn (Σ / J) k

  ⟨_⟩ : ∀ {Σ k} -> ItemIn Σ k -> Item Σ k
  ⟨ here I ⟩ = {!   !}
  ⟨ there I J ⟩ = {!   !}

  data Ctx where
    ∅ : {Σ : Sig} -> Ctx Σ
    _,_ : (Σ : Sig) -> (Γ : Ctx Σ) -> Ty Γ -> Ctx Σ

  data Tel : ∀ {Σ} -> Ctx Σ -> Set

  _++_ : ∀ {Σ} -> (Γ : Ctx Σ) -> Tel Γ -> Ctx Σ
  Γ ++ e = {!   !}

  data Tel where
    ε : ∀ {Σ} {Γ : Ctx Σ} -> Tel Γ
    _,,_ : ∀ {Σ} {Γ : Ctx Σ} -> (Δ : Tel Γ) -> Ty (Γ ++ Δ) -> Tel Γ

  -- Γ ++ (Δ ,, A) = (Γ , )
  data Name : Set

  dat-ty : ∀ {Σ} -> ItemIn Σ dat -> Ty {Σ} ∅

  data Item where
    dat-item : (Σ : Sig) -> (name : Name) -> (P : Tel {Σ} ∅) -> Item Σ dat
    ctor-item : (Σ : Sig) -> (D : ItemIn Σ dat) -> (name : Name) -> (C : Tel {Σ / ⟨ D ⟩} (dat-ty D)) -> Item Σ ctor
    def-item : (Σ : Sig) -> (Γ : Ctx Σ) -> Ty Γ -> Item Σ def

    -- def-item : (Σ : Sig) -> (Γ : Ctx Σ) -> Ty Γ -> Item Σ
    -- sig-item : (Σ : Sig) -> (Γ : Ctx Σ) -> Ty Γ -> Item Σ




