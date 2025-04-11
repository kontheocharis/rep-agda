{-# OPTIONS --prop #-}
module TT.Lemmas where

open import Utils
open import TT.Core
open import TT.Tel
open import TT.Base
open import TT.Data
open import TT.Repr
open import TT.Sig
open import TT.Theories

open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; subst; cong; cong₂; trans; sym)


module El-apps-lams-code (T : TT) (T-Π : Π-structure T) (T-U : U-structure T) where
  open Tel-construction T
  open TT T
  open U-structure T-U
  open Π-structure T-Π

  El-apps-lams-code : ∀ {Δ : Tel} {P : Spine Δ → Ty} (δ : Spine Δ) → El (apps (lams (λ δ → code (P δ))) δ) ≡ P δ
  El-apps-lams-code {P = P} δ = trans (cong (λ t → El t) (Πs-β {f = λ δx → code (P δx)})) U-η-1