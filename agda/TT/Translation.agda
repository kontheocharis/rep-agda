{-# OPTIONS --prop #-}
module TT.Translation where

open import Utils
open import TT.Core
open import TT.Tel
open import TT.Base
open import TT.Data
open import TT.Repr
open import TT.Sig
open import TT.Theories

open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; subst)
    
open TT
open U-structure
open Π-structure
open Σ-structure
open Id-structure
open ⊤-structure
open Data-structure
open MLTT-structure
open Tel-construction
open Sig-construction
open Repr-structure
open Repr-compat-Π
open Repr-compat-Σ
open Repr-compat-⊤
open Repr-compat-Id

open MLTT
open DataTT

-- Given a model of MLTT, we can construct a model of DataTT. This gives us a
-- map from the syntax of DataTT to the syntax of MLTT, by the universal
-- property of the syntax of DataTT, applied to the syntax of MLTT.

R : MLTT → DataTT

-- Base structure is the same
R M .T = M .T
R M .T-MLTT = M .T-MLTT

-- Need to translate Data and Repr structures

-- Data is translated by the provided inductive algebras
R M .T-Data .Data S γ δ =
  let alg-carrier = _-X:_ (M .T-MLTT) S γ in
   M .T-MLTT .T-U .El (apps (M .T-MLTT .T-Π) alg-carrier δ)
R M .T-Data .ctor {S = S} {γ = γ} o v =
  let alg-element-for-o = at (M .T-MLTT) o (_-α:_ (M .T-MLTT) S γ) in
  (apps (M .T-MLTT .T-Π) alg-element-for-o v)
R M .T-Data .elim {S = S} {γ = γ} P β δx = 
  let alg-induction = _-κ:_ (M .T-MLTT) S γ in
  let code-P = lams (M .T-MLTT .T-Π) (λ δx → (M .T-MLTT .T-U .code) (P δx)) in
  let induction-on-P = M .T-MLTT .T-Π .app alg-induction code-P in
  let section = apps (M .T-MLTT .T-Π) {!   !} {!   !} in
  {!   !}
R M .T-Data .Data-β = {!   !}

-- TODO: repr on data

-- Repr is translated away
R M .T-R .Repr A = A
R M .T-R .repr t = t
R M .T-R .unrepr t = t
R M .T-R .Repr-η-1 = refl
R M .T-R .Repr-η-2 = refl
R M .T-RΠ .Repr-Π = refl
R M .T-RΠ .repr-lam = refl
R M .T-RΠ .unrepr-lam = refl
R M .T-RΠ .repr-app = refl
R M .T-RΠ .unrepr-app = refl
R M .T-RΣ .Repr-Σ = refl
R M .T-RΣ .repr-fst = refl
R M .T-RΣ .unrepr-fst = refl
R M .T-RΣ .repr-snd = refl
R M .T-RΣ .unrepr-snd = refl
R M .T-RΣ .repr-pair = refl
R M .T-RΣ .unrepr-pair = refl
R M .T-R⊤ .Repr-⊤ = refl
R M .T-R⊤ .repr-tt = refl
R M .T-R⊤ .unrepr-tt = refl
R M .T-RId .Repr-Id = refl
R M .T-RId .repr-rfl = refl
R M .T-RId .unrepr-rfl = refl
R M .T-RId .repr-J = refl
R M .T-RId .unrepr-J = refl

