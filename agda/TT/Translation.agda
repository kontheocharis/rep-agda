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
    
open TT
open U-structure
open Π-structure
open Σ-structure
open Id-structure
open ⊤-structure
open Data-structure
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
R M .T-U = M .T-U
R M .T-Π = M .T-Π
R M .T-Σ = M .T-Σ
R M .T-Id = M .T-Id
R M .T-⊤ = M .T-⊤

-- Need to translate Data and Repr structures
R M .T-Data .Data = {!   !}
R M .T-Data .ctor = {!   !}
R M .T-Data .elim = {!   !}
R M .T-Data .Data-β = {!   !}
R M .T-R .Repr = {!   !}
R M .T-R .repr = {!   !}
R M .T-R .unrepr = {!   !}
R M .T-R .Repr-η-1 = {!   !}
R M .T-R .Repr-η-2 = {!   !}
R M .T-RΠ .Repr-Π = {!   !}
R M .T-RΠ .repr-lam = {!   !}
R M .T-RΠ .unrepr-lam = {!   !}
R M .T-RΠ .repr-app = {!   !}
R M .T-RΠ .unrepr-app = {!   !}
R M .T-RΣ .Repr-Σ = {!   !}
R M .T-RΣ .repr-fst = {!   !}
R M .T-RΣ .unrepr-fst = {!   !}
R M .T-RΣ .repr-snd = {!   !}
R M .T-RΣ .unrepr-snd = {!   !}
R M .T-RΣ .repr-pair = {!   !}
R M .T-RΣ .unrepr-pair = {!   !}
R M .T-R⊤ .Repr-⊤ = {!   !}
R M .T-R⊤ .repr-tt = {!   !}
R M .T-R⊤ .unrepr-tt = {!   !}
R M .T-RId .Repr-Id = {!   !}
R M .T-RId .repr-rfl = {!   !}
R M .T-RId .unrepr-rfl = {!   !}
R M .T-RId .repr-J = {!   !}
R M .T-RId .unrepr-J = {!   !}

