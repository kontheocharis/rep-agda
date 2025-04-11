{-# OPTIONS --prop #-}
module TT.Theories where

open import Utils
open import TT.Core
open import TT.Tel
open import TT.Base
open import TT.Data
open import TT.Repr
open import TT.Sig

-- The type of MLTT models
record MLTT : Set1 where
  field
    {{T}} : TT
    {{T-U}} : U-structure T
    {{T-Π}} : Π-structure T
    {{T-Σ}} : Σ-structure T
    {{T-Id}} : Id-structure T
    {{T-⊤}} : ⊤-structure T
    
-- The type of DataTT models
record DataTT : Set1 where
  field
    {{M}} : MLTT

  T = MLTT.T M

  field
    {{T-Data}} : Data-structure T
    {{T-R}} : Repr-structure T
    {{T-RΠ}} : Repr-compat-Π T
    {{T-RΣ}} : Repr-compat-Σ T
    

-- Given a model of MLTT, we can construct a model of DataTT, by the recursor of
-- the initial model of DataTT applied to the initial model of DataTT. This
-- gives us a map from the syntax of DataTT to the syntax of MLTT.
