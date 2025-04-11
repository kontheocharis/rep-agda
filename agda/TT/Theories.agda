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
    T : TT
    T-U : U-structure T
    T-Π : Π-structure T
    T-Σ : Σ-structure T
    T-Id : Id-structure T
    T-⊤ : ⊤-structure T
    
-- The type of DataTT models
record DataTT : Set1 where
  field
    T : TT
    T-U : U-structure T
    T-Π : Π-structure T
    T-Σ : Σ-structure T
    T-Id : Id-structure T
    T-⊤ : ⊤-structure T
    T-Data : Data-structure T T-U T-Π T-Σ T-Id T-⊤
    T-R : Repr-structure T
    T-RΠ : Repr-compat-Π T T-R T-Π
    T-RΣ : Repr-compat-Σ T T-R T-Σ
    T-R⊤ : Repr-compat-⊤ T T-R T-⊤
    T-RId : Repr-compat-Id T T-R T-Id