{-# OPTIONS --prop #-}
module TT.Theories where

open import Utils
open import TT.Core
open import TT.Tel
open import TT.Base
open import TT.Data
open import TT.Repr
open import TT.Sig

-- The type of extensional MLTT models
record MLTT-Ext : Set1 where
  open MLTT-structure
  field
    T : TT
    T-MLTT : MLTT-structure T
    T-Id-ext : Id-extensional T (T-MLTT .T-Id)

  open MLTT-structure T-MLTT public
  open Id-extensional T-Id-ext public
  open TT T public
    
module _ where
  open MLTT-Ext

  postulate
    -- Syntax of MLTT and a recursor.
    --
    -- Agda cannot define syntax for second order theories natively.
    MLTT-Ext-syntax : MLTT-Ext
    MLTT-Ext-rec : (d : MLTT-Ext) → T MLTT-Ext-syntax ~> T d
  
  -- We could postulate additionally the computation rules for the recursor. 
  -- Also, we could postulate the preservation of all the structure of the syntax.
  -- This is not needed for our purposes.
    
-- The type of DataTT models
record DataTT : Set1 where
  field
    T : TT
    T-MLTT : MLTT-structure T
    T-Data : Data-structure T T-MLTT

  open MLTT-structure T-MLTT

  field
    T-R : Repr-structure T
    T-RΠ : Repr-compat-Π T T-R T-Π
    T-RΣ : Repr-compat-Σ T T-R T-Σ
    T-R⊤ : Repr-compat-⊤ T T-R T-⊤
    T-RId : Repr-compat-Id T T-R T-Id
    

module _ where
  open DataTT
  postulate
    -- Syntax of dataTT and a recursor.
    DataTT-syntax : DataTT
    DataTT-rec : (d : DataTT) → T DataTT-syntax ~> T d