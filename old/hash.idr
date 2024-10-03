module Hash

import Data.List
import Data.Nat
import Data.Vect

-- Defining Stage as a simple Enum type
data Stage = Syntax | Pre | Run

-- Using mutual blocks in Idris to define interdependent types
mutual
  -- Definitions for signatures and contexts
  data Sig = EmptySig
           | ConsSig Sig Item

  data Ctx : Sig -> Type where
    EmptyCtx : Ctx EmptySig
    ExtCtx : (Σ : Sig) -> Ty Σ -> Ctx Σ -> Ctx (ConsSig Σ _)

  -- Definition for Items in a signature
  data Item : Sig -> Type where
    DataItem : (Σ : Sig) -> (D : Ty EmptySig) -> List (Ty (ConsSig EmptySig D)) -> Item Σ
    DefItem : (Σ : Sig) -> (Γ : Ctx Σ) -> Ty Γ -> Item Σ
    SigItem : (Σ : Sig) -> (Γ : Ctx Σ) -> Ty Γ -> Item Σ

  -- Type Ty depends on a context within a signature
  data Ty : {Σ : Sig} -> Ctx Σ -> Type

-- The Ty data type can further be fleshed out based on specific requirements
