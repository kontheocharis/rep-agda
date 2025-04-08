module Translation where

open import Agda.Builtin.Nat using (Nat; suc; zero)
open import Data.Fin.Base using (Fin; suc; zero)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Data.Product.Base using (_,_) renaming (Σ to Pair)

import MLTT as M
import DataTT as D

R-Ty : D.Ty → M.Ty
R-Tm : ∀ {A} → D.Tm A → M.Tm (R-Ty A)

R-Ty D.U = M.U
R-Ty (D.El A) = M.El (R-Tm A)
R-Ty (D.⊤) = M.⊤
R-Ty (D.Π A B) = M.Π (R-Ty A) (λ a → R-Ty (B a))
