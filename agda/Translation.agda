{-# OPTIONS --prop --rewriting #-}
module Translation where

open import Agda.Builtin.Nat using (Nat; suc; zero)
open import Data.Fin.Base using (Fin; suc; zero)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; subst; cong)
open import Data.Product.Base using (_,_) renaming (Σ to Pair)

import MLTT as M
open import DataTT


{-# BUILTIN REWRITE _≡_ #-}

-- Inductive hypothesis for second order syntax elimination. Agda (with {-#
-- NO_POSITIVITY_CHECK #-}) does not generate eliminators and instead relies on
-- dependent pattern matching. The eliminators that areconstructible
-- are the correct ones for first-order syntax, but not second order syntax.
--
-- This is because eliminators for second order syntax will take a recursive
-- constructor parameter e.g. L → L in 
--     data L : Set where lam : (L → L) → L ; app : L → L → L
--
-- The eliminator for L is basically a logical predicate
--   elim-L : ∀ {P : L → Set} →
--     → (∀ {f : L → L} → (g : ∀ {l} → P l → P (f l)) → P (lam f))
--     → (∀ {l} → P l → P l → P (app l l))
--     → ∀ {l} → P l
--
-- Agda's dependent pattern matching will not allow us to access a function
-- g : ∀ {l} → P l → P (f l) as an inductive hypothesis; all we get is
-- lam : (L → L) → L and the freedom to recurse. To get around this, we
-- postulate the inductive hypotheses. This is a hack and is only 'legal'
-- when we are applying it to functions which arise as second order abstract
-- syntax in the data types involved.

-- R-displayed-model 

R-Ty : Ty → M.Ty
R-Tm : ∀ {A} → Tm A → M.Tm (R-Ty A)

coe : ∀ {A B : Set} → A ≡ B → A → B
coe refl a = a

postulate 
  R2-Tm-Ty : ∀ {A} → (Tm A → Ty) → (M.Tm (R-Ty A) → M.Ty)

  R2-Tm-Tm : ∀ {A B} → ((a : Tm A) → Tm (B a)) → ((a : M.Tm (R-Ty A)) → M.Tm (R2-Tm-Ty B a))

  R2-Tm-Ty-eq : ∀ {A f a} → (R2-Tm-Ty {A = A} f) (R-Tm a) ≡ R-Ty (f a)

  R2-Tm-Tm-eq : ∀ {A B f a} → (R2-Tm-Tm {A = A} {B = B} f) (R-Tm {A = A} a) ≡ coe (sym ({!   !})) (R-Tm (f a))

R-Ty U = M.U
R-Ty (El A) = M.El (R-Tm A)
R-Ty (⊤) = M.⊤
R-Ty (Π A B) = M.Π (R-Ty A) (λ a → R2-Tm-Ty B a)
R-Ty (Σ A B) = M.Σ (R-Ty A) (λ a → R2-Tm-Ty B a)
R-Ty (Id a b) = M.Id (R-Tm a) (R-Tm b)
R-Ty (Data S (X , _) δ) = M.El (R-Tm (apps X δ))
R-Ty (Repr T) = R-Ty T

R-Tm (app t u) = coe (cong M.Tm R2-Tm-Ty-eq) (M.app (R-Tm t) (R-Tm u))
R-Tm (lam f) = M.lam (R2-Tm-Tm f)
R-Tm (pair t u) = M.pair (R-Tm t) (coe (cong M.Tm (sym R2-Tm-Ty-eq)) (R-Tm u))
R-Tm tt = M.tt
R-Tm (fst t) = M.fst (R-Tm t)
R-Tm (snd t) = {!   !} -- M.snd (R-Tm t)
-- R-Tm (refl {a = a}) = M.refl (R-Tm a)
-- R-Tm (J P {a = a} {b = b} p) = M.J (R-Tm P) (R2-Tm-Tm p) (R-Tm a) (R-Tm b)
 