{-# OPTIONS --prop --allow-unsolved-metas #-}
module Translation where

open import Agda.Builtin.Nat using (Nat; suc; zero)
open import Data.Fin.Base using (Fin; suc; zero)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; subst; cong)
open import Data.Product.Base using (_,_) renaming (Σ to Pair)

import MLTT as M
open import DataTT

open DataTT-model
open DataTT-transformation 


R : DataTT-model
R .Ty∘ = M.Ty 
R .Tm∘ A = M.Tm A
R .U∘ = M.U
R .El∘ t = M.El t
R .⊤∘ = M.⊤
R .tt∘ = M.tt
R .Π∘ A B = M.Π A B
R .lam∘ f = M.lam f
R .app∘ x a = M.app x a
R .Σ∘ A B = M.Σ A B
R .pair∘ a b = M.pair a b
R .fst∘ p = M.fst p
R .snd∘ p = M.snd p
R .Id∘ x y = M.Id x y
R .refl∘ = M.refl
R .J∘ P reflP p = M.J P reflP p
R .Repr∘ A = A
R .unrepr∘ t = t
R .repr∘ t = t



-- R-Ty : Ty → M.Ty
-- R-Tm : ∀ {A} → Tm A → M.Tm (R-Ty A)

-- coe : ∀ {A B : Set} → A ≡ B → A → B
-- coe refl a = a

-- postulate 
--   R2-Tm-Ty : ∀ {A} → (Tm A → Ty) → (M.Tm (R-Ty A) → M.Ty)

--   R2-Tm-Tm : ∀ {A B} → ((a : Tm A) → Tm (B a)) → ((a : M.Tm (R-Ty A)) → M.Tm (R2-Tm-Ty B a))

--   R2-Tm-Ty-eq : ∀ {A f a} → (R2-Tm-Ty {A = A} f) (R-Tm a) ≡ R-Ty (f a)

--   R2-Tm-Tm-eq : ∀ {A B f a} → (R2-Tm-Tm {A = A} {B = B} f) (R-Tm {A = A} a) ≡ coe (sym ({!   !})) (R-Tm (f a))

-- R-Ty U = M.U
-- R-Ty (El A) = M.El (R-Tm A)
-- R-Ty (⊤) = M.⊤
-- R-Ty (Π A B) = M.Π (R-Ty A) (λ a → R2-Tm-Ty B a)
-- R-Ty (Σ A B) = M.Σ (R-Ty A) (λ a → R2-Tm-Ty B a)
-- R-Ty (Id a b) = M.Id (R-Tm a) (R-Tm b)
-- R-Ty (Data S (X , _) δ) = M.El (R-Tm (apps X δ))
-- R-Ty (Repr T) = R-Ty T

-- R-Tm (app t u) = coe (cong M.Tm R2-Tm-Ty-eq) (M.app (R-Tm t) (R-Tm u))
-- R-Tm (lam f) = M.lam (R2-Tm-Tm f)
-- R-Tm (pair t u) = M.pair (R-Tm t) (coe (cong M.Tm (sym R2-Tm-Ty-eq)) (R-Tm u))
-- R-Tm tt = M.tt
-- R-Tm (fst t) = M.fst (R-Tm t)
-- R-Tm (snd t) = {!   !} -- M.snd (R-Tm t)
-- -- R-Tm (refl {a = a}) = M.refl (R-Tm a)
-- -- R-Tm (J P {a = a} {b = b} p) = M.J (R-Tm P) (R2-Tm-Tm p) (R-Tm a) (R-Tm b)
 