-- open import Data.String using (String)
-- open import Data.List using (List; _∷_; []; length; _++_; lookup; map; foldl; replicate)
-- open import Data.Fin using (Fin; zero; suc)
-- open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
-- open import Data.Bool using (Bool; true; false; if_then_else_)
-- open import Data.Unit using (⊤; tt)
-- open import Data.Vec using (Vec; _∷_; []; lookup; map)
open import Agda.Builtin.Nat using (Nat; suc; zero; _==_)
open import Agda.Builtin.Word using (Word64)
-- open import Agda.Primitive

data LTy : Set where
  Word : LTy

data LTm : LTy -> Set where
  w : Word64 -> LTm Word

postulate
  ^ : LTy -> Set

-- data LTy : Set where

-- data LTm : LTy -> Set where

-- Product : List Set -> Set
-- Product [] = ⊤
-- Product (A ∷ As) = A × Product As

-- record Poly (S : Set) : Set where
--   constructor poly
--   field
--     sh : Nat
--     pos : Fin sh -> Nat
--     coe : Fin sh -> S

-- mk-poly : ∀ {S} {sh : Nat} -> Vec (S × Nat) sh -> Poly S
-- mk-poly {S} {sh} xs = poly sh (λ i -> proj₂ (Data.Vec.lookup xs i)) (λ i -> proj₁ (Data.Vec.lookup xs i))

-- data STy : Set where
--   _=>_ : STy -> STy -> STy
--   μ : Poly STy -> STy
--   _⦅_⦆ : Poly STy -> STy -> STy
--   Q : LTy -> STy
--   I : STy

-- data SCtx : Set where
--   ∅ : SCtx
--   _,_ : SCtx -> STy -> SCtx

-- data SVar : SCtx -> Set where
--   z : ∀ {Γ A} -> SVar (Γ , A)
--   s : ∀ {Γ A} -> SVar Γ -> SVar (Γ , A)

-- fin-zero : ∀ {l : Level} {A : Set l} -> Fin zero -> A
-- fin-zero ()

-- DepVec : (n : Nat) -> (Fin n -> Set) -> Set
-- DepVec zero _ = ⊤
-- DepVec (suc n) P = Σ (P zero) (λ x -> DepVec n (λ i -> P (suc i)))

-- extend-ctx : SCtx -> List STy -> SCtx
-- extend-ctx Γ [] = Γ
-- extend-ctx Γ (A ∷ As) = extend-ctx (Γ , A) As

-- data STm : SCtx -> STy -> Set where
--   lam : ∀ {Γ A B} -> STm (Γ , A) B -> STm Γ (A => B)
--   app : ∀ {Γ A B} -> STm Γ (A => B) -> STm Γ A -> STm Γ B
--   _/_ : ∀ {Γ A} -> (P : Poly STy) -> (i : Fin (Poly.sh P)) -> STm Γ (Poly.coe P i) -> Vec (STm Γ A) (Poly.pos P i) -> STm Γ (P ⦅ A ⦆)
--   v : ∀ {Γ A} -> SVar Γ -> STm Γ A
--   letin : ∀ {Γ A B} -> STm Γ A -> STm (Γ , A) B -> STm Γ B
--   q : ∀ {Γ} {C : LTy} -> LTm C -> STm Γ (Q C)
--   caseof : ∀ {Γ A B P} -> STm Γ (P ⦅ A ⦆) -> DepVec (Poly.sh P) (λ i -> STm (extend-ctx (Γ , Poly.coe P i) (replicate (Poly.pos P i) A)) B) -> STm Γ B
--   unwrap : ∀ {Γ F} -> STm Γ (μ F) -> STm Γ (F ⦅ μ F ⦆)
--   wrap : ∀ {Γ F} -> STm Γ (F ⦅ μ F ⦆) -> STm Γ (μ F)
--   fold : ∀ {Γ F A} -> STm Γ ((F ⦅ A ⦆) => A) -> STm Γ ((μ F) => A)
--   unfold : ∀ {Γ F A} -> STm Γ (A => (F ⦅ A ⦆)) -> STm Γ (A => (μ F))
--   ⋆ : ∀ {Γ} -> STm Γ I

-- weaken-S : ∀ {Γ Δ A} -> STm Γ A -> STm (Γ , Δ) A
-- -- weaken-S (lam e) = lam (weaken-S e)
-- weaken-S (app f e) = app (weaken-S f) (weaken-S e)
-- weaken-S ((P / i) e es) = (P / i) (weaken-S e) (Data.Vec.map weaken-S es)
-- weaken-S (v n) = v (s n)
-- weaken-S _ = {!   !}

-- weaken-fn-S : ∀ {Γ Δ A B} -> (STm Γ A -> STm Γ B) -> (STm (Γ , Δ) A -> STm (Γ , Δ) B)
-- weaken-fn-S = {!   !}

-- mk-lam : ∀ {Γ A B} -> (STm Γ A -> STm Γ B) -> STm Γ (A => B)
-- mk-lam f = lam ((weaken-fn-S f) (v z))

--   -- data STms : SCtx -> List STy -> Set

--   -- data STms where
--   --   [] : ∀ {Γ} -> STms Γ []
--   --   _,_ : ∀ {Γ A As} -> STm Γ A -> STms Γ As -> STms Γ (A ∷ As)

--   -- extend-ctx : SCtx -> List STy -> SCtx
--   -- extend-ctx Γ [] = Γ
--   -- extend-ctx Γ (A ∷ As) = extend-ctx (Γ , A) As

--   -- data DepVec : List Set -> Set where
--   --   [] : DepVec []
--   --   _,_ : ∀ {A As} -> A -> DepVec As -> DepVec (A ∷ As)

--   -- VariantTerms : ∀ {F} -> SCtx -> VariantIdx F -> STy ∅ -> Set
--   -- VariantTerms {F} Γ i A = STms Γ (map (λ T -> T [ A ]) (variant-tys {F} i))

--   -- VariantElims : SFunc -> SCtx -> STy ∅ -> STy ∅ -> Set
--   -- VariantElims F Γ A B = DepVec (map (λ f -> STm (extend-ctx Γ (map (λ l -> l [ A ]) (SField.ty f)))  B) (SFunc.variants F))

-- NatF : Poly STy
-- NatF = mk-poly (( I , 0 ) ∷ ( I , 1 ) ∷ [])

-- NatT : STy
-- NatT = μ NatF

-- zeF : ∀ {Γ} {A : STy} -> STm Γ (NatF ⦅ A ⦆)
-- zeF = (NatF / zero) ⋆ []

-- suF : ∀ {Γ} {A : STy} -> STm Γ A -> STm Γ (NatF ⦅ A ⦆)
-- suF n = (NatF / suc zero) ⋆ (n ∷ [])

-- ze : ∀ {Γ} -> STm Γ NatT
-- ze = wrap zeF

-- su : ∀ {Γ} -> STm Γ NatT -> STm Γ NatT
-- su n = wrap (suF n)

-- su' : ∀ {Γ} -> STm Γ (NatT => NatT)
-- su' = lam (su (v z))

-- nat-elim : ∀ {Γ B} -> STm Γ B -> STm Γ (NatT => B) -> STm Γ (NatT => B)
-- nat-elim b f = lam (caseof {P = NatF} (unwrap (v z)) ((weaken-S (weaken-S b)) , app (weaken-S (weaken-S (weaken-S f))) (v z) , tt))


