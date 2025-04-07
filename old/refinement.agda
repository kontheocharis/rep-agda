{-# OPTIONS --rewriting #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _<?_; _≥_; s≤s⁻¹)
open import Data.Nat.Properties using (suc-injective)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

subst-ty : {A B : Set} → A ≡ B → A → B
subst-ty = subst (λ X → X)

postulate
  Repr : ∀ {i} -> Set i -> Set i
  repr : ∀ {i} {T : Set i} -> T -> Repr T
  repr-pi : ∀ {i} {A : Set i} {B : A -> Set i} -> Repr ((a : A) -> B a) ≡ ((a : A) -> Repr (B a))
  {-# REWRITE repr-pi #-}
  repr-set : Repr Set ≡ Set
  {-# REWRITE repr-set #-}
  repr-lam : ∀ {i} {A : Set i} {B : A -> Set i} {t : (a : A) -> B a} -> repr (λ x -> t x) ≡ λ x -> repr (t x)
  {-# REWRITE repr-lam #-}
  -- repr-app : ∀ {i} {A : Set i} {B : A -> Set i} {t : (a : A) -> B a} {x : A} -> repr (t x) ≡ (subst-ty (repr-pi {i} {A} {B}) (repr t)) x
  -- {-# REWRITE repr-app #-}


data List (T : Set) : Set where
  nil : List T
  cons : T -> List T -> List T

length : ∀ {T} -> List T -> ℕ
length nil = zero
length (cons _ xs) = suc (length xs)

data Vec (T : Set) : ℕ -> Set where
  vec-nil : Vec T zero
  vec-cons : ∀ {n} -> T -> Vec T n -> Vec T (suc n)

Vec' : Set -> ℕ -> Set
Vec' T n = Σ (List T) (λ l -> length l ≡ n)

vec-nil' : ∀ {T} -> Vec' T zero
vec-nil' = nil , refl

vec-cons' : ∀ {T n} -> T -> Vec' T n -> Vec' T (suc n)
vec-cons' x (xs , eq) = cons x xs , cong suc eq

suc-cong-id : ∀ {m n} -> (p : suc m ≡ suc n) -> cong suc (suc-injective p) ≡ p
suc-cong-id refl = refl

vec-ind' : ∀ {T} -> (P : (n : ℕ) -> Vec' T n -> Set)
  -> P zero vec-nil'
  -> (∀ {n} -> (x : T) -> (xs : Vec' T n) -> P (suc n) (vec-cons' x xs))
  -> ∀ {n} -> (v : Vec' T n) -> P n v
vec-ind' P ni co {n = 0} (nil , refl) = ni
vec-ind' P ni co {n = suc m} (cons x xs , eq) = subst (λ p -> P (suc m) (cons x xs , p)) (suc-cong-id eq) (co x (xs , suc-injective eq))
