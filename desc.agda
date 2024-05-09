module Desc where

open import Agda.Builtin.Unit
open import Agda.Builtin.Equality
open import Data.Product using (_×_; _,_; Σ)
open import Agda.Builtin.Sigma using (fst; snd)
open import Function.Base using (_∘_)

data Desc (I : Set) : Set1 where
  one : I -> Desc I
  var : I -> Desc I
  _*_ : Desc I -> Desc I -> Desc I
  σ : (S : Set) -> (φ : S -> Desc I) -> Desc I


⦅_⦆ : ∀ {I} -> Desc I -> (I -> Set) -> (I -> Set)
⦅ one i' ⦆ X i = i ≡ i'
⦅ var i' ⦆ X i = X i'
⦅ c * d ⦆ X i = ⦅ c ⦆ X i × ⦅ d ⦆ X i
⦅ σ S φ ⦆ X i = Σ S (λ s -> ⦅ φ s ⦆ X i)

_⇒_ : {I : Set} -> (I -> Set) -> (I -> Set) -> Set
_⇒_ {I} X Y = ∀ {i} -> X i -> Y i

data μ {I : Set} (d : Desc I) : I -> Set where
  ⟨_⟩ : {i : I} -> ⦅ d ⦆ (μ d) i -> μ d i

map : ∀ {I X Y} -> (d : Desc I) -> (X ⇒ Y) -> (⦅ d ⦆ X ⇒ ⦅ d ⦆ Y)
map (one i') f p = p
map (var i') f x = f x
map (c * d) f (x , y) = (map c f x , map d f y)
map (σ S φ) f (s , x) = (s , map (φ s) f x)

mutual
  fold : ∀ {I X} {d : Desc I} -> (⦅ d ⦆ X ⇒ X) -> (μ d ⇒ X)
  fold {d = d} a ⟨ x ⟩ = a (map-fold d d a x)

  map-fold : ∀ {I X} -> (d e : Desc I) -> (⦅ d ⦆ X ⇒ X) -> (⦅ e ⦆ (μ d) ⇒ ⦅ e ⦆ X)
  map-fold d (one i) f p = p
  map-fold d (var i) f p = fold f p
  map-fold d (c * e) f (x , y) = (map-fold d c f x , map-fold d e f y)
  map-fold d (σ S φ) f (s , x) = (s , map-fold d (φ s) f x)

data Inv {I J : Set} (e : J -> I) : I -> Set where
  from : (j : J) -> Inv e (e j)

data Orn {I} (J : Set) (e : J -> I) : Desc I -> Set1 where
  o-one : ∀ {i} -> Inv e i -> Orn J e (one i)
  o-var : ∀ {i} -> Inv e i -> Orn J e (var i)
  o-_*_ : ∀ {d d'} -> Orn J e d -> Orn J e d' -> Orn J e (d * d')
  o-σ : (S : Set) -> ∀ {φ} -> (ψ : (s : S) -> Orn J e (φ s)) -> Orn J e (σ S φ)
  o-σ⁺ : ∀ {d} -> (S : Set) -> (ψ : S -> Orn J e d) -> Orn J e d

orn-desc : ∀ {I J e} {d : Desc I} -> Orn J e d -> Desc J
orn-desc (o-one (from j)) = one j
orn-desc (o-var (from j)) = var j
orn-desc (o- d * d') = orn-desc d * orn-desc d'
orn-desc (o-σ S ψ) = σ S (λ s -> orn-desc (ψ s))
orn-desc (o-σ⁺ S ψ) = σ S (λ s -> orn-desc (ψ s))

erase : ∀ {I J e} {d : Desc I} {F : I -> Set} -> (r : Orn J e d) -> (⦅ orn-desc r ⦆ (F ∘ e) ⇒ ((⦅ d ⦆ F) ∘ e))
erase (o-one (from j)) refl = refl
erase (o-var (from j)) x = x
erase (o- d * d') (x , y) = (erase d x , erase d' y)
erase (o-σ S ψ) (s , x) = (s , erase (ψ s) x)
erase (o-σ⁺ S ψ) (s , x) = erase (ψ s) x

orn-alg : ∀ {I J e} {d : Desc I} (r : Orn J e d) -> (⦅ orn-desc r ⦆ ((μ d) ∘ e) ⇒ ((μ d) ∘ e))
orn-alg r x = ⟨ erase r x ⟩


alg-orn : ∀ {I} {F : I -> Set} (d : Desc I) -> (⦅ d ⦆ F ⇒ F) -> Orn (Σ I F) fst d
alg-orn = {!   !}
-- alg-orn (one i) f = o-one (from (i , f refl))
-- alg-orn {F = F} (var i) f = o-σ⁺ (F i) (λ j -> o-var (from (i , j)))
-- alg-orn (c * d) f = {!   !}
-- alg-orn (σ S φ) f = o-σ S (λ s -> alg-orn (φ s) (λ j -> f (s , j)))

-- data Index : ∀ {I} -> Desc I -> Set1 where
--   here : ∀ {I} -> {d : Desc I} -> (i : I) -> Index (node× i d)
--   there : ∀ {I} -> {d : Desc I} -> (i : I) -> Index d -> Index (node× i d)
--   σi : ∀ {I S} -> {φ : S -> Desc I} -> ((s : S) -> Index (φ s)) -> Index (σ S φ)

-- data Tran : ∀ {I} -> Desc I -> Desc I -> Set1 where
--   vac : ∀ {I} -> {d : Desc I} -> (i : I) -> Tran d (end i)
--   skip : ∀ {I} -> {c d : Desc I} -> (i : I) -> Tran c d -> Tran (node× i c) d
--   select :  ∀ {I} -> {c d : Desc I} -> Index c -> Tran c d -> Tran c (node× d)
--   σt :  ∀ {S I} -> {φ ψ : S -> Desc I} -> ((s : S) -> Tran (φ s) (ψ s)) -> Tran (σ S φ) (σ S ψ)
--   _∘_ : ∀ {I} -> ∀ {c d e : Desc I} -> Tran c d -> Tran d e -> Tran c e

-- π : ∀ {I} -> {X : I -> Set} -> {d : Desc I} -> Index d -> (Interp d X ⇒ X)
-- π here i (x , xs) = x
-- π (there n) i (x , xs) = π n i xs
-- π (σi f) i (s , xs) = π (f s) i xs

-- interp-fun : ∀ {I} -> {d : Desc I} -> {X Y : I -> Set} -> (f : X ⇒ Y) -> (Interp d X ⇒ Interp d Y)
-- interp-fun {d = end i'} f i refl = refl
-- interp-fun {d = node× d} f i (x , xs) = (f i x , interp-fun f i xs)
-- interp-fun {d = σ S φ} f i (s , xs) = (s , interp-fun f i xs)

-- interp-tran : ∀ {I X} -> {d d' : Desc I} -> Tran d d' -> (Interp d X ⇒ Interp d' X)
-- interp-tran (vac i') i x = refl
-- interp-tran (select n t) i x = (π n i x , interp-tran t i x)
-- interp-tran (σt f) i (s , xs) = (s , interp-tran (f s) i xs)
-- interp-tran (skip t) i (x , xs) = interp-tran t i xs
-- interp-tran (t ∘ t') i x = interp-tran t' i (interp-tran t i x)

-- id-tran : ∀ {I} -> {d : Desc I} -> Tran d d
-- id-tran {d = end i} = vac i
-- id-tran {d = node× d} = select here (skip (id-tran))
-- id-tran {d = σ S φ} = σt (λ _ -> id-tran)

-- {-# TERMINATING #-}
-- μF : ∀ {d d'} -> Tran d d' -> (μ d ⇒ μ d')
-- μF t (ctor x) i = ctor (interp-tran t (interp-fun (μF t) x) i)

-- Like

-- orn-alg : ∀ {R I} -> {d : Desc I} -> (Interp d R ⇒ R)
-- orn-alg  = {!   !}

-- record Like (d : Desc) : Set1 where
--   field
--     R : Set
--     compile : Interp d R -> R
--     inspect : (r : R) -> μ (orn-alg compile)

-- 2LTT


data Ty : Set where
  _=>_ : Ty -> Ty -> Ty
  _*_ : Ty -> Ty -> Ty
  unit : Ty
  bool : Ty

-- data Ctx : Set where
--   ∙ : Ctx
--   _,_ : Ctx -> Ty -> Ctx

-- data Var : Ctx -> Ty -> Set where
--   here : ∀ {Γ A} -> Var (Γ , A) A
--   there : ∀ {Γ A B} -> Var Γ A -> Var (Γ , B) A
{-# NO_POSITIVITY_CHECK #-}
data Tm : Ty -> Set where
  lam : ∀ {A B} -> (Tm A -> Tm B) -> Tm (A => B)
  ap : ∀ {A B} -> Tm (A => B) -> Tm A -> Tm B
  tt : Tm unit
  -- var : ∀ {Γ A} -> Var Γ A -> Tm Γ A
  pair : ∀ {A B} -> Tm A -> Tm B -> Tm (A * B)
  first : ∀ {A B} -> Tm (A * B) -> Tm A
  second : ∀ {A B} -> Tm (A * B) -> Tm B
  true : Tm bool
  false : Tm bool
  if_then_else_ : ∀ {A} -> Tm bool -> Tm A -> Tm A -> Tm A

data Code : Ty -> Set where
  ⟨_⟩ : ∀ {A} -> Tm A -> Code A

~_ : ∀ {A} -> (t : Code A) -> Tm A
~ (⟨ x ⟩) = x

-- data Codes : Ctx -> Set where
--   ⟨∙⟩ : Codes ∙
--   ⟨_/_⟩ : ∀ {Γ A} -> Codes Γ -> Code A -> Codes (Γ , A)

-- weaken : ∀ {Γ A} -> (B : Ty) -> Tm Γ A -> Tm (Γ , B) A
-- weaken = {!   !}

-- weaken-full : ∀ {A} -> (Γ : Ctx) -> Tm ∙ A -> Tm Γ A
-- weaken-full = {!   !}

-- fold-ctx : {C : Set} -> (C -> Ty -> C) -> C -> Ctx -> C
-- fold-ctx f c ∙ = c
-- fold-ctx f c (Γ , A) = f (fold-ctx f c Γ) A

-- ~~_ : ∀ {Γ A} -> Code A -> Ctx
-- ~~_ {Γ = Γ} _ = Γ

-- %_ : ∀ {A E} -> (t : Var E -> Code A) -> Tm ( ∙ , E ) A
-- -- %_ {Γ = ∙} t = ~ (t ⟨∙⟩)
-- %_ {A} {E} t = ~ (t {!   !})

pi-iso : ∀ {A : Ty} -> (Code A -> Code A) -> (Code (A => A))
pi-iso f = ⟨ lam (λ x -> ~(f ⟨ x ⟩)) ⟩

iso-pi : ∀ {A : Ty} -> (Code (A => A)) -> (Code A -> Code A)
iso-pi f x = ⟨ ap (~ f) (~ x) ⟩

Gen : Set -> Set
Gen A = (R : Ty) -> (A -> Code R) -> Code R

mutual
  data Typ (I : Set) : Set1
  record Fn (I : Set) : Set1

  Typ⦅_⦆ : ∀ {I} -> Typ I -> (I -> Set)

  record Fn I where
    inductive
    field
      dom : Typ I
      cod : Typ (Σ I Typ⦅ dom ⦆)

  data Typ I where
    desc : Desc I -> Typ I
    fn : Fn I -> Typ I

  Fn⦅_⦆ : ∀ {I} -> Fn I -> (I -> Set)
  Fn⦅ f ⦆ i = (a : Typ⦅ Fn.dom f ⦆ i) -> Typ⦅ Fn.cod f ⦆ (i , a)

  Typ⦅ fn f ⦆ i = Fn⦅ f ⦆ i
  Typ⦅ desc d ⦆ i = μ d i


mutual
  record ReprDesc {I : Set} (d : Desc I) : Set1
  record ReprFn {I : Set} (d : Fn I) : Set1

  data Repr {I : Set} : Typ I -> Set1 where
    desc-repr : ∀ {d} -> ReprDesc d -> Repr (desc d)
    fn-repr : ∀ {f} -> ReprFn f -> Repr (fn f)

  record ReprFn {I} f where
    inductive
    field
      dom : Repr (Fn.dom f)
      cod : Repr (Fn.cod f)

  record ReprDesc {I} d where
    field
      R : I -> Ty
      compile : ∀ {i} -> ⦅ d ⦆ (Code ∘ R) i -> Code (R i)
      view : ∀ {i} -> (c : Code (R i)) -> Gen (μ (orn-desc (alg-orn d compile)) (i , c))


Repr⦅_⦆ : ∀ {I} {t : Typ I} -> Repr t -> (I -> Set)
Repr⦅ desc-repr d ⦆ i = Code (ReprDesc.R d i)
Repr⦅ fn-repr f ⦆ i = Repr⦅ ReprFn.dom f ⦆ i -> Repr⦅ ReprFn.cod f ⦆ (i , {!   !})

mutual
  record ReprLam {I : Set} (F : Fn I) (RF : ReprFn F) (f : (i : I) -> (Fn⦅ F ⦆) i) : Set1

  default-repr-lam : ∀ {I} {F : Fn I} {RF : ReprFn F} (f : (i : I) -> (Fn⦅ F ⦆) i) -> ((i : I) -> Repr⦅ fn-repr RF ⦆ i)
  default-repr-lam f i d = {!   !}

  record ReprLam {I} F RF f where
    field
      f' : (i : I) -> Repr⦅ fn-repr RF ⦆ i
      coh : ∀ {i} -> f' i ≡ default-repr-lam f i

