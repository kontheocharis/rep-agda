{-# OPTIONS --prop #-}
module TT.Translation where

open import Utils
open import TT.Core
open import TT.Tel
open import TT.Base
open import TT.Data
open import TT.Repr
open import TT.Sig
open import TT.Theories
open import TT.Lemmas

open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; subst; cong; cong₂; trans; sym)

-- Given a model of MLTT, we can construct a model of DataTT. This gives us a
-- map from the syntax of DataTT to the syntax of MLTT, by the universal
-- property of the syntax.

module R (m : MLTT) where
  open MLTT m
  open MLTT-structure T-MLTT
  open TT T
  open U-structure T-U
  open Π-structure T-Π
  open Σ-structure T-Σ
  open Id-structure T-Id
  open ⊤-structure T-⊤
  open Tel-construction T
  open Sig-construction T-MLTT
  open IndAlg

  open Data-structure
  open Repr-structure
  open Repr-compat-Π
  open Repr-compat-Σ
  open Repr-compat-⊤
  open Repr-compat-Id
  open DataTT

  open El-apps-lams-code (m .T) T-Π T-U
  
  d : DataTT

  -- Base structure is the same
  d .T = m .T
  d .T-MLTT = m .T-MLTT

  -- Need to translate Data and Repr structures

  -- Data is translated by the provided inductive algebras
  d .T-Data .Data S γ δ = El (apps (γ .Carrier) δ)
  d .T-Data .ctor {S = S} {γ} o v = apps (at o (γ .algebra)) v
  d .T-Data .elim {Δ = Δ} {S = S} {γ} P β δx = 
    let α = γ .algebra in
    let alg-induction = γ .induction in
    let code-P = lams (λ δx → code (P δx)) in
    let induction-on-P = app alg-induction code-P in
    
    -- let β-actual : Spine (disp-alg  (sig-spine  S (λ p → lams  (d .T-Data .ctor p))) P)
    --     β-actual = β in

    let P' = λ δx₁ → El (apps code-P δx₁) in
    let β' : Spine (disp-alg α P')
        β' = coe
              (cong₂ (λ α P → Spine (disp-alg α P)) {y = α} {u = P}
                {!   !}
                (funext (λ δ → sym (El-apps-lams-code δ)))) β in
    let section-coh = apps
          {Δ = disp-alg α (λ δx → El (apps code-P δx))}
          induction-on-P β' in
    let section = fst section-coh in

    coe
      (trans (cong (λ t → Tm (El t)) (Πs-β {f = λ δx → code (P δx)})) (cong Tm U-η-1))
      (apps section δx)

  d .T-Data .Data-β = {!   !}
  -- : Spine (M .T) () 
  -- TODO: repr on data

  -- Repr is translated away
  d .T-R .Repr A = A
  d .T-R .repr t = t
  d .T-R .unrepr t = t
  d .T-R .Repr-η-1 = refl
  d .T-R .Repr-η-2 = refl
  d .T-RΠ .Repr-Π = refl
  d .T-RΠ .repr-lam = refl
  d .T-RΠ .unrepr-lam = refl
  d .T-RΠ .repr-app = refl
  d .T-RΠ .unrepr-app = refl
  d .T-RΣ .Repr-Σ = refl
  d .T-RΣ .repr-fst = refl
  d .T-RΣ .unrepr-fst = refl
  d .T-RΣ .repr-snd = refl
  d .T-RΣ .unrepr-snd = refl
  d .T-RΣ .repr-pair = refl
  d .T-RΣ .unrepr-pair = refl
  d .T-R⊤ .Repr-⊤ = refl
  d .T-R⊤ .repr-tt = refl
  d .T-R⊤ .unrepr-tt = refl
  d .T-RId .Repr-Id = refl
  d .T-RId .repr-rfl = refl
  d .T-RId .unrepr-rfl = refl
  d .T-RId .repr-J = refl
  d .T-RId .unrepr-J = refl


𝓡 : MLTT → DataTT
𝓡 m = R.d m

