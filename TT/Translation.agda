{-# OPTIONS --rewriting #-}
module TT.Translation where

open import TT.Utils
open import TT.Core
open import TT.Tel
open import TT.Base
open import TT.Data
open import TT.Repr
open import TT.Sig
open import TT.Theories

open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; subst; cong; cong₂; trans; sym)

-- Given a model of MLTT, we can construct a model of DataTT. This gives us a
-- map from the syntax of DataTT to the syntax of MLTT, by the universal
-- property of the syntax.

module R (mltt : MLTT-Ext) where
  open MLTT-Ext mltt

  open DataTT

  open Data-structure
  open Repr-structure
  open Repr-Data-structure
  open Repr-compat-Π
  open Repr-compat-Σ
  open Repr-compat-⊤
  open Repr-compat-Id

  open Us-notation (mltt .T) T-Π T-U

  datatt : DataTT
  
  open Data-structure (datatt .T-Data) 
  open Sig-construction (datatt .T-MLTT) 

  -- Base structure is the same
  datatt .T = mltt .T
  datatt .T-MLTT = mltt .T-MLTT

  -- Need to translate Data and Repr structures

  -- Data is translated by the provided inductive algebras
  datatt .T-Data .Data S γ δ = El (apps (γ .Carrier) δ)
  datatt .T-Data .ctor {S = S} {γ} o v = apps (at o (γ .algebra)) v
  datatt .T-Data .ctors S γ = γ .algebra
  datatt .T-Data .ctors-def S γ = sym (sig-spine-η {Γ = λ {O} o → input O _} {α = γ .algebra})
  datatt .T-Data .elim {Δ = Δ} {S = S} {γ} P β δx = apply-ind-sec γ P β δx
  datatt .T-Data .Data-β {Δ = Δ} {S = S} {γ = γ} P β o v = reflect (apply-ind-coh γ P β o v)

  -- Repr is translated away
  datatt .T-R .Repr A = A
  datatt .T-R .repr t = t
  datatt .T-R .unrepr t = t
  datatt .T-R .Repr-η-1 = refl
  datatt .T-R .Repr-η-2 = refl
  datatt .T-RΠ .Repr-Π = refl
  datatt .T-RΠ .repr-lam = refl
  datatt .T-RΠ .unrepr-lam = refl
  datatt .T-RΠ .repr-app = refl
  datatt .T-RΠ .unrepr-app = refl
  datatt .T-RΣ .Repr-Σ = refl
  datatt .T-RΣ .repr-fst = refl
  datatt .T-RΣ .unrepr-fst = refl
  datatt .T-RΣ .repr-snd = refl
  datatt .T-RΣ .unrepr-snd = refl
  datatt .T-RΣ .repr-pair = refl
  datatt .T-RΣ .unrepr-pair = refl
  datatt .T-R⊤ .Repr-⊤ = refl
  datatt .T-R⊤ .repr-tt = refl
  datatt .T-R⊤ .unrepr-tt = refl
  datatt .T-RId .Repr-Id = refl
  datatt .T-RId .repr-rfl = refl
  datatt .T-RId .unrepr-rfl = refl
  datatt .T-RId .repr-J = refl
  datatt .T-RId .unrepr-J = refl

  datatt .T-RData .Repr-Data δ = refl
  datatt .T-RData .repr-total {Δ = Δ} δx = map-last {Δ = Δ} (λ δ x → x) δx
  datatt .T-RData .unrepr-total {Δ = Δ} δx = map-last {Δ = Δ} (λ δ x → x) δx
  datatt .T-RData .repr-total-def δx = refl
  datatt .T-RData .unrepr-total-def δx = refl
  datatt .T-RData .unrepr-total-repr-total {Δ} δx = trans (split-take-id (map-last {Δ = Δ} (λ δ x → x) δx)) (split-take-id δx)
  datatt .T-RData .repr-ctor {γ = γ} o v = Id-uip-right refl (rfl _)
  datatt .T-RData .repr-disp-alg {γ = γ} M β = β
  datatt .T-RData .repr-disp-alg-def {γ = γ} M β = sym (sig-spine-η {Γ = λ {O} o → disp-input O _})
  datatt .T-RData .unrepr-disp-alg {γ = γ} M β = β
  datatt .T-RData .unrepr-disp-alg-def {γ = γ} M β = sym (sig-spine-η {Γ = λ {O} o → disp-input O _})
  datatt .T-RData .repr-elim {γ = γ} M β δx = refl 
  datatt .T-RData .unrepr-elim {γ = γ} M β δx = refl 


-- From this, we can derive translations between syntax:
module 𝓡 where
  open TT
  open _~>_
  open MLTT-Ext
  open DataTT
  open R
  
  D-Ty = DataTT-syntax .T .Ty 
  M-Ty = MLTT-Ext-syntax .T .Ty 
  D-Tm = DataTT-syntax .T .Tm 
  M-Tm = MLTT-Ext-syntax .T .Tm 
  
  𝓡-Ty : D-Ty → M-Ty
  𝓡-Ty A = (DataTT-rec (datatt MLTT-Ext-syntax)) .Ty~> A

  𝓡-Tm : ∀ {A} → D-Tm A → M-Tm (𝓡-Ty A)
  𝓡-Tm t = (DataTT-rec (datatt MLTT-Ext-syntax)) .Tm~> t

  -- Becase equality in the model is propositional equality in
  -- Agda, this holds automatically.
  𝓡-Ty~ : ∀ {A B : D-Ty} → A ≡ B → 𝓡-Ty A ≡ 𝓡-Ty B
  𝓡-Ty~ refl = refl

  𝓡-Tm~ : ∀ {A} {t u : D-Tm A} → t ≡ u → 𝓡-Tm t ≡ 𝓡-Tm u
  𝓡-Tm~ refl = refl
  

-- DataTT + extensionality also contains a model of MLTT + extensionality
module INJ
  (datatt : DataTT)
  (id-ext : Id-extensional (DataTT.T datatt) (MLTT-structure.T-Id (DataTT.T-MLTT datatt)))
  where
  open TT
  open MLTT-Ext
  open DataTT
  open Id-extensional
  
  mltt : MLTT-Ext
  
  mltt .T = datatt .T
  mltt .T-MLTT = datatt .T-MLTT
  mltt .T-Id-ext = id-ext
  

-- R is a left inverse of INJ (as morphisms of models)
module R-left-inverse (mltt : MLTT-Ext) where
  mltt' : MLTT-Ext
  mltt' = INJ.mltt (R.datatt mltt) (MLTT-Ext.T-Id-ext mltt)

  -- Because we are using records, and are grouping MLTT together, agda can
  -- infer this :) (See "Base structure is the same" in R)
  R-left-inv : mltt ≡ mltt'
  R-left-inv = refl
  

  