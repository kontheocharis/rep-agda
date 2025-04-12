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

module R (m : MLTT-Ext) where
  open MLTT-Ext m

  open DataTT

  open Data-structure
  open Repr-structure
  open Repr-compat-Π
  open Repr-compat-Σ
  open Repr-compat-⊤
  open Repr-compat-Id
  open El-apps-lams-code (m .T) T-Π T-U

  model : DataTT
  
  open Data-structure (model .T-Data) 
  open Sig-construction (model .T-MLTT) 
  

  -- Base structure is the same
  model .T = m .T
  model .T-MLTT = m .T-MLTT

  -- Need to translate Data and Repr structures

  -- Data is translated by the provided inductive algebras
  model .T-Data .Data S γ δ = El (apps (γ .Carrier) δ)
  model .T-Data .ctor {S = S} {γ} o v = apps (at o (γ .algebra)) v
  model .T-Data .elim {Δ = Δ} {S = S} {γ} P β δx = apply-ind-sec γ P (coe-disp-alg-η {γ = γ} β) δx
  model .T-Data .Data-β {Δ = Δ} {S = S} {γ = γ} P β o v
    = let x = reflect (apply-ind-coh γ P (coe-disp-alg-η {γ = γ} β) o v) in {!   !}
    -- let induction-on-P = app (γ .induction) (lams (λ δx → code (P δx))) in

    -- let β-over-α = coe (cong₂ (λ α P → Spine (disp-alg α P))
    --             (sig-spine-η {Γ = λ {O} o → input O _} {α = γ .algebra})
    --             (funext (λ δ → sym (El-apps-lams-code δ)))) β in
    -- let section-coh = apps induction-on-P β-over-α in
    -- let coh = at o (get-spine {Δ = coh β-over-α _} (snd section-coh)) in
    -- let coh-for-v = reflect (apps coh v) in
    
    -- {!   !}
    -- coh-for-v
    -- trans (cong₂ apps refl (cong (λ x → (output _ ⨾ x)) (cong₂ apps (cong (at o) sig-spine-η) refl))) (trans coh-for-v {!   !} )

    -- trans {!  !} (trans {!   !} {!   !})
  -- TODO: repr on data
-- coe-Tm ( trans ( cong El Πs-β) U-η-1) ( apps (..) (..)) ≡ apps ( Sig-construction.at T-MLTT o β) (..)
  -- Repr is translated away
  model .T-R .Repr A = A
  model .T-R .repr t = t
  model .T-R .unrepr t = t
  model .T-R .Repr-η-1 = refl
  model .T-R .Repr-η-2 = refl
  model .T-RΠ .Repr-Π = refl
  model .T-RΠ .repr-lam = refl
  model .T-RΠ .unrepr-lam = refl
  model .T-RΠ .repr-app = refl
  model .T-RΠ .unrepr-app = refl
  model .T-RΣ .Repr-Σ = refl
  model .T-RΣ .repr-fst = refl
  model .T-RΣ .unrepr-fst = refl
  model .T-RΣ .repr-snd = refl
  model .T-RΣ .unrepr-snd = refl
  model .T-RΣ .repr-pair = refl
  model .T-RΣ .unrepr-pair = refl
  model .T-R⊤ .Repr-⊤ = refl
  model .T-R⊤ .repr-tt = refl
  model .T-R⊤ .unrepr-tt = refl
  model .T-RId .Repr-Id = refl
  model .T-RId .repr-rfl = refl
  model .T-RId .unrepr-rfl = refl
  model .T-RId .repr-J = refl
  model .T-RId .unrepr-J = refl


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
  𝓡-Ty A = (DataTT-rec (model MLTT-Ext-syntax)) .Ty~> A

  𝓡-Tm : ∀ {A} → D-Tm A → M-Tm (𝓡-Ty A)
  𝓡-Tm t = (DataTT-rec (model MLTT-Ext-syntax)) .Tm~> t

  𝓡-Ty~ : ∀ {A B : D-Ty} → A ≡ B → 𝓡-Ty A ≡ 𝓡-Ty B
  𝓡-Ty~ refl = refl

  𝓡-Tm~ : ∀ {A} {t u : D-Tm A} → t ≡ u → 𝓡-Tm t ≡ 𝓡-Tm u
  𝓡-Tm~ refl = refl