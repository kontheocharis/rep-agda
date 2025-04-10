{-# OPTIONS --prop --allow-unsolved-metas #-}
module TT.Base where

open import TT.Core
open import TT.Tel

record U-structure (T : TT) : Set1 where
  open TT T
  field
    U : Ty
    El : Tm U → Ty
    code : Ty → Tm U

    U-η-1 : ∀ {A} → Ty~ (El (code A)) A
    U-η-2 : ∀ {t} → Tm~ refl-Ty (code (El t)) t

    El~ : ∀ {A~ t t'} → Tm~ A~ t t' → Ty~ (El t) (El t')
    code~ : ∀ {A A'} → Ty~ A A' → Tm~ refl-Ty (code A) (code A')
      

record Π-structure (T : TT) : Set1 where
  open TT T
  field
    Π : (A : Ty) → (Tm A → Ty) → Ty

    lam : ∀ {A} {B : Tm A → Ty}
      → ((a : Tm A) → Tm (B a)) → Tm (Π A B)

    app : ∀ {A} {B : Tm A → Ty}
      → Tm (Π A B) → (a : Tm A) → Tm (B a)

    Π-β : ∀ {A} {B : Tm A → Ty} {f : (a : Tm A) → Tm (B a)} {t : Tm A}
      → Tm~ refl-Ty (app (lam f) t) (f t)
    Π-η : ∀ {A} {B : Tm A → Ty} {f : Tm (Π A B)}
      → Tm~ refl-Ty (lam (λ t → app f t)) f

    Π~ : ∀ {A A'} → (A~ : Ty~ A A') → ∀ {B B'} → (B~ : ∀ {a a'} → Tm~ A~ a a' → Ty~ (B a) (B' a'))
      → Ty~ (Π A B) (Π A' B')

    lam~ : ∀ {A A'} {A~ : Ty~ A A'} → ∀ {B : Tm A → Ty} {B' : Tm A' → Ty}
      → {B~ : ∀ {a a'} → Tm~ A~ a a' → Ty~ (B a) (B' a')}
      → {f : (a : Tm A) → Tm (B a)}
      → {f' : (a' : Tm A') → Tm (B' a')}
      → (f~ : ∀ {a a'} → (a~ : Tm~ A~ a a') → Tm~ (B~ a~) (f a) (f' a'))
      → Tm~ (Π~ A~ B~) (lam f) (lam f')

    app~ : ∀ {A A'} {A~ : Ty~ A A'} → ∀ {B : Tm A → Ty} {B' : Tm A' → Ty}
      → {B~ : ∀ {a a'} → Tm~ A~ a a' → Ty~ (B a) (B' a')}
      → {f : Tm (Π A B)}
      → {f' : Tm (Π A' B')}
      → (f~ : Tm~ (Π~ A~ B~) f f')
      → ∀ {t t'} → (a~ : Tm~ A~ t t')
      → Tm~ (B~ a~) (app f t) (app f' t')
      

  syntax Π A (λ x → B) = [ x ∶ A ] ⇒ B
      
  open Tel-construction T

  Πs : (Δ : Tel) → (Spine Δ → Ty) → Ty
  Πs ∙ t = t []
  Πs (ext A Δ) t = [ a ∶ A ] ⇒ Πs (Δ a) (λ δ → t (a , δ))

  syntax Πs Δ (λ δ → B) = [ δ ∷ Δ ] ⇒ B

  Πs~ : ∀ {Δ Δ'} (Δ~ : Tel~ Δ Δ') 
    → ∀ {Y : Spine Δ → Ty} {Y' : Spine Δ' → Ty}
    → (Y~ : ∀ {δ δ'} → Spine~ Δ~ δ δ' → Ty~ (Y δ) (Y' δ'))
    → Ty~ (Πs Δ Y) (Πs Δ' Y')
  Πs~ ∙~ Y~ = Y~ []~
  Πs~ (ext~ A~ Δ~) Y~ = Π~ A~ (λ a~ → Πs~ (Δ~ a~) (λ δ~ → Y~ (_,~_ {Δ~ = Δ~} a~ δ~)))

  lams : ((δ : Spine Δ) → Tm (Y δ)) → Tm (Πs Δ Y)
  lams {Δ = ∙} f = f []
  lams {Δ = ext A Δ} f = lam (λ a → lams (λ δ → f (a , δ)))

  lams~ : ∀ {Δ Δ'} {Δ~ : Tel~ Δ Δ'} {Y : Spine Δ → Ty} {Y' : Spine Δ' → Ty}
    → {Y~ : ∀ {δ δ'} → Spine~ Δ~ δ δ' → Ty~ (Y δ) (Y' δ')}
    → {f : (δ : Spine Δ) → Tm (Y δ)} {f' : (δ' : Spine Δ') → Tm (Y' δ')}
    → (f~ : ∀ {δ δ'} → (δ~ : Spine~ Δ~ δ δ') → Tm~ (Y~ δ~) (f δ) (f' δ'))
    → Tm~ (Πs~ Δ~ Y~) (lams f) (lams f')
  lams~ {Δ~ = ∙~} f~ = f~ []~
  lams~ {Δ~ = ext~ A~ Δ~} f~ = lam~ (λ a~ → lams~ (λ δ~ → f~ (_,~_ {Δ~ = Δ~} a~ δ~) ))

  apps : Tm (Πs Δ Y) → (δ : Spine Δ) → Tm (Y δ)
  apps {Δ = ∙} t [] = t
  apps {Δ = ext A Δ} t (a , δ) = apps (app t a) δ
  
  apps~ : ∀ {Δ Δ'} {Δ~ : Tel~ Δ Δ'} {Y : Spine Δ → Ty} {Y' : Spine Δ' → Ty}
    → {Y~ : ∀ {δ δ'} → Spine~ Δ~ δ δ' → Ty~ (Y δ) (Y' δ')}
    → {t : Tm (Πs Δ Y)} {t' : Tm (Πs Δ' Y')}
    → (t~ : Tm~ (Πs~ Δ~ Y~) t t')
    → {δ : Spine Δ} {δ' : Spine Δ'}
    → (δ~ : Spine~ Δ~ δ δ')
    → Tm~ (Y~ δ~) (apps t δ) (apps t' δ')
  apps~ {Δ~ = ∙~} t~ []~ = t~
  apps~ {Δ~ = ext~ A~ Δ~} {Y~ = Y~} t~ (a~ ,~ δ~) =
    apps~ {Y~ = λ δ~ → Y~ (_,~_ {Δ~ = Δ~} a~ δ~)}
      (app~ {B~ = λ a~ → Πs~ (Δ~ a~) (λ δ~ → Y~ (_,~_ {Δ~ = Δ~} a~  δ~))} t~ a~) δ~

  Πs-β : ∀ {Δ}
    {B : Spine Δ → Ty}
    {B~ : ∀ {δ δ'} → Spine~ refl-Tel δ δ' → Ty~ (B δ) (B δ')}
    {f : (δ : Spine Δ) → Tm (B δ)} {δ : Spine Δ}
    → Tm~ refl-Ty (apps {Δ = Δ} (lams f) δ) (f δ)
  Πs-β {Δ = ∙} {B} {f} {δ = []} = refl-Tm
  Πs-β {Δ = ext A Δ} {B} {B~} {f} {δ = (a , δ)} = 
    trans-Tm
      (apps~ {Y~ = λ δ~ → B~ (_,~_ {Δ~ = λ a~ → {!   !}} refl-Tm δ~)}
        (Π-β {f = λ a' → lams (λ δ' → f (a' , δ'))})
        (refl-Spine {δ = δ}))
      (Πs-β {Δ = Δ a} {B~ = λ δ~ → B~ (_,~_ {Δ~ = λ a~ → {!   !}} refl-Tm δ~)} {f = λ δ' → f (a , δ')} {δ = δ})
  
record ⊤-structure (T : TT) : Set1 where
  open TT T
  field
    ⊤ : Ty
    tt : Tm ⊤
    ⊤-η : ∀ {t} → Tm~ refl-Ty tt t

record Σ-structure (T : TT) : Set1 where
  open TT T
  field
    Σ : (A : Ty) → (Tm A → Ty) → Ty
    pair : {A : Ty} → {B : Tm A → Ty}
      → (a : Tm A)
      → (b : Tm (B a))
      → Tm (Σ A B)
    fst : {A : Ty} → {B : Tm A → Ty}
      → Tm (Σ A B)
      → Tm A
    snd : {A : Ty} → {B : Tm A → Ty}
      → (p : Tm (Σ A B))
      → Tm (B (fst p))

    Σ-β-fst : ∀ {A} {B : Tm A → Ty} {a : Tm A} {b : Tm (B a)}
      → Tm~ refl-Ty (fst (pair {B = B} a b)) a
    Σ-β-snd : ∀ {A} {B : Tm A → Ty} {a : Tm A} {b : Tm (B a)}
      → Tm~ refl-Ty (snd (pair a b)) b
    Σ-η : ∀ {A} {B : Tm A → Ty} {p : Tm (Σ A B)}
      → Tm~ refl-Ty (pair (fst p) (snd p)) p

  syntax Σ A (λ x → B) = [ x ∶ A ] × B


module Σs-notation (T : TT) {{T-Σ : Σ-structure T}} {{T-⊤ : ⊤-structure T}} where
  open TT T
  open Σ-structure T-Σ
  open ⊤-structure T-⊤
  open Tel-construction T

  Σs : Tel → Ty
  Σs ∙ = ⊤
  Σs (ext A Δ) = Σ A (λ a → Σs (Δ a))

    
record Id-structure (T : TT) : Set1 where
  open TT T
  field
    Id : {A : Ty} → Tm A → Tm A → Ty
    rfl : {A : Ty} → (a : Tm A) → Tm (Id a a)
    J : {A : Ty}
        → (P : (a : Tm A) → (b : Tm A) → Tm (Id a b) → Ty)
        → ((a : Tm A) → Tm (P a a (rfl a)))
        → {a : Tm A} → {b : Tm A} → (p : Tm (Id a b))
        → Tm (P a b p)
    Id-β : ∀ {A} {P} {a} {r : (a : Tm A) → Tm (P a a (rfl a))}
      → Tm~ refl-Ty (J P r (rfl a)) (r a)
  