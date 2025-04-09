{-# OPTIONS --prop --without-K --rewriting #-}

module MLTTCon where

import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence)

data Con  : Set
data Ty   : Con → Set
data Sub  : Con → Con → Set
data Tm   : ∀ Γ → Ty Γ → Set
data Con~ : Con → Con → Prop
data Ty~  : ∀ {Γ₀ Γ₁} → Con~ Γ₀ Γ₁ → Ty Γ₀ → Ty Γ₁ → Prop
data Sub~ : ∀ {Γ₀ Γ₁ Δ₀ Δ₁} → Con~ Γ₀ Γ₁ → Con~ Δ₀ Δ₁ → Sub Γ₀ Δ₀ → Sub Γ₁ Δ₁ → Prop
data Tm~  : ∀ {Γ₀ Γ₁ A₀ A₁}(Γ₂ : Con~ Γ₀ Γ₁) → Ty~ Γ₂ A₀ A₁ → Tm Γ₀ A₀ → Tm Γ₁ A₁ → Prop

variable
  Γ Δ Γ₀ Γ₁ Δ₀ Δ₁ θ θ₀ θ₁ : Con
  A B C A₀ A₁ B₀ B₁       : Ty _
  t u v t₀ t₁ u₀ u₁       : Tm _ _
  σ δ ν σ₀ σ₁ δ₀ δ₁ ν₀ ν₁ : Sub _ _
  Γ₂                      : Con~ Γ₀ Γ₁
  Δ₂                      : Con~ Δ₀ Δ₁
  θ₂                      : Con~ θ₀ θ₁
  A₂                      : Ty~ _ A₀ A₁
  B₂                      : Ty~ _ B₀ B₁

infixl 4 _,_
infixr 5 _∘_
infix 5 _[_]

data Con where
  ∙   : Con
  _,_ : ∀ Γ → Ty Γ → Con
  
<_> : Tm Γ A → Sub Γ (Γ , A)

p' : Sub (Γ , A) Γ 

data Ty where
  coe  : Con~ Γ₀ Γ₁ → Ty Γ₀ → Ty Γ₁

  ------------------------------------------------------------
  _[_] : Ty Δ → Sub Γ Δ → Ty Γ
  U    : Ty Γ
  Π    : (A : Ty Γ) → Ty (Γ , A) → Ty Γ
  El   : Tm Γ U → Ty Γ

  ⊤    : Ty Γ
  Σ    : (A : Ty Γ) → Ty (Γ , A) → Ty Γ
  Id   : {A : Ty Γ} → Ty (Γ , A , A [ p' ])

data Sub where
  coe : Con~ Γ₀ Γ₁ → Con~ Δ₀ Δ₁ → Sub Γ₀ Δ₀ → Sub Γ₁ Δ₁

  ------------------------------------------------------------
  id  : Sub Γ Γ
  _∘_ : Sub Δ θ → Sub Γ Δ → Sub Γ θ
  ε   : Sub Γ ∙
  p   : Sub (Γ , A) Γ
  _,_ : (σ : Sub Γ Δ) → Tm Γ (A [ σ ]) → Sub Γ (Δ , A)
  
p' = p

data Tm where
  coe  : ∀ Γ₂ → Ty~ Γ₂ A₀ A₁ → Tm Γ₀ A₀ → Tm Γ₁ A₁

  ------------------------------------------------------------
  _[_] : Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ])
  q    : Tm (Γ , A) (A [ p ])
  lam  : Tm (Γ , A) B → Tm Γ (Π A B)
  app  : Tm Γ (Π A B) → Tm (Γ , A) B

  tt   : Tm Γ ⊤
  pair : (a : Tm Γ A) → Tm Γ (B [ < a > ]) → Tm Γ (Σ A B)
  fst  : Tm Γ (Σ A B) → Tm Γ A
  snd  : (p : Tm Γ (Σ A B)) → Tm Γ (B [ < fst p > ])

  refl : Tm (Γ , A) (Id [ < q > ])
  J   : {A : Ty Γ} → (P : Ty (Γ , A , A [ p ] , Id)) → Tm (Γ , A) (P [ < q > , refl ]) → Tm (Γ , A , A [ p ] , Id) P

data Con~ where
  rfl : Con~ Γ Γ
  sym : Con~ Γ Δ → Con~ Δ Γ
  trs : Con~ Γ Δ → Con~ Δ θ → Con~ Γ θ

  ------------------------------------------------------------
  ∙   : Con~ ∙ ∙
  _,_ : ∀ Γ₂ → Ty~ Γ₂ A₀ A₁ → Con~ (Γ₀ , A₀) (Γ₁ , A₁)

p~ : Sub~ (Γ₂ , A₂) Γ₂ p p 

wk : (σ : Sub Γ Δ) → Sub (Γ , A [ σ ]) (Δ , A)

data Ty~ where
  rfl  : Ty~ rfl A A
  sym  : ∀ {Γ₀₁} → Ty~ Γ₀₁ A B → Ty~ (sym Γ₀₁) B A
  trs  : ∀ {Γ₀₁ Γ₁₂} → Ty~ Γ₀₁ A B → Ty~ Γ₁₂ B C → Ty~ (trs Γ₀₁ Γ₁₂) A C
  coh  : ∀ Γ₂ A → Ty~ {Γ₀}{Γ₁} Γ₂ A (coe Γ₂ A)

  ------------------------------------------------------------
  _[_] : Ty~ Δ₂ A₀ A₁ → Sub~ Γ₂ Δ₂ σ₀ σ₁ → Ty~ Γ₂ (A₀ [ σ₀ ]) (A₁ [ σ₁ ])
  U    : Ty~ Γ₂ U U
  Π    : (A₂ : Ty~ Γ₂ A₀ A₁) → Ty~ (Γ₂ , A₂) B₀ B₁ → Ty~ Γ₂ (Π A₀ B₀) (Π A₁ B₁)
  El   : Tm~ Γ₂ U t₀ t₁ → Ty~ Γ₂ (El t₀) (El t₁)

  ⊤    : Ty~ Γ₂ ⊤ ⊤
  Σ    : (A₂ : Ty~ Γ₂ A₀ A₁) → Ty~ (Γ₂ , A₂) B₀ B₁ → Ty~ Γ₂ (Σ A₀ B₀) (Σ A₁ B₁)
  Id   : {A₂ : Ty~ Γ₂ A₀ A₁} → Ty~ (Γ₂ , A₂ , A₂ [ p~ {A₂ = A₂} ]) (Id {A = A₀}) (Id {A = A₁})

  ------------------------------------------------------------
  [id] : Ty~ rfl (A [ id ]) A
  [∘]  : Ty~ rfl (A [ σ ∘ δ ]) (A [ σ ] [ δ ])
  U[]  : Ty~ rfl (U [ σ ]) U
  Π[]  : Ty~ rfl (Π A B [ σ ]) (Π (A [ σ ]) (B [ wk σ ]))
  El[] : Ty~ rfl (El t [ σ ]) (El (coe rfl U[] (t [ σ ])))
  
  ⊤[]  : Ty~ rfl (⊤ [ σ ]) ⊤
  Σ[]  : Ty~ rfl (Σ A B [ σ ]) (Σ (A [ σ ]) (B [ wk σ ]))
  Id[] : Ty~ (rfl , rfl , A₂) ((Id {A = A}) [ wk (wk σ) ]) (Id {A = A [ σ ]})

wk σ = σ ∘ p , coe rfl (sym [∘]) q
  
< a > = id , coe rfl (sym [id]) a
  
<_>~ : Tm~ Γ₂ A₂ t u → Sub~ Γ₂ (Γ₂ , A₂) (< t >) (< u >)

data Sub~ where
  rfl  : Sub~ rfl rfl σ σ
  sym  : ∀ {Γ₀₁ Δ₀₁} → Sub~ Γ₀₁ Δ₀₁ σ δ → Sub~ (sym Γ₀₁) (sym Δ₀₁) δ σ
  trs  : ∀ {Γ₀₁ Δ₀₁ Γ₁₂ Δ₁₂} → Sub~ Γ₀₁ Δ₀₁ σ δ → Sub~ Γ₁₂ Δ₁₂ δ ν → Sub~ (trs Γ₀₁ Γ₁₂) (trs Δ₀₁ Δ₁₂) σ ν
  coh  : ∀ Γ₂ Δ₂ σ → Sub~ {Γ₀}{Γ₁} {Δ₀}{Δ₁} Γ₂ Δ₂ σ (coe Γ₂ Δ₂ σ)

  ------------------------------------------------------------
  id  : Sub~ Γ₂ Γ₂ id id
  _∘_ : Sub~ Δ₂ θ₂ σ₀ σ₁ → Sub~ Γ₂ Δ₂ δ₀ δ₁ → Sub~ Γ₂ θ₂ (σ₀ ∘ δ₀) (σ₁ ∘ δ₁)
  ε   : Sub~ Γ₂ ∙ ε ε
  p   : Sub~ (Γ₂ , A₂) Γ₂ p p
  _,_ : (σ₂ : Sub~ Γ₂ Δ₂ σ₀ σ₁) → Tm~ Γ₂ (A₂ [ σ₂ ]) t₀ t₁ → Sub~ Γ₂ (Δ₂ , A₂) (σ₀ , t₀) (σ₁ , t₁)

  ------------------------------------------------------------
  εη  : Sub~ rfl rfl σ ε
  idl : Sub~ rfl rfl (id ∘ σ) σ
  idr : Sub~ rfl rfl (σ ∘ id) σ
  ass : Sub~ rfl rfl (σ ∘ δ ∘ ν) ((σ ∘ δ) ∘ ν)
  p∘  : Sub~ rfl rfl (p ∘ (σ , t)) σ
  pq  : Sub~ rfl rfl (p , q) (id {Γ , A})
  ,∘  : Sub~ rfl rfl ((σ , t) ∘ δ) (σ ∘ δ , coe rfl (sym [∘]) (t [ δ ]))
  idp  : Sub~ rfl rfl (p ∘ σ , coe rfl (sym [∘]) (q [ σ ])) σ
  
p~ {A₂ = A₂} = p {A₂ = A₂}

<>-comm : Sub~ rfl rfl (< t > ∘ σ) (wk σ ∘ < t [ σ ] >)

<>-swap-Ty : Ty~ rfl ((A [ < t > ]) [ σ ]) ((A [ wk σ ]) [ < t [ σ ] > ])
<>-swap-Ty = trs (trs (sym [∘]) (rfl [ <>-comm ])) [∘]

data Tm~ where
  rfl  : Tm~ rfl rfl t t
  sym  : ∀ {Γ₀₁ A₀₁} → Tm~ Γ₀₁ A₀₁ t u → Tm~ (sym Γ₀₁) (sym A₀₁) u t
  trs  : ∀ {Γ₀₁ A₀₁ Γ₁₂ A₁₂} → Tm~ Γ₀₁ A₀₁ t u → Tm~ Γ₁₂ A₁₂ u v → Tm~ (trs Γ₀₁ Γ₁₂) (trs A₀₁ A₁₂) t v
  coh  : ∀ Γ₂ A₂ t → Tm~ {Γ₀}{Γ₁} {A₀}{A₁} Γ₂ A₂ t (coe Γ₂ A₂ t)

  ------------------------------------------------------------
  _[_] : Tm~ Δ₂ A₂ t₀ t₁ → (σ₂ : Sub~ Γ₂ Δ₂ σ₀ σ₁) → Tm~ Γ₂ (A₂ [ σ₂ ]) (t₀ [ σ₀ ]) (t₁ [ σ₁ ])
  q    : Tm~ (Γ₂ , A₂) (A₂ [ p {A₂ = A₂} ]) q q
  lam  : Tm~ (Γ₂ , A₂) B₂ t₀ t₁ → Tm~ Γ₂ (Π A₂ B₂) (lam t₀) (lam t₁)
  app  : Tm~ Γ₂ (Π A₂ B₂) t₀ t₁ → Tm~ (Γ₂ , A₂) B₂ (app t₀) (app t₁)

  tt   : Tm~ Γ₂ ⊤ tt tt
  pair : Tm~ Γ₂ (Σ A₂ B₂) (pair t₀ u₀) (pair t₁ u₁)
  fst  : Tm~ Γ₂ (Σ A₂ B₂) t₀ t₁ → Tm~ Γ₂ A₂ (fst t₀) (fst t₁)
  snd  : (t₂ : Tm~ Γ₂ (Σ A₂ B₂) t₀ t₁) → Tm~ Γ₂ (B₂ [ <_>~ {A₂ = A₂} (fst {B₂ = B₂} t₂) ]) (snd t₀) (snd t₁)
  
  refl : Tm~ Γ₂ (Id {A₂ = A₂} [ < q {A₂ = A₂} >~ ]) (refl {A = A₀}) (refl {A = A₁})
  J   : {A₂ : Ty~ Γ₂ A₀ A₁} → ∀ {P₀ P₁} → (P : Ty~ (Γ₂ , A₂ , A₂ [ p {A₂ = A₂} ] , Id {A₂ = A₂}) P₀ P₁)
     → ∀ {t₀ t₁}
     → (t₂ : Tm~ (Γ₂ , A₂) (P [ _,_ {A₂ = Id {A₂ = A₂}} (< q {A₂ = A₂} >~) (refl {A₂ = A₂}) ]) t₀ t₁)
     → Tm~ (Γ₂ , A₂ , A₂ [ p {A₂ = A₂} ] , Id {A₂ = A₂}) P (J P₀ t₀) (J P₁ t₁)

  ------------------------------------------------------------
  [id] : Tm~ rfl [id] (t [ id ]) t
  [∘]  : Tm~ rfl [∘] (t [ σ ∘ δ ]) (t [ σ ] [ δ ])
  q[]   : Tm~ rfl (trs (sym [∘]) (rfl [ p∘ ])) (q [ σ , t ]) t
  lam[] : Tm~ rfl Π[] (lam t [ σ ]) (lam (t [ wk σ ]))

  tt[] : Tm~ rfl ⊤[] (tt [ σ ]) tt
  pair[] : Tm~ rfl Σ[] (pair t u [ σ ]) (pair (t [ σ ]) (coe rfl <>-swap-Ty (u [ σ ])))
  fst[] : Tm~ rfl rfl (fst t [ σ ]) (fst (coe rfl Σ[] (t [ σ ])))
  snd[] : Tm~ rfl rfl (snd t [ σ ]) (coe rfl (trs (rfl [ _,_ {A₂ = rfl} id (trs (sym (coh _ _ _)) (trs (sym fst[]) (coh _ _ _)))]) (sym <>-swap-Ty)) (snd (coe rfl Σ[] (t [ σ ]))))

  Πβ    : Tm~ rfl rfl (app (lam t)) t
  Πη    : Tm~ rfl rfl (lam (app t)) t

  ttη   : Tm~ rfl rfl t tt
  pairβ₁ : Tm~ rfl rfl (fst (pair t u)) t
  pairβ₂ : Tm~ rfl (A₂ [ < pairβ₁ >~ ]) (snd (pair t u)) u
  pairη : Tm~ rfl rfl (pair (fst t) (snd t)) t

  -- Jelim : ∀ {P u} → Tm~ rfl rfl (J P u [ {!   !} ]) {!   !}
  
<_>~ {A₂ = A₂} {t = t} {u = u} a = _,_ {A₂ = A₂} id (trs (trs (sym (coh rfl (sym [id]) t)) a) (coh rfl (sym [id]) u))

<>-comm {t = t} {σ = σ} = {!   !} -- trs ,∘ (trs (trs idl rfl , (trs (sym (coh rfl _ _)) (trs ({!   !}) (coh rfl _ _)))) (sym ,∘))

{-# BUILTIN REWRITE Sub~ #-}
{-# BUILTIN REWRITE Ty~ #-}
{-# BUILTIN REWRITE Tm~ #-}

[][]'-Ty : Ty~ rfl  ((A [ σ ]) [ δ ]) (A [ σ ∘ δ ])
[][]'-Ty = sym [∘]

[][]'-Tm : Tm~ rfl (sym [∘]) ((t [ σ ]) [ δ ]) (t [ σ ∘ δ ])
[][]'-Tm = sym [∘]

q[]' : Tm~ rfl (trs (sym [∘]) (rfl [ p∘ ])) (q [ σ , t ]) t
q[]' = q[]

[id]'-Ty : Ty~ rfl (A [ id ]) A
[id]'-Ty = [id]

[id]'-Tm : Tm~ rfl [id] (t [ id ]) t
[id]'-Tm = [id]

ass' : Sub~ rfl rfl ((σ ∘ δ) ∘ ν) (σ ∘ δ ∘ ν)
ass' = sym ass

,∘' :  Sub~ rfl rfl ((σ , t) ∘ δ) (σ ∘ δ , coe rfl (sym [∘]) (t [ δ ]))
,∘' = ,∘

idl' : Sub~ rfl rfl (id ∘ σ) σ
idl' = idl

idr' : Sub~ rfl rfl (σ ∘ id) σ
idr' = idr

p∘' : Sub~ rfl rfl (p ∘ (σ , t)) σ
p∘' = p∘

pq' : Sub~ rfl rfl (p , q) (id {Γ , A})
pq' = pq

idp' : Sub~ rfl rfl (p ∘ σ , coe rfl (sym [∘]) (q [ σ ])) σ
idp' = idp

remove-coe' : Sub~ rfl rfl (p ∘ σ , coe rfl (sym [∘]) (q [ σ ])) σ
remove-coe' = idp

{-# REWRITE [][]'-Ty [][]'-Tm q[]' [id]'-Ty [id]'-Tm ass' ,∘' idl' idr' p∘' pq' idp' remove-coe' #-}