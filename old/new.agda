
mutual
  data Ctx : Set where
    ∙ : Ctx
    _,_ : Ctx -> Ctx -> Ctx

  data Sub : Ctx -> Ctx -> Set

  data Ty₀ : Ctx -> Set

  data Ty₁ : Ctx -> Set

  _[_] : {Γ : Ctx} -> {Δ : Ctx} -> Ty₀ Δ -> Sub Γ Δ -> Ty₀ Γ

  data Sub where
    id : {Γ : Ctx} -> Sub Γ Γ
    ⟨_,_⟩₀ : {Γ : Ctx} -> {Δ : Ctx} -> (γ : Sub Γ Δ) -> {A : Ty₀ Δ} -> (t : Tm₀ Γ (A [ γ ])) -> Sub Γ (Δ , A)

  data Tm₀ : (Γ : Ctx) -> Ty₀ Γ -> Set where

  data Tm₁ : (Γ : Ctx) -> Ty₁ Γ -> Set where

