open import Agda.Builtin.Nat using (Nat)

Stage : Set
Stage = Nat

interleaved mutual

  data Ctx : Set

  data Ty : Stage -> Ctx -> Set

  data Var : Stage -> Ctx -> Set

  data Tm : ∀ {Γ l} -> Ty l Γ -> Set

  var-ty : ∀ {Γ l} -> Var l Γ -> Ty l Γ

  data Ctx where
    ∅ : Ctx
    _,_ : (Γ : Ctx) {l : Stage} -> Ty l Γ -> Ctx

  weaken-ty : ∀ {Γ l m} {W : Ty m Γ} -> Ty l Γ -> Ty l (Γ , W)

  weaken-tm : ∀ {Γ l m} {W : Ty m Γ} {T : Ty l Γ} -> Tm T -> Tm (weaken-ty {Γ} {l} {m} {W} T)

  sub-ty : ∀ {Γ l} {T : Ty l Γ} -> Ty l (Γ , T) -> Tm T -> Ty l Γ

  data Ty where
    pi : ∀ {Γ} -> (T : Ty 1 Γ) -> (R : Ty 1 (Γ , T)) -> Ty 1 Γ
    sig : ∀ {Γ} -> (T : Ty 1 Γ) -> (R : Ty 1 (Γ , T)) -> Ty 1 Γ
    eq : ∀ {Γ} {T : Ty 1 Γ} -> (t1 t2 : Tm T) -> Ty 1 Γ
    univ : ∀ {Γ} -> Ty 1 Γ
    el : ∀ {Γ} -> Tm (univ {Γ}) -> Ty 1 Γ
    unit : ∀ {Γ} -> Ty 1 Γ
    ^_ : ∀ {Γ} -> (T : Ty 0 Γ) -> Ty 1 Γ

  data Tm where

  data Var where
    z : ∀ {Γ l} {T : Ty l Γ} -> Var l (Γ , T)
    s : ∀ {Γ l m} {T : Ty m Γ} -> Var l Γ -> Var l (Γ , T)

  weaken-ty = {!   !}
  weaken-tm = {!   !}
  sub-ty = {!   !}

  var-ty {Γ = (Γ , T)} z = weaken-ty T
  var-ty {Γ = (Γ , T)} (s v) = weaken-ty (var-ty v)

  data Tm where
    lam : ∀ {Γ} (T : Ty 1 Γ) {R : Ty 1 (Γ , T)} -> (r : Tm R) -> Tm (pi T R)
    app : ∀ {Γ} {T : Ty 1 Γ} {R : Ty 1 (Γ , T)} -> (t : Tm (pi T R)) -> (r : Tm T) -> Tm (sub-ty R r)
    pair : ∀ {Γ} {T : Ty 1 Γ} {R : Ty 1 (Γ , T)} -> (t : Tm T) -> (r : Tm R) -> Tm (sig T R)
    refl : ∀ {Γ} {T : Ty 1 Γ} -> (t : Tm T) -> Tm (eq t t)
    ty : ∀ {Γ} (T : Ty 1 Γ) -> Tm (univ {Γ})
    quot : ∀ {Γ} {T : Ty 0 Γ} -> Tm T -> Tm (^ T)
    var : ∀ {Γ} (v : Var 1 Γ) -> Tm (var-ty v)

  data Desc {Γ : Ctx} (I : Ty 1 Γ) : Set where
    leaf : Tm I -> Desc I
    choice : (S : Ty 1 Γ) -> Desc {Γ = (Γ , S)} (weaken-ty I) -> Desc I
    node : Tm I -> Desc I -> Desc I

  interp : ∀ {Γ} {I : Ty 1 Γ} -> Desc I -> Tm (pi I univ) -> Tm (pi I univ)
  interp {Γ} {I} (leaf t) F = lam I (ty (eq (var z) (weaken-tm t)))
  interp {Γ} {I} (choice S f) F = lam I (ty (sig (weaken-ty S) (el ({!   !}))))
  interp {Γ} {I} (node t d) F = lam I (ty {!   !})
  -- [ choice T f ] F =
  -- [ node t d ] F =

