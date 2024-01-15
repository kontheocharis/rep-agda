open import Data.Unit
open import Data.Empty
open import Data.Nat

data Ty0 : Set where
  zero : Ty0
  one : Ty0

mutual
  data Ty1 : Set where
    zero : Ty1
    one : Ty1

  Interp : Ty1 -> Set
  Interp zero = ⊥
  Interp one = ⊤

quot : Ty0 -> Ty1
quot zero = zero
quot one = one

_over_ : Ty1 -> Ty1 -> Ty1
zero over B = zero
one over B = one

fold : {T : Ty1} -> {I : Ty1} -> (Interp (T over I) -> Interp I) -> Interp T -> Interp I
fold = {!   !}

unfold : {T : Ty1} -> {I : Ty1} -> (Interp I -> Interp (T over I)) -> Interp I -> Interp T
unfold = {!   !}


record Repr (T : Ty1) : Set where
  field
    R : Ty0
    I : Ty1

    wrap : Interp (T over I) -> Interp I
    unwrap : Interp (T over I) -> Interp (T over I)

    build : Interp I -> Interp (quot R)
    unbuild : Interp (quot R) -> Interp I

repr : {T : Ty1} -> {{r : Repr T}} -> Interp T -> Interp (quot Repr.R)
repr = Repr.build . Repr.wrap

unrepr : {T : Ty1} -> {{r : Repr T}} -> Interp (quot Repr.R) -> Interp T
unrepr = Repr.unwrap . Repr.unbuild



