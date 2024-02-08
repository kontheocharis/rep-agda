open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.Product hiding (map)
open import Function
open import Relation.Binary.PropositionalEquality using (_≡_)

data Ty0 (I : Set) : Set where

-- We actually need a term structure here
data Ty1 (I : Set) : Set1 where
  end : I -> Ty1 I
  σ : (S : Set) -> (S -> Ty1 I) -> Ty1 I
  node_×_ : I -> Ty1 I -> Ty1 I
  quot : Ty0 I -> Ty1 I

^_ : {I : Set} -> Ty0 I -> Ty1 I
^ R = {!   !}

[[_]] : {I : Set} -> Ty1 I -> (I -> Set) -> (I -> Set)
[[ end i' ]] I i = (i ≡ i')
[[ σ S t ]] I i = Σ S (λ s -> [[ t s ]] I i)
[[ node i' × U ]] I i = I i' × [[ U ]] I i
[[ quot R ]] I i = {!   !}

data Fix {I : Set} (T : Ty1 I) (i : I) : Set where
  <_> : [[ T ]] (Fix T) i -> Fix T i

[_] : {I : Set} -> Ty1 I -> I -> Set
[ T ] = Fix T

-- map : {T : Ty1} -> {I J : Set} -> (I -> J) -> [[ T ]] J -> [[ T ]] J
-- map f (< t >) = < map f t >

_~>_ : {I : Set} -> (I -> Set) -> (I -> Set) -> Set
_~>_ {I} A B = {i : I} -> A i -> B i

Morph : {I : Set} -> Ty1 I -> Ty1 I -> Set
Morph {I} T B = [ T ] ~> [ B ]

Alg : {I : Set} -> Ty1 I -> Ty1 I -> Set
Alg T B = [[ T ]] [ B ] ~> [ B ]

CoAlg : {I : Set} -> Ty1 I -> Ty1 I -> Set
CoAlg T B = [ B ] ~> [[ T ]] [ B ]

fold :  {I : Set} -> {T B : Ty1 I} -> (Alg T B) -> Morph T B
fold = {!   !}

unfold : {I : Set} -> {T B : Ty1 I} -> (CoAlg T B) -> Morph B T
unfold = {!   !}


record Repr {I : Set} (T : Ty1 I) : Set1 where
  field
    R : Ty0 I
    B : Ty1 I

    wrap : Alg T B
    unwrap : CoAlg T B

    build : Morph B (^ R)
    unbuild : Morph (^ R) (B)

open Repr

repr : {I : Set} -> {T : Ty1 I} -> {{r : Repr T}} -> Morph T (^ (R r))
repr {{r}} = (build r) ∘ fold (wrap r)

unrepr : {I : Set} -> {T : Ty1 I} -> {{r : Repr T}} -> Morph (^ (R r)) T
unrepr {{r}} = unfold (unwrap r) ∘ (unbuild r)



