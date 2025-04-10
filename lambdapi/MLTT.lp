// Sorts

constant symbol Ty : TYPE;
constant symbol Tm : Ty → TYPE;

// Types

constant symbol U : Ty;

injective symbol El : (Tm U) → Ty;

constant symbol Π' (A : Ty) (B : (Tm A) → Ty) : Ty;

notation Π' quantifier;

constant symbol = [A : Ty] (a : (Tm A)) (b : (Tm A)) : Ty;

notation = infix left 10;

constant symbol ⊤ : Ty;

constant symbol Σ' (A : Ty) (B : (Tm A) → Ty) : Ty;

notation Σ' quantifier;

symbol lam [A B] (x : Π a : (Tm A) , (Tm (B a))) : (Tm (Π' A B));

symbol app [A B] (f : (Tm (Π' A B))) (x : (Tm A)) : (Tm (B x));

constant symbol refl [A] (a : (Tm A)) : (Tm (a = a));

symbol J [A]
  [P : Π a : Tm A , Π b : Tm A , Π p : Tm (a = b) , Ty]
  (reflP : Π a : Tm A , Tm (P a a (refl a)))
  (a : Tm A) (b : Tm A) (p : Tm (a = b)) : Tm (P a b p);

constant symbol tt : Tm ⊤;

symbol pair [A B] (a : Tm A) (b : Tm (B a)) : Tm (Σ' A B);

symbol fst [A B] (p : Tm (Σ' A B)) : Tm A;

symbol snd [A B] (p : Tm (Σ' A B)) : Tm (B (fst p));

// Beta
rule app (lam $f) $x ↪ $f $x;

// Eta
rule lam [$A] [$B] (λ x , app [$A.[]] [$B.[]] $f.[] x) ↪ $f;

// Pair-fst

rule fst (pair $a $b) ↪ $a;

// Pair-snd

rule snd (pair $a $b) ↪ $b;

// Pair-eta

rule pair [$A] [$B] (fst $p) (snd [$A] [$B] $p) ↪ $p;

// J-elim

rule J $reflP $a $a (refl $a) ↪ $reflP $a;



// Motive and methods

  // (TyM : SORT)
  // (TmM : EL TyM → SORT)
  // (UM : EL TyM)
  // (ElM : EL (TmM UM) → EL TyM)
  // (ΠM : Π A : EL TyM , (EL (TmM A) → EL TyM) → EL TyM)
  // (=M : Π A : EL TyM , EL (TmM A) → EL (TmM A) → EL TyM)
  // (⊤M : EL TyM)
  // (ΣM : Π A : EL TyM , (EL (TmM A) → EL TyM) → EL TyM)

