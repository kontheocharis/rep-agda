// Sorts

constant symbol Ty : TYPE;

constant symbol Tm : Ty → TYPE;

// constant symbol Tel : TYPE;

// constant symbol Spine : Tel → TYPE;

// Types

constant symbol U : Ty;

injective symbol El : Tm U → Ty;

constant symbol Π' (A : Ty) (B : Tm A → Ty) : Ty;

notation Π' quantifier;

constant symbol = [A : Ty] (a : Tm A) (b : Tm A) : Ty;

notation = infix left 10;

constant symbol ⊤ : Ty;

constant symbol Σ' (A : Ty) (B : Tm A → Ty) : Ty;

notation Σ' quantifier;

// // Telescopes

// constant symbol ∙ : Tel;

// constant symbol ▷ (A : Ty) (Δ : Tm A → Tel) : Tel;

// notation ▷ infix right 10;

// // Spines

// constant symbol  ̇ : Spine ∙;

// constant symbol ⊳ [A Δ] : Π a : Tm A , Spine (Δ a) → Spine (A ▷ Δ);

// notation ⊳ quantifier;

// Terms

symbol lam [A B] (x : Π a : Tm A , Tm (B a)) : Tm (Π' A B);

symbol app [A B] (f : Tm (Π' A B)) (x : Tm A) : Tm (B x);

constant symbol refl [A] (a : Tm A) : Tm (a = a);

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



