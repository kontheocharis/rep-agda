require RepForm.DataTT as D;
require RepForm.MLTT as M;

symbol RTy : D.Ty → M.Ty;

symbol RTy' : M.Ty → D.Ty;

rule RTy' (RTy $A) ↪ $A;

symbol RTm [A] : D.Tm A → M.Tm (RTy A);

symbol RTm' [A] : M.Tm A → D.Tm (RTy' A);

rule RTm' (RTm $t) ↪ $t;

rule RTy D.U ↪ M.U;

rule RTy (D.El $t) ↪ M.El (RTm $t);

rule RTy D.⊤ ↪ M.⊤;

rule RTy ((D.=) [$A] $a  $b) ↪ (M.=) (RTm $a) (RTm $b);

rule RTy (D.Π' $A (λ x, $B.[x])) ↪ M.Π' (RTy $A) (λ x, RTy ($B.[RTm' x]));



