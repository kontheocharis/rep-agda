# Custom Representations of Inductive Families

This is an Agda formalisation to accompany the paper "Custom Representations of
Inductive Families" by Constantine Theocharis and Edwin Brady.

MLTT and its developed extension DataTT are formalised by a shallow embedding in
Agda (as second-order generalised algebraic theories, using the propositional
equality of Agda for equations).

Then a model of DataTT is constructed, given a model of MLTT. By the universal
property of syntax (i.e. recursor), this should give a translation from DataTT to MLTT.

A version of the recursor for second-order syntax is postulated because Agda
cannot construct it through `data` definitions. See
https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2023.18 for some
details. This could be fully defined in Agda if first-order syntax with explicit
contexts was used, but it would make everything much more challenging because
the substitution calculus would need to be reasoned about manually.

This is a summary of the files:

- `TT/Utils.agda` : Some equality-related tools.
- `TT/Core.agda` : Definition of type theories.
- `TT/Base.agda` : Basic type formers: Pi, Sigma, Id etc.
- `TT/Tel.agda` : Telescopic extension of the syntax of type theory.
- `TT/Sig.agda` : Algebraic signatures over a type theory, used for specifying data types.
- `TT/Data.agda` : Type formers for adding data types to a type theory.
- `TT/Theories.agda` : Definition of MLTT and DataTT
- `TT/Translation.agda` : Translation from DataTT to MLTT.


We assume *function extensionality*, *axiom K* and make use of Agda's rewriting
system (but only on proven statements, not postulates.)