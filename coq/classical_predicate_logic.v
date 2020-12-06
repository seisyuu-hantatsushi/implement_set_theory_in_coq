From mathcomp Require Import ssreflect.

Require Import  predicate_logic .

Axiom DoubleNegativeElimination: forall A:Prop, ~~A -> A.

Theorem LawOfExcludeMiddle: forall P:Prop, P \/ ~P.
Proof.
  move => P.
  apply DoubleNegativeElimination.
  apply DoubleNegativeLawOfExcludeMiddle.
Qed.

Require Export predicate_logic.
