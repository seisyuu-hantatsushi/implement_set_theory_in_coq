From mathcomp Require Import ssreflect.

Require Import predicate_logic.

Module ClassicalPredicatelLogic.
  Axiom DoubleNegativeElimination: forall A:Prop, ~~A -> A.

  Theorem DoubleNegativeLawOfExcludeMiddle: forall P:Prop, ~~(P \/ ~P).
  Proof.
    move => P H.
    apply H.
    right.
    move => H0.
    apply H.
    left.
    apply H0.
  Qed.

  Theorem LawOfExcludeMiddle: forall P:Prop, P \/ ~P.
  Proof.
    move => P.
    apply DoubleNegativeElimination.
    apply DoubleNegativeLawOfExcludeMiddle.
  Qed.

End ClassicalPropositionalLogic.

Export propositional_logic.
