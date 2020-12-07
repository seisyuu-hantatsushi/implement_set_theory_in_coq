From mathcomp Require Import ssreflect.

Require Import  predicate_logic .

Axiom DoubleNegativeElimination: forall A:Prop, ~~A -> A.

Theorem LawOfExcludeMiddle: forall P:Prop, P \/ ~P.
Proof.
  move => P.
  apply DoubleNegativeElimination.
  apply DoubleNegativeLawOfExcludeMiddle.
Qed.

(* If P implies Q, then not P or Q are true *)
Theorem If_P_implies_Q_then_notP_or_Q:
  forall P Q:Prop, (P -> Q) -> (~P \/ Q).
Proof.
  move => P Q H0.
  move: (LawOfExcludeMiddle P).
  case.
  move => H1.
  right.
  apply H0.
  apply H1.
  move => H1.
  left.
  apply H1.
Qed.

Theorem PeircesLaw: forall P Q:Prop, ((P -> Q) -> P) -> P.
Proof.
  move => P Q H0.
  apply DoubleNegativeElimination.
  move => H1.
  have: (P -> Q) -> P.
  move => H2.
  move: H1.
  case.
  apply H0.
  apply H2.
  move => H2.
  apply H1.
  apply H0.
  move => H3.
  move: H1.
  case.
  apply H3.
Qed.

Require Export predicate_logic.
