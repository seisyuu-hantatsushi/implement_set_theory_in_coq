From mathcomp Require Import ssreflect.

(* 自同律 *)
Theorem LawOfIdentity: forall A:Prop, A <-> A.
Proof.
  rewrite /iff.
  split.
  apply.
  apply.
Qed.

Theorem NotFalse : ~False.
Proof.
  rewrite /not.
  apply.
Qed.

Theorem LawOfContradiction: forall P:Prop, ~(P /\ ~P).
Proof.
  move => P.
  case.
  move => H HN.
  apply HN.
  apply H.
Qed.

Theorem DoubleNegative: forall A:Prop, A -> ~~A.
Proof.
  rewrite /not.
  move => A HA HNA.
  apply HNA.
  apply HA.
Qed.

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

