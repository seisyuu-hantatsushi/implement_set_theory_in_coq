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

(* 矛盾律 *)
Theorem LawOfContradiction: forall P:Prop, ~(P /\ ~P).
Proof.
  move => P.
  case.
  move => H HN.
  apply HN.
  apply H.
Qed.

(* 二重否定 *)
Theorem DoubleNegative: forall A:Prop, A -> ~~A.
Proof.
  rewrite /not.
  move => A HA HNA.
  apply HNA.
  apply HA.
Qed.

(* 冪等律 *)
Theorem LawOfIdempotenceAtAnd: forall P:Prop, P /\ P <-> P.
Proof.
  move => P.
  rewrite /iff.
  split.
  case.
  move => HP.
  apply.
  move => HP.
  split.
  apply HP.
  apply HP.
Qed.

Theorem LawOfIdempotenceAtOr: forall P:Prop, P \/ P <-> P.
Proof.
  move => P.
  rewrite /iff.
  split.
  case.
  apply.
  apply.
  move => HP.
  right.
  apply HP.
Qed.

Theorem LawOfCommutativeAtAnd: forall A B:Prop, A /\ B <-> B /\ A.
Proof.
  move => A B.
  rewrite /iff.
  split; case; move => H0 H1; split.
  apply H1.
  apply H0.
  apply H1.
  apply H0.
Qed.

Theorem LawOfCommutativeAtOr: forall A B:Prop, A \/ B <-> B \/ A.
Proof.
  move => A B.
  rewrite /iff.
  split; case; move => H.
  right.
  apply H.
  left.
  apply H.
  right.
  apply H.
  left.
  apply H.
Qed.

Theorem LawOfAssociateAtAnd: forall A B C:Prop, (A /\ B) /\ C <-> A /\ (B /\ C).
Proof.
  move => A B C.
  rewrite /iff.
  split; case.
  case.
  move => HA HB HC.
  split.
  apply HA.
  split.
  apply HB.
  apply HC.
  move => HA.
  case.
  move => HB HC.
  split.
  split.
  apply HA.
  apply HB.
  apply HC.
Qed.

Theorem LawOfAssociateAtOr: forall A B C:Prop, (A \/ B) \/ C <-> A \/ (B \/ C).
Proof.
  move => A B C.
  rewrite /iff.
  split; case.
  case; move => H.
  left.
  apply H.
  right.
  left.
  apply H.
  move => H.
  right.
  right.
  apply H.
  move => H.
  left.
  left.
  apply H.
  case; move => H.
  left.
  right.
  apply H.
  right.
  apply H.
Qed.

Theorem LawOfDistributiveByOr: forall A B C:Prop, (A /\ B) \/ C <-> (A \/ C) /\ (B \/ C).
Proof.
  move => A B C.
  rewrite /iff.
  split.
  case.
  case.
  move => HA HB.
  split; left.
  apply HA.
  apply HB.
  move => HC.
  split; right; apply HC.
  case; move => H0 H1.
  case H0; move => H2.
  case H1; move => H3.
  left.
  split.
  apply H2.
  apply H3.
  right.
  apply H3.
  right.
  apply H2.
Qed.

Theorem LawOfDistributiveByAnd: forall A B C:Prop, (A \/ B) /\ C <-> (A /\ C) \/ (B /\ C).
Proof.
  move => A B C.
  rewrite /iff.
  split; case; case; move => H0 H1.
  left.
  split.
  apply H0.
  apply H1.
  right.
  split.
  apply H0.
  apply H1.
  split.
  left.
  apply H0.
  apply H1.
  split.
  right.
  apply H0.
  apply H1.
Qed.

Theorem LawOfAbsorptionToOr: forall A B:Prop, (A /\ B) \/ A <-> A.
Proof.
  move => A B.
  rewrite /iff.
  split.
  case.
  case.
  move => HA HB.
  apply HA.
  apply.
  move => HA.
  right.
  apply HA.
Qed.

Theorem LawOfAbsorptionToAnd: forall A B:Prop, (A \/ B) /\ A <-> A.
Proof.
  move => A B.
  rewrite /iff.
  split.
  case.
  move => H0.
  apply.
  move => H0.
  split.
  left.
  apply H0.
  apply H0.
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

