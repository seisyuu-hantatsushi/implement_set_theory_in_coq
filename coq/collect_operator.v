From mathcomp Require Import ssreflect.

Require Import zf.

Theorem AbsorptionEmpty:
  forall U:Type, forall A:Collection U, (A ∪ `Ø`) = A.
Proof.
  move => U A.
  apply mutally_included_iff_eq.
  split => x.
  case. by [].
  apply all_collection_included_empty.
  move => H.
  left. by [].
Qed.

Theorem AbsorptionFull:
  forall U:Type, forall A:Collection U, (A ∪ (FullCollection U)) = FullCollection U.
Proof.
  move => U A.
  apply mutally_included_iff_eq.
  split => x.
  case. exact.
  exact.
  move => H.
  right. by [].
Qed.

Theorem LawOfExcludedMiddleAtCollection:
  forall U:Type, forall A:Collection U, A ∪ (A ^c) = FullCollection U.
Proof.
  move => U A.
  apply mutally_included_iff_eq.
  split => x H.
  exact.
  apply: in_or_to_in_union.
  apply LawOfExcludedMiddle.
Qed.

Theorem LawOfDistributiveByUnion:
  forall U:Type, forall A B C:Collection U, (A ∩ B) ∪ C = (A ∪ C) ∩ (B ∪ C).
Proof.
  move => U A B C.
  apply mutally_included_iff_eq.
  split => x H0.
  apply in_intersection_iff_in_and.
  suff: (x ∈ A \/ x ∈ C) /\ (x ∈ B \/ x ∈ C).
  case => HAC HBC.
  split; apply in_or_to_in_union; by [].
  have L1: (x ∈ A /\ x ∈ B) \/ x ∈ C.
  case: H0 => x0 HAB; [left; apply in_intersection_iff_in_and | right]; by[].
  apply LawOfDistributiveByOr. by[].
  suff: (x ∈ A /\ x ∈ B) \/ x ∈ C.
  case => H; [left; apply in_intersection_iff_in_and | right]; by[].
  apply LawOfDistributiveByOr.
  case H0 => x0 H1 H2.
  split; apply in_union_iff_in_or; by [].
Qed.

Theorem LawOfDistributiveByIntersection:
  forall U:Type, forall A B C:Collection U, (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C).
Proof.
  move => U A B C.
  apply mutally_included_iff_eq.
  split => x H0.
  apply in_union_iff_in_or.
  suff: (x ∈ A /\ x ∈ C) \/ (x ∈ B /\ x ∈ C).
  case => H; [left|right]; apply in_intersection_iff_in_and; by [].
  apply LawOfDistributiveByAnd.
  case: H0 => x0 HAB HC.
  split; [apply in_union_iff_in_or|]; by[].
  suff: (x ∈ A \/ x ∈ B) /\ x ∈ C.
  case => HAB HC.
  apply in_and_to_in_intersection.
  split; [apply in_union_iff_in_or|]; by[].
  apply LawOfDistributiveByAnd.
  case H0 => x0 H1; [left|right]; apply in_intersection_iff_in_and; by [].
Qed.

Theorem LawOfAbsorptionToUnion:
  forall U:Type, forall A B:Collection U, (A ∩ B) ∪ A = A.
Proof.
  move => U A B.
  apply union_iff_subcollect.
  move => x. case => x0 HA HB. by [].
Qed.

Theorem LawOfAbsorptionToIntersection:
  forall U:Type, forall A B:Collection U, (A ∪ B) ∩ A = A.
Proof.
  move => U A B.
  rewrite LawOfCommutativeAtIntersection.
  apply subcollect_to_intersection.
  move => x. left. by [].
Qed.

Theorem DoMorgranLawAtUnion:
  forall U:Type, forall A B:Collection U, (A ∪ B)^c = A^c ∩ B^c.
Proof.
  move => U A B.
  apply mutally_included_iff_eq.
  split => x H.
  apply in_and_to_in_intersection.
  apply LawOfDeMorgan_NegtationOfDisjunction.
  move => HAB.
  apply H.
  apply in_or_to_in_union. by [].
  apply in_intersection_to_in_and in H.
  apply LawOfDeMorgan_NegtationOfDisjunction in H.
  move => HF.
  apply H.
  apply in_union_to_in_or. by [].
Qed.

Theorem DoMorgranLawAtIntersection:
  forall U:Type, forall A B:Collection U, (A ∩ B)^c = A^c ∪ B^c.
Proof.
  move => U A B.
  apply mutally_included_iff_eq.
  split => x H.
  apply in_or_to_in_union.
  apply LawOfDeMorgan_NegtationOfConjunction => HAB.
  apply H.
  apply in_and_to_in_intersection in HAB. by [].
  apply in_union_to_in_or in H.
  apply LawOfDeMorgan_NegtationOfConjunction in H.
  move => HAB.
  apply H.
  apply in_intersection_to_in_and. by [].
Qed.
