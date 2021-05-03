From mathcomp Require Import ssreflect.

Require Import zf.

Inductive SymDiffOfCollection {U:Type} (A B:Collection U): Collection U :=
| intro_sym_diff_of_collection:
    forall x:U, x ∈ (A \ B) ∪ (B \ A) -> x ∈ SymDiffOfCollection A B.

Notation "A △ B" := (SymDiffOfCollection A B) (right associativity, at level 30).

Inductive DirectSumOfCollection {U:Type} (X':Collection (Collection U)): Collection U:=
| definition_of_direct_sum_of_collection: forall x:U,
    x ∈ (⋃ X')  /\
    (forall A B:Collection U, A ∈ X' /\ B ∈ X' -> A ∩ B = `Ø`)
    -> x ∈ DirectSumOfCollection X'.

Definition CoveringBySets {U:Type} (X:Collection U) (X':Collection (Collection U)) := X = (⋃ X').

Definition CollectionIsPartition {U:Type} (X:Collection U) (X':Collection (Collection U)) :=
  X = (⋃ X') /\
  forall A B:Collection U, A ∈ X' /\ B ∈ X' -> A ∩ B <> `Ø` -> A = B.

Section CollectionOperator.
  Variable U:Type.
  Theorem AbsorptionEmpty:
    forall A:Collection U, (A ∪ `Ø`) = A.
  Proof.
    move => A.
    apply mutally_included_iff_eq.
    split => x.
    case. by [].
    apply all_collection_included_empty.
    move => H.
    left. by [].
  Qed.

  Theorem AbsorptionFull:
    forall A:Collection U, (A ∪ (FullCollection U)) = FullCollection U.
  Proof.
    move => A.
    apply mutally_included_iff_eq.
    split => x.
    case. exact.
    exact.
    move => H.
    right. by [].
  Qed.

  Theorem LawOfExcludedMiddleAtCollection:
    forall A:Collection U, A ∪ (A ^c) = FullCollection U.
  Proof.
    move => A.
    apply mutally_included_iff_eq.
    split => x H.
    exact.
    apply: in_or_to_in_union.
    apply LawOfExcludedMiddle.
  Qed.

  Theorem LawOfDistributiveByUnion:
    forall A B C:Collection U, (A ∩ B) ∪ C = (A ∪ C) ∩ (B ∪ C).
  Proof.
    move => A B C.
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
    forall A B C:Collection U, (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C).
  Proof.
    move => A B C.
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
    forall A B:Collection U, (A ∩ B) ∪ A = A.
  Proof.
    move => A B.
    apply union_iff_subcollect.
    move => x. case => x0 HA HB. by [].
  Qed.

  Theorem LawOfAbsorptionToIntersection:
    forall A B:Collection U, (A ∪ B) ∩ A = A.
  Proof.
    move => A B.
    rewrite LawOfCommutativeAtIntersection.
    apply subcollect_to_intersection.
    move => x. left. by [].
  Qed.

  Theorem DoMorgranLawAtUnion:
    forall A B:Collection U, (A ∪ B)^c = A^c ∩ B^c.
  Proof.
    move => A B.
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
    forall A B:Collection U, (A ∩ B)^c = A^c ∪ B^c.
  Proof.
    move => A B.
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

  Goal forall (A B:Collection U), A △ B = A^c △ B^c.
  Proof.
    move => A B.
    apply mutally_included_to_eq.
    split => x H.
    +inversion H as [x0 H0 Hx0].
     split.
     ++inversion H0 as [x1 H1|x1 H1];
         [right|left];
         inversion H1 as [x2 H3 H4 H5];
         split.
       apply notin_collect_iff_in_complement.
       apply H4.
       apply notin_collect_iff_in_complement.
       rewrite -complement_of_complement_collect_is_self.
       apply H3.
       apply H4.
       apply notin_collect_iff_in_complement.
       rewrite -complement_of_complement_collect_is_self.
       apply H3.
    +inversion H.
     inversion H0; split;
       [right|left];
       split; inversion H2.
     apply DoubleNegativeElimination.
     apply H5.
     apply notin_collect_iff_in_complement.
     apply H4.
     apply DoubleNegativeElimination.
     apply H5.
     apply notin_collect_iff_in_complement.
     apply H4.
  Qed.

  Goal
    forall (X:Collection U) (X':Collection (Collection U)),
      CollectionIsPartition X X' -> CoveringBySets X X'.
  Proof.
    move => X X' H.
    inversion H.
    trivial.
  Qed.

End CollectionOperator.

Require Export zf.
