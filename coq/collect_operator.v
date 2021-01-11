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
