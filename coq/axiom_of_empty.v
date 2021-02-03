From mathcomp Require Import ssreflect.

Require Import relation.

(* Axiom Of Extentionality in setontypetheory *)

Axiom AxiomOfEmpty: forall U:Type, exists z':Collection U, (forall x:U, x ∉ z').

Inductive EmptyCollection (U:Type) : Collection U := .
Inductive FullCollection (U:Type) : Collection U :=
| intro_full_collection: forall x:U, x ∈ FullCollection U.

Notation "`Ø`" :=  (EmptyCollection _) (at level 10).

Definition ComplementOfCollection (U:Type) (X:Collection U) : Collection U :=
  fun x:U => x ∉ X.

Notation "A ^c" := (ComplementOfCollection _ A) (at level 15).

Theorem noone_in_empty:
  forall U:Type, forall x:U, x ∉ `Ø`.
Proof.
  move => U x.
  case.
Qed.

Theorem same_empty_collection_is_exsitance:
  forall U:Type, exists a':Collection U, (forall x:U, x ∉ a') <-> (a' = `Ø`).
Proof.
  move => U.
  case: (AxiomOfEmpty U) => e' HAE.
  exists e'.
  rewrite /iff. split => H.
  apply: AxiomOfExtentionality => x0.
  rewrite /iff. split => H0.
  case: (HAE x0). by [].
  case: (noone_in_empty U x0). by [].
  by [].
Qed.

Theorem noone_in_collection_to_empty_collection:
  forall U:Type, forall {a':Collection U}, (forall x:U, x ∉ a') -> a' = `Ø`.
Proof.
  move => U a' HE.
  apply AxiomOfExtentionality.
  rewrite /iff. split => H.
  case: (HE x). by[].
  case: (noone_in_empty U x). by [].
Qed.

Theorem empty_collection_to_noone_in_collection:
  forall U:Type, forall a':Collection U, a' = `Ø` -> (forall x:U, x ∉ a').
Proof.
  move => U a' H.
  rewrite H.
  apply noone_in_empty.
Qed.

Theorem empty_collection_is_noone_in_collection:
  forall U:Type, forall a':Collection U, a' = `Ø` <-> (forall x:U, x ∉ a').
Proof.
  move => U a'.
  rewrite /iff. split.
  apply empty_collection_to_noone_in_collection.
  apply noone_in_collection_to_empty_collection.
Qed.

Theorem not_empty_collection_to_exists_element_in_collection:
  forall U:Type, forall a':Collection U, a' <> `Ø` -> (exists x:U, x ∈ a').
Proof.
  move => U a' HaNE.
  apply DoubleNegativeElimination => H.
  have L1: forall x:U, x ∉ a'.
  apply DeMorganNotExists.
  trivial.
  apply empty_collection_is_noone_in_collection in L1.
  apply HaNE.
  trivial.
Qed.

Theorem exists_element_in_collection_to_not_empty_collection:
  forall U:Type, forall a':Collection U, (exists x:U, x ∈ a') -> a' <> `Ø`.
Proof.
  move => U a' HexA HxA.
  move: HexA.
  apply DeMorganNotExists.
  apply empty_collection_is_noone_in_collection.
  trivial.
Qed.

Theorem not_empty_collection_has_least_a_element:
  forall U:Type, forall a':Collection U, a' <> `Ø` <-> (exists x:U, x ∈ a').
Proof.
  move => U a'.
  rewrite /iff. split.
  apply not_empty_collection_to_exists_element_in_collection.
  apply exists_element_in_collection_to_not_empty_collection.
Qed.

Theorem empty_collection_is_unique:
  forall U:Type, forall {a' b':Collection U}, (forall x: U, x ∉ a') -> (forall x: U, x ∉ b') -> a' = b'.
Proof.
  move => U a' b' HNa HNb.
  apply (noone_in_collection_to_empty_collection U) in HNa.
  apply (noone_in_collection_to_empty_collection U) in HNb.
  rewrite HNa HNb.
  reflexivity.
Qed.

Theorem all_collection_included_empty:
  forall U:Type, forall A:(Collection U), `Ø` ⊂ A.
Proof.
  move => U A x H.
  case: (noone_in_empty U x). by[].
Qed.

Theorem collection_is_subcollect_of_fullcollection:
  forall U:Type, forall A:(Collection U), A ⊂ FullCollection U.
Proof.
  move => U A x H.
  split.
Qed.

Theorem element_in_empty_collection_to_empty_collection_eq:
  forall (U:Type) (A:Collection U),
    (forall x:U, x ∈ A -> x ∈ `Ø`) -> A = `Ø`.
Proof.
  move => U A H.
  apply mutally_included_to_eq.
  split;[trivial|apply all_collection_included_empty].
Qed.

Theorem complement_of_complement_collect_is_self:
  forall U:Type, forall A:Collection U, A = (A^c)^c.
Proof.
  move => U A.
  apply mutally_included_to_eq.
  split => x H.
  case. by [].
  apply DoubleNegativeElimination in H. by [].
Qed.

Theorem LawOfExcludedMiddleAtComplementCollection:
  forall U:Type, forall A:Collection U, forall x:U, x ∈ A \/ x ∈ A^c.
Proof.
  move => U A x.
  apply LawOfExcludedMiddle.
Qed.

Theorem notin_collect_iff_in_complement:
  forall U:Type, forall A:Collection U, forall x:U, x ∉ A <-> x ∈ A^c.
Proof.
  move => U A x.
  rewrite /iff. split; apply.
Qed.
