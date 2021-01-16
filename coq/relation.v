From mathcomp Require Import ssreflect.

Require Import setsontypetheory.

Definition Relation U := U -> U -> Prop.

Definition ReflexiveRelation U (R:Relation U) := forall x:U, R x x. (* 反射的 *)
Definition IrreflexiveRelation U (R:Relation U) := forall x:U, ~R x x. (* 非反射的 *)
Definition SymmetricRelation U (R:Relation U) := forall x y:U, R x y -> R y x. (* 対称的 *)
Definition AntisymmetricRelation U (R:Relation U) := forall x y:U, R x y -> R y x -> x = y. (* 反対称的 *)
Definition AsymmetricRelation U (R:Relation U) := forall x y:U, ~(R x y -> R y x). (* 非対称的 *)
Definition TransitiveRelation U (R:Relation U) := forall x y z:U, R x y -> R y z -> R x z. (* 推移的 *)

Inductive PartialOrder (U:Type) (R:Relation U) : Prop :=
  define_partail_order: ReflexiveRelation U R -> AntisymmetricRelation U R -> TransitiveRelation U R -> PartialOrder U R.

(* operator Included. Collection -> Collection -> Prop *)
Definition Included U (X Y:Collection U) := forall x:U, x ∈ X -> x ∈ Y.
Definition IncludedNotEqualTo U (X Y:Collection U) := forall x:U, x ∈ X -> x ∈ Y /\ X <> Y.

Notation "A ⊂ B" := (Included _ A B) (right associativity, at level 35) : type_scope.
(* SUBSET OF WITH NOT EQUAL TO. Unicode:228A *)
Notation "A ⊊ B" := (IncludedNotEqualTo _ A B) (right associativity, at level 35) : type_scope.

Theorem Included_is_ReflexiveRelation: forall U:Type, ReflexiveRelation (Collection U) (Included U).
Proof.
  move => U x x0. exact.
Qed.

Theorem Included_is_AntisymmetricRelation: forall U:Type, AntisymmetricRelation (Collection U) (Included U).
Proof.
  move => U x y H0 H1.
  apply AxiomOfExtentionality => x0.
  rewrite /iff. split => H2.
  apply H0. by [].
  apply H1. by [].
Qed.

Theorem Included_is_TransitiveRelation: forall U:Type, TransitiveRelation (Collection U) (Included U).
Proof.
  move => U x y z H0 H1 x0 H2.
  apply H1.
  apply H0. by[].
Qed.

Theorem Included_is_PartialOrder: forall U:Type, PartialOrder (Collection U) (Included U).
  move => U.
  apply define_partail_order.
  apply Included_is_ReflexiveRelation.
  apply Included_is_AntisymmetricRelation.
  apply Included_is_TransitiveRelation.
Qed.

Theorem mutally_included_to_eq: forall U:Type, forall {A B:Collection U}, A ⊂ B /\ B ⊂ A -> A = B.
Proof.
  move => U A B.
  case.
  apply Included_is_AntisymmetricRelation.
Qed.

Theorem same_collection_to_mutally_included:
  forall U:Type, forall {A B:Collection U}, A = B -> A ⊂ B /\ B ⊂ A.
Proof.
  move => U A B H.
  rewrite H.
  split.
  apply Included_is_ReflexiveRelation.
  apply Included_is_ReflexiveRelation.
Qed.

Theorem mutally_included_iff_eq: forall U:Type, forall {A B:Collection U}, A ⊂ B /\ B ⊂ A <-> A = B.
Proof.
  move => U A B.
  rewrite /iff. split.
  apply mutally_included_to_eq.
  apply same_collection_to_mutally_included.
Qed.

Require Export setsontypetheory.
