From mathcomp Require Import ssreflect.

Require Import collect_operator.
Require Import direct_product.
Require Import mapping.
Require Import mapping_morphism.
Require Import collection_family.

Inductive EquivalenceClass {U:Type} (R:Relation U) (a:U) : Collection U :=
  definition_of_equivalence_class: forall x:U, EquivalenceRelation U R /\ R a x -> x ∈ EquivalenceClass R a.
(*
Inductive QuotientSet {U:Type} (R:Relation U) (X:Collection U) : Collection (Collection U) :=
  definition_of_quotinet_set: forall (A:Collection U), (forall x:U, x ∈ X -> A ⊂ EquivalenceClass R x) -> A ∈ QuotientSet R X.
 *)
Definition QuotientSet (U:Type) (R:Relation U) (a:U) := PowerCollection (EquivalenceClass R a).

Section EquivalenceClass.
  Variable U:Type.
  Variable R:Relation U.

  Theorem a_element_in_equivalence_class_of_it_element:
    EquivalenceRelation U R ->
    forall a:U, a ∈ EquivalenceClass R a.
  Proof.
    move => H a.
    split.
    split.
    split.
    apply H.
    apply H.
    apply H.
    inversion H.
    apply H0.
  Qed.

  Theorem equivalence_relation_element_in_equivalence_class_of_it_element:
    EquivalenceRelation U R ->
    forall a x:U, R a x -> x ∈ EquivalenceClass R a.
  Proof.
    move => H a x HR.
    split.
    split; assumption.
  Qed.

  Theorem element_in_equivalence_class_of_it_element_to_relation:
    EquivalenceRelation U R ->
    forall a x:U, x ∈ EquivalenceClass R a -> R a x.
  Proof.
    move => HR a x H.
    inversion H.
    inversion H0.
    apply H3.
  Qed.
  
  Theorem equivalence_relation_to_equivalence_class_eq:
    EquivalenceRelation U R ->
    forall a b:U, R a b -> EquivalenceClass R a = EquivalenceClass R b.
  Proof.
    move => H a b HR.
    inversion H.
    apply mutally_included_to_eq.
    split => x H';[inversion H' as [x0 [HR' HRax]]|
                   inversion H' as [x0 [HR' HRbx]]];
             split;split.
    apply H.
    apply H1.
    apply (H2 x a b).
    apply H1.
    trivial.
    assumption.
    apply H.
    apply (H2 a b x).
    apply HR.
    assumption.
  Qed.

  Theorem equivalence_class_eq_to_equivalence_relation:
    EquivalenceRelation U R ->
    forall a b:U, EquivalenceClass R a = EquivalenceClass R b -> R a b.
  Proof.
    move => HR a b H.
    apply mutally_included_iff_eq in H.
    inversion H.
    move: (H1 b) => H1b.
    apply element_in_equivalence_class_of_it_element_to_relation.
    apply HR.
    apply H1b.
    apply a_element_in_equivalence_class_of_it_element.
    apply HR.
  Qed.

  Theorem equivalence_relation_iff_equivalence_class_eq:
    EquivalenceRelation U R ->
    forall a b:U,  R a b <-> EquivalenceClass R a = EquivalenceClass R b.
  Proof.
    move => HR a b.
    rewrite /iff.
    split;[apply equivalence_relation_to_equivalence_class_eq|
           apply equivalence_class_eq_to_equivalence_relation];trivial.
  Qed.

  Theorem same_relation_to_intersection_of_equivalence_class_not_empty:
    EquivalenceRelation U R ->
    forall a b:U, R a b -> EquivalenceClass R a ∩ EquivalenceClass R b <> `Ø`.
  Proof.
    move => HR a b H.
    apply exists_element_in_collection_to_not_empty_collection.
    exists a.
    split;[apply a_element_in_equivalence_class_of_it_element|
           apply equivalence_relation_element_in_equivalence_class_of_it_element];trivial.
    inversion HR.
    apply H1.
    assumption.
  Qed.
  
  Theorem intersection_of_equivalence_class_not_empty_to_same_relation:
    EquivalenceRelation U R ->
    forall a b:U, EquivalenceClass R a ∩ EquivalenceClass R b <> `Ø` -> R a b.
  Proof.
    move => HR a b H.
    apply not_empty_collection_to_exists_element_in_collection in H.
    inversion H as [x].
    inversion H0.
    apply element_in_equivalence_class_of_it_element_to_relation.
    trivial.
    suff: R a b.
    apply equivalence_relation_element_in_equivalence_class_of_it_element.
    trivial.
    inversion HR.
    apply: (H6 a x b).
    apply element_in_equivalence_class_of_it_element_to_relation;trivial.
    apply H5.
    apply element_in_equivalence_class_of_it_element_to_relation;trivial.
  Qed.

  Theorem same_relation_iff_intersection_of_equivalence_class_not_empty:
    EquivalenceRelation U R ->
    forall a b:U, R a b <-> EquivalenceClass R a ∩ EquivalenceClass R b <> `Ø`.
  Proof.
    move => HR a b.
    rewrite /iff.
    split;[apply same_relation_to_intersection_of_equivalence_class_not_empty|
           apply intersection_of_equivalence_class_not_empty_to_same_relation];trivial.
  Qed.
  
End EquivalenceClass.
