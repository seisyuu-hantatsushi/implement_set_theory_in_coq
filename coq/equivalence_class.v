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
  Goal
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

  Goal
    EquivalenceRelation U R ->
    forall a x:U, R a x -> x ∈ EquivalenceClass R a.
  Proof.
    move => H a x HR.
    split.
    split; assumption.
  Qed.

  Goal
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

End EquivalenceClass.
