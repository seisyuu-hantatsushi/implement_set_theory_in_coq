From mathcomp Require Import ssreflect.

Require Import setsontypetheory.

Definition Relation U := U -> U -> Prop.

Definition ReflexiveRelation U := forall R:Relation U, forall x:U, R x x.
Definition IrreflexiveRelation U := forall R:Relation U, forall x:U, ~R x x.

(* operator Included. Collection -> Collection -> Prop *)
Definition Included U (X Y:Collection U) := forall x:U, x ∈ X -> x ∈ Y.
Definition IncludedNotEqualTo U (X Y:Collection U) := forall x:U, x ∈ X -> x ∈ Y /\ X <> Y.

Notation "A ⊂ B" := (Included _ A B) (right associativity, at level 30) : type_scope.
(* SUBSET OF WITH NOT EQUAL TO. Unicode:228A *)
Notation "A ⊊ B" := (IncludedNotEqualTo _ A B) (right associativity, at level 30) : type_scope.

Require Export setsontypetheory.
