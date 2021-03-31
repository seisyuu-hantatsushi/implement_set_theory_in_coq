From mathcomp Require Import ssreflect.

Require Import collect_operator.
Require Import direct_product.
Require Import mapping.

(* 配置集合, MappingSpace *)
Inductive MappingSpace {U:Type} (X Y:Collection U) : Collection (TypeOfDirectProduct U) :=
  definition_of_mapping_space: forall (F:TypeOfDirectProduct U),
    (exists f:U->U, MappingFunction f X Y /\ F = GraphOfFunction f X Y) -> F ∈ MappingSpace X Y.

Section MappingSpace.

  Variable U:Type.

  Goal forall (X Y: Collection U) (F:TypeOfDirectProduct U),
      F ∈ MappingSpace X Y -> exists f:U->U,MappingFunction f X Y /\ F = GraphOfFunction f X Y.
  Proof.
    move => X Y F HFM.
    inversion HFM.
    apply H.
  Qed.

End MappingSpace.

(* GraphOfIndexToFamilySet, 添字集合と集合族のGraph*)
Inductive GraphOfIndexToFamilySet {U:Type} (map: U -> Collection U) (I:Collection U) (X: Collection (Collection U)) :
  Collection (TypeOfOrderedPair (Collection U)) :=
| definition_of_graph_of_index_to_family_set:
    forall Z:TypeOfOrderedPair (Collection U), (exists i:U, exists x':Collection U, Z=<|{|i|},x'|> /\ x' = map i /\ i ∈ I /\ x' ∈ X) -> Z ∈ GraphOfIndexToFamilySet map I X.

(* make sure that correspondence between indexed value in indexed set and set in set of family set. *)
Definition IndexingFunction {U:Type} (map: U -> Collection U) (I:Collection U) (X: Collection (Collection U)) :=
  forall i:U, i ∈ I -> exists x':Collection U, x' = map i /\ x' ∈ X.
