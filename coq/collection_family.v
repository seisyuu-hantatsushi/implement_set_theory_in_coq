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

Inductive PickFamilySet {U:Type} (S:Collection (TypeOfOrderedPair (Collection U))) (i:U) : Collection (Collection U) :=
| definition_of_pick_family_set: forall X:Collection U, <|{|i|}, X|> ∈ S -> X ∈ (PickFamilySet S i).

Section CollectionFamily.
  Variable U:Type.

  Theorem indexed_set_is_unique:
    forall (f_i: U -> Collection U) (I:Collection U) (X': Collection (Collection U)) (F: Collection (TypeOfOrderedPair (Collection U))),
      F = GraphOfIndexToFamilySet f_i I X' ->
      IndexingFunction f_i I X' ->
      forall (i:U), i ∈ I -> exists! X:Collection U, {|X|} = (PickFamilySet F i).
  Proof.
    move => f_i I X' F HF HIF i HiI.
    have L1: exists X:Collection U, X = f_i i /\ X ∈ X'.
    apply HIF.
    trivial.
    inversion L1 as [X].
    exists X.
    split.
    apply mutally_included_to_eq.
    split => Z H0.
    apply singleton_to_eq in H0.
    rewrite H0.
    split.
    rewrite HF.
    split.
    exists i.
    exists X.
    split;[reflexivity|split;[apply H|split;[trivial|apply H]]].
    inversion H0.
    rewrite HF in H1.
    inversion H1.
    inversion H3 as [i0 [X1]].
    inversion H5 as [Heq].
    apply ordered_pair_iff_and in Heq.
    inversion Heq.
    apply singleton_eq_to_element_eq in H7.
    apply eq_to_singleton.
    inversion H6.
    rewrite H8.
    rewrite H9.
    inversion H.
    rewrite H7 in H11.
    rewrite H11.
    reflexivity.
    move => X0 H'.
    apply mutally_included_iff_eq in H'.
    inversion H'.
    apply singleton_to_eq.
    apply: (H1 X).
    split.
    rewrite HF.
    split.
    exists i.
    exists X.
    split;[reflexivity|split;[apply H|split;[trivial|apply H]]].
  Qed.

  

End CollectionFamily.
