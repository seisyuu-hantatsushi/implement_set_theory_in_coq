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
    forall Z:TypeOfOrderedPair (Collection U),
      (exists i:U, exists x':Collection U, Z=<|{|i|},x'|> /\ x' = map i /\ i ∈ I /\ x' ∈ X) ->
      Z ∈ GraphOfIndexToFamilySet map I X.

(* make sure that correspondence between indexed value in indexed set and set in set of family set. *)
Definition IndexingFunction {U:Type} (map: U -> Collection U) (I:Collection U) (X: Collection (Collection U)) :=
  forall i:U, i ∈ I -> exists x':Collection U, x' = map i /\ x' ∈ X.

Inductive PickFamilySet {U:Type} (X_I:Collection (TypeOfOrderedPair (Collection U))) (i:U) : Collection U :=
| intro_of_pick_family_set: forall (x:U), (exists (X_i:Collection U), <|{|i|}, X_i|> ∈ X_I /\ x ∈ X_i) -> x ∈ (PickFamilySet X_I i).

(* ⌞ Unicode: 231E BOTTOM LEFT CORNER *)
Notation "X_I ⌞ i" := (PickFamilySet X_I i) (right associativity, at level 20).

Inductive BigCupOfFamilySet {U:Type} (I:Collection U) (X_I: U -> Collection U) : Collection U :=
| intro_of_bigcup_of_family: forall x:U, (exists i:U, i ∈ I /\ x ∈ (X_I i)) -> x ∈ BigCupOfFamilySet I X_I.

Notation "⋃{ I , X_I }" := (BigCupOfFamilySet I X_I).

Inductive BigCapOfFamilySet {U:Type} (I:Collection U) (X_I: U -> Collection U) : Collection U :=
| intro_of_bigcap_of_family: forall x: U, (forall i:U, i ∈ I -> x ∈ (X_I i)) -> x ∈ BigCapOfFamilySet I X_I.

Notation "⋂{ I , X_I }" := (BigCapOfFamilySet I X_I).

Section CollectionFamily.
  Variable U:Type.

  Theorem indexed_set_is_unique:
    forall (f_i: U -> Collection U) (I:Collection U) (X': Collection (Collection U)) (F: Collection (TypeOfOrderedPair (Collection U))),
      F = GraphOfIndexToFamilySet f_i I X' ->
      IndexingFunction f_i I X' ->
      forall (i:U), i ∈ I -> exists! X_i:Collection U, X_i = (PickFamilySet F i).
  Proof.
    move => f_i I X' F HF HIF i HiI.
    have L1: exists X:Collection U, X = f_i i /\ X ∈ X'.
    apply HIF.
    trivial.
    inversion L1 as [X_i].
    exists X_i.
    split.
    apply mutally_included_to_eq.
    split => x H0.
    split.
    exists X_i.
    split.
    rewrite HF.
    split.
    exists i.
    exists X_i.
    inversion H.
    split;[reflexivity|split;trivial;[split;trivial]].
    trivial.
    inversion H0.
    inversion H1 as [X_i'].
    inversion H3.
    rewrite HF in H4.
    inversion H4.
    inversion H6 as [i0 [X_i'']].
    inversion H.
    inversion H8 as [H11 [H12 [H13 H14]]].
    apply ordered_pair_iff_and in H11.
    inversion H11.
    rewrite H9.
    apply singleton_eq_to_element_eq in H15.
    rewrite -H15 in H12.
    rewrite H12 in H16.
    rewrite H16 in H5.
    assumption.
    move => x' H'.
    rewrite H'.
    apply mutally_included_to_eq.
    split => x H0.
    split.
    exists X_i.
    split.
    rewrite HF.
    split.
    exists i.
    exists X_i.
    split;[reflexivity|].
    inversion H.
    split;[trivial|split;trivial].
    trivial.
    inversion H0.
    inversion H1 as [X_i'].
    inversion H3.
    rewrite HF in H4.
    inversion H4.
    inversion H6 as [i0 [X_i0']].
    inversion H8 as [H9 [H10 [H11 H12]]].
    apply ordered_pair_iff_and in H9.
    inversion H9.
    apply singleton_eq_to_element_eq in H13.
    rewrite -H13 in H10.
    rewrite -H14 in H10.
    inversion H.
    rewrite H10 in H5.
    rewrite H15.
    assumption.
  Qed.

  Theorem indexed_set_eq_empty_to_bigcup_eq_empty:
    forall (f_i: U -> Collection U) (I:Collection U) (X_I: Collection (TypeOfOrderedPair (Collection U))),
      I = `Ø` ->
      ⋃{ I , (fun i:U => X_I ⌞ i) } = `Ø`.
  Proof.
    move => f_i I X_I HIE.
    apply mutally_included_to_eq.
    split => x H.
    inversion H.
    inversion H0 as [i].
    inversion H2.
    rewrite HIE in H3.
    apply DoubleNegativeElimination.
    move => HxnE.
    move: H3.
    apply noone_in_empty.
    apply DoubleNegativeElimination.
    move => HxnB.
    move :H.
    apply noone_in_empty.
  Qed.

  Theorem indexed_set_eq_empty_to_bigcap_eq_full:
    forall (I:Collection U) (X_I: Collection (TypeOfOrderedPair (Collection U))),
      I = `Ø` ->
      ⋂{ I , (fun i:U => X_I ⌞ i) } = (FullCollection U).
  Proof.
    move => I X_I HIE.
    apply mutally_included_to_eq.
    split => x H.
    apply intro_full_collection.
    split => i HiI.
    rewrite HIE in HiI.
    apply DoubleNegativeElimination => HXi.
    move: HiI.
    apply noone_in_empty.
  Qed.

  Theorem a_collection_included_bigcup_of_family_set_to_a_collection_included_element_of_family_set:
    forall (I Y:Collection U) (X_I: Collection (TypeOfOrderedPair (Collection U))),
      ⋃{ I , (fun i:U => X_I ⌞ i) } ⊂ Y -> forall i:U, i ∈ I -> X_I ⌞ i ⊂ Y.
  Proof.
    move => I Y X_I H i HiI x HxXi.
    apply H.
    split.
    exists i.
    split; trivial.
  Qed.

  Theorem a_collection_included_element_of_family_set_to_a_collection_included_bigcup_of_family_set:
    forall (I Y:Collection U) (X_I: Collection (TypeOfOrderedPair (Collection U))),
      (forall i:U, i ∈ I -> X_I ⌞ i ⊂ Y) -> ⋃{ I , (fun i:U => X_I ⌞ i) } ⊂ Y.
  Proof.
    move => I Y X_I H x H'.
    inversion H'.
    inversion H0 as [i].
    inversion H2.
    apply H in H3.
    apply H3.
    assumption.
  Qed.

  Theorem a_collection_included_bigcup_of_family_set_iff_a_collection_included_element_of_family_set:
    forall (I Y:Collection U) (X_I: Collection (TypeOfOrderedPair (Collection U))),
      ⋃{ I , (fun i:U => X_I ⌞ i) } ⊂ Y <-> forall i:U, i ∈ I -> X_I ⌞ i ⊂ Y.
  Proof.
    move => I Y X_I.
    rewrite /iff.
    split;[apply a_collection_included_bigcup_of_family_set_to_a_collection_included_element_of_family_set|
           apply a_collection_included_element_of_family_set_to_a_collection_included_bigcup_of_family_set].
  Qed.

  Theorem bigcap_of_family_set_included_a_collection_to_element_of_family_set_included_a_collection:
    forall (I Y:Collection U) (X_I: Collection (TypeOfOrderedPair (Collection U))),
      Y ⊂ ⋂{ I , (fun i:U => X_I ⌞ i) } -> forall i:U, i ∈ I -> Y ⊂ X_I ⌞ i.
  Proof.
    move => I Y X_I H i HiI x HxY.
    apply H in HxY.
    inversion HxY.
    apply H0 in HiI.
    assumption.
  Qed.

  Theorem element_of_family_set_included_a_collection_to_bigcap_of_family_set_included_a_collection:
    forall (I Y:Collection U) (X_I: Collection (TypeOfOrderedPair (Collection U))),
      (forall i:U, i ∈ I -> Y ⊂ X_I ⌞ i) -> Y ⊂ ⋂{ I , (fun i:U => X_I ⌞ i) }.
  Proof.
    move => I Y X_I H x HxY.
    split => i HiI.
    apply H in HiI.
    apply HiI.
    assumption.
  Qed.

  Theorem a_collection_included_element_of_family_set_iff_a_collection_included_bigcap_of_family_set:
    forall (I Y:Collection U) (X_I: Collection (TypeOfOrderedPair (Collection U))),
      Y ⊂ ⋂{ I , (fun i:U => X_I ⌞ i) } <-> forall i:U, i ∈ I -> Y ⊂ X_I ⌞ i.
  Proof.
    move => I Y X_I.
    rewrite /iff.
    split;[apply bigcap_of_family_set_included_a_collection_to_element_of_family_set_included_a_collection|
           apply element_of_family_set_included_a_collection_to_bigcap_of_family_set_included_a_collection].
  Qed.

  Theorem bigcap_intersection_indexed_set:
    forall (f_i: U -> Collection U) (I I1 I2:Collection U) (X_I: Collection (TypeOfOrderedPair (Collection U))),
      I = I1 ∪ I2 ->
      ⋂{ I , (fun i:U => X_I ⌞ i) } = ⋂{ I1 , (fun i:U => X_I ⌞ i) } ∩ ⋂{ I2 , (fun i:U => X_I ⌞ i) }.
  Proof.
    move => f_i I I1 I2 X_I HI.
    apply mutally_included_to_eq.
    rewrite HI.
    split => x H.
    inversion H as [x0].
    split;[split => i1' Hi1'I1; move: (H0 i1'); apply; left|
           split => i2' Hi2'I2; move: (H0 i2'); apply; right];trivial.
    inversion H as [x0].
    inversion H0 as [x1].
    inversion H1 as [x2].
    split.
    move => i.
    case => [i1'|i2'].
    apply H3.
    apply H5.
  Qed.

  Theorem LawOfDeMorganOfBigcup:
    forall(I:Collection U) (X_I: Collection (TypeOfOrderedPair (Collection U))),
      (⋃{ I , (fun i:U => X_I ⌞ i) })^c = ⋂{ I , (fun i:U => (X_I ⌞ i)^c) }.
  Proof.
    move => I X_I.
    apply mutally_included_to_eq.
    split => x H.
    split => i HiI HxXI.
    apply H.
    split.
    exists i.
    split;trivial.
    move => Hn.
    inversion Hn.
    inversion H0 as [i].
    inversion H.
    inversion H2.
    apply H3 in H5.
    apply H5.
    assumption.
  Qed.

  Theorem LawOfDeMorganOfBigcap:
    forall (I:Collection U) (X_I: Collection (TypeOfOrderedPair (Collection U))),
      (⋂{ I , (fun i:U => X_I ⌞ i) })^c = ⋃{ I , (fun i:U => (X_I ⌞ i)^c) }.
  Proof.
    move => I X_I.
    apply mutally_included_to_eq.
    split => x H.
    split.
    apply notin_collect_iff_in_complement in H.
    apply DoubleNegativeElimination.
    move => Hn.
    apply H.
    split.
    move => i HiI.
    apply DoubleNegativeElimination.
    move => H'.
    apply Hn.
    exists i.
    split;trivial.
    move => H'.
    inversion H.
    inversion H0 as [i].
    inversion H'.
    inversion H2.
    apply H3 in H5.
    apply H6.
    trivial.
  Qed.

  Theorem bigcup_family_set_union_eq:
    forall (I Y:Collection U) (X_I: Collection (TypeOfOrderedPair (Collection U))),
      I <> `Ø` ->
      ⋃{ I , (fun i:U => (X_I ⌞ i) ∪ Y) } = ⋃{ I , (fun i:U => (X_I ⌞ i)) } ∪ Y.
  Proof.
    move => I Y X_I HInE.
    apply not_empty_collection_to_exists_element_in_collection in HInE.
    inversion HInE as [i HiI].
    apply mutally_included_to_eq.
    split => x H.
    inversion H as [x0].
    inversion H0 as [i0].
    inversion H2 as [Hi0I].
    case H3 => x1.
    move => Hx1XI.
    left.
    split.
    exists i0.
    split;trivial.
    move => Hx1Y.
    right.
    trivial.
    case H.
    move => x0 Hx0B.
    inversion Hx0B as [x1].
    inversion H0 as [i0].
    split.
    exists i0.
    inversion H2.
    split.
    trivial.
    left.
    trivial.
    move => x0 Hx0Y.
    split.
    exists i.
    split;[trivial|right;trivial].
  Qed.

  Theorem bigcup_family_set_intersection_eq:
    forall (I Y:Collection U) (X_I: Collection (TypeOfOrderedPair (Collection U))),
      ⋃{ I , (fun i:U => (X_I ⌞ i) ∩ Y) } = ⋃{ I , (fun i:U => (X_I ⌞ i)) } ∩ Y.
  Proof.
    move => I Y X_I.
    apply mutally_included_to_eq.
    split => x H.
    inversion H as [x0 [i [HiI [x0' HxXI HxY]]]].
    split;[split;exists i;split;trivial|trivial].
    inversion H as [x0 [x1 [i [HiI]]]].
    split.
    exists i.
    split;[trivial|split;trivial].
  Qed.

  Theorem bigcap_family_set_union_eq:
    forall (I Y:Collection U) (X_I: Collection (TypeOfOrderedPair (Collection U))),
      ⋂{ I , (fun i:U => (X_I ⌞ i) ∪ Y) } = ⋂{ I , (fun i:U => (X_I ⌞ i)) } ∪ Y.
  Proof.
    move => I Y X_I.
    apply mutally_included_to_eq.
    split => x H.
    suff:  x ∈ Y \/ x ∉ Y.
    case => HY.
    right.
    trivial.
    left.
    split => i HiI.
    inversion H.
    apply H0 in HiI.
    inversion HiI.
    apply H2.
    apply DoubleNegativeElimination => Hn.
    apply HY.
    assumption.
    apply LawOfExcludedMiddle.
    split => i HiI.
    inversion H.
    left.
    inversion H0.
    apply H2 in HiI.
    trivial.
    right.
    trivial.
  Qed.


End CollectionFamily.









