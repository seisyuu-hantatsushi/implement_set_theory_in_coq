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

Inductive PickFamilySet {U:Type} (X_I:Collection (TypeOfOrderedPair (Collection U))) (i:U) : Collection U :=
| definition_of_pick_family_set: forall (x:U), (exists (X_i:Collection U), <|{|i|}, X_i|> ∈ X_I /\ x ∈ X_i) -> x ∈ (PickFamilySet X_I i).

(* ⌞ Unicode: 231E BOTTOM LEFT CORNER *)
Notation "X_I ⌞ i" := (PickFamilySet X_I i) (right associativity, at level 20).

Inductive BigCupOfFamilySet {U:Type} (I:Collection U) (X_I: U -> Collection U) : Collection U :=
| definition_of_bigcup_of_family: forall x:U, (exists i:U, i∈ I /\ x ∈ (X_I i)) -> x ∈ BigCupOfFamilySet I X_I.

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
    forall (f_i: U -> Collection U) (I:Collection U) (X': Collection (Collection U)) (X_I: Collection (TypeOfOrderedPair (Collection U))),
      I = `Ø` ->
      X_I = GraphOfIndexToFamilySet f_i I X' ->
      IndexingFunction f_i I X' ->
      BigCupOfFamilySet I (fun i:U => X_I ⌞ i) = `Ø`.
  Proof.
    move => f_i I X' X_I HIE HXI Hfi.
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

  Theorem bigcup_family_set_union_eq:
    forall (f_i: U -> Collection U) (I Y:Collection U) (X': Collection (Collection U)) (X_I: Collection (TypeOfOrderedPair (Collection U))),
      I <> `Ø` ->
      X_I = GraphOfIndexToFamilySet f_i I X' ->
      IndexingFunction f_i I X' ->
      BigCupOfFamilySet I (fun i:U => (X_I ⌞ i) ∪ Y ) = (BigCupOfFamilySet I (fun i:U => (X_I ⌞ i))) ∪ Y.
  Proof.
    move => f_i I Y X' X_I HInE HXI Hfi.
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

End CollectionFamily.







