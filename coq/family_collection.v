From mathcomp Require Import ssreflect.

Require Import collect_operator.
Require Import direct_product.
Require Import mapping.
Require Import mapping_space.

Definition TypeOfSetOfFamilySet U := Collection (TypeOfOrderedPair (Collection U)).

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

Inductive PickFamilySet {U:Type} (X_I:TypeOfSetOfFamilySet U) (i:U) : Collection U :=
| intro_of_pick_family_set: forall (x:U), (exists (X_i:Collection U), <|{|i|}, X_i|> ∈ X_I /\ x ∈ X_i) -> x ∈ (PickFamilySet X_I i).

(* ⌞ Unicode: 231E BOTTOM LEFT CORNER *)
Notation "X_I ⌞ i" := (PickFamilySet X_I i) (right associativity, at level 20).

Inductive BigCupOfFamilySet {U V:Type} (I:Collection V) (X_I: V -> Collection U) : Collection U :=
| intro_of_bigcup_of_family: forall x:U, (exists i:V, i ∈ I /\ x ∈ (X_I i)) -> x ∈ BigCupOfFamilySet I X_I.

Notation "⋃{ I , X_I }" := (BigCupOfFamilySet I X_I).

Inductive BigCapOfFamilySet {U V:Type} (I:Collection V) (X_I: V -> Collection U) : Collection U :=
| intro_of_bigcap_of_family: forall x: U, (forall i:V, i ∈ I -> x ∈ (X_I i)) -> x ∈ BigCapOfFamilySet I X_I.

Notation "⋂{ I , X_I }" := (BigCapOfFamilySet I X_I).

Inductive BuilderOfFamilySet {U V:Type} (I:Collection V) (X_I:V -> Collection U) : Collection (Collection U) :=
| definition_of_collection_of_family_set:
    forall Xi:Collection U, (exists i:V, i ∈ I /\ Xi = X_I i) -> Xi ∈ BuilderOfFamilySet I X_I.

Definition CoveringByFamilySet {U V:Type} (X:Collection U) (I:Collection V) (X_I: V -> Collection U) := X = ⋃{ I , X_I }.

Definition ProvidePartitionByFamilySetToSet {U V:Type} (X:Collection U) (I:Collection V) (X_I: V -> Collection U) :=
  CoveringByFamilySet X I X_I /\
  (forall i:V, i ∈ I -> X_I i <> `Ø`) /\
  (forall i j:V, i ∈ I /\ j ∈ I /\ i <> j -> (X_I i) ∩ (X_I j) = `Ø`).

(*
Inductive DirectProductOfFamilySet {U V:Type} (I:Collection V) (X_I: V -> Collection U) :=
  *)

Section FamilyCollection.
  Variable U:Type.

  Theorem indexed_set_is_unique:
    forall (f_i: U -> Collection U) (I:Collection U) (X': Collection (Collection U)) (F: TypeOfSetOfFamilySet U),
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
    forall (f_i: U -> Collection U) (I:Collection U) (X_I: TypeOfSetOfFamilySet U),
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
    forall (I Y:Collection U) (X_I: TypeOfSetOfFamilySet U),
      ⋃{ I , (fun i:U => X_I ⌞ i) } ⊂ Y -> forall i:U, i ∈ I -> X_I ⌞ i ⊂ Y.
  Proof.
    move => I Y X_I H i HiI x HxXi.
    apply H.
    split.
    exists i.
    split; trivial.
  Qed.

  Theorem a_collection_included_element_of_family_set_to_a_collection_included_bigcup_of_family_set:
    forall (I Y:Collection U) (X_I: TypeOfSetOfFamilySet U),
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
    forall (I Y:Collection U) (X_I: TypeOfSetOfFamilySet U),
      ⋃{ I , (fun i:U => X_I ⌞ i) } ⊂ Y <-> forall i:U, i ∈ I -> X_I ⌞ i ⊂ Y.
  Proof.
    move => I Y X_I.
    rewrite /iff.
    split;[apply a_collection_included_bigcup_of_family_set_to_a_collection_included_element_of_family_set|
           apply a_collection_included_element_of_family_set_to_a_collection_included_bigcup_of_family_set].
  Qed.

  Theorem bigcap_of_family_set_included_a_collection_to_element_of_family_set_included_a_collection:
    forall (I Y:Collection U) (X_I: TypeOfSetOfFamilySet U),
      Y ⊂ ⋂{ I , (fun i:U => X_I ⌞ i) } -> forall i:U, i ∈ I -> Y ⊂ X_I ⌞ i.
  Proof.
    move => I Y X_I H i HiI x HxY.
    apply H in HxY.
    inversion HxY.
    apply H0 in HiI.
    assumption.
  Qed.

  Theorem element_of_family_set_included_a_collection_to_bigcap_of_family_set_included_a_collection:
    forall (I Y:Collection U) (X_I: TypeOfSetOfFamilySet U),
      (forall i:U, i ∈ I -> Y ⊂ X_I ⌞ i) -> Y ⊂ ⋂{ I , (fun i:U => X_I ⌞ i) }.
  Proof.
    move => I Y X_I H x HxY.
    split => i HiI.
    apply H in HiI.
    apply HiI.
    assumption.
  Qed.

  Theorem a_collection_included_element_of_family_set_iff_a_collection_included_bigcap_of_family_set:
    forall (I Y:Collection U) (X_I: TypeOfSetOfFamilySet U),
      Y ⊂ ⋂{ I , (fun i:U => X_I ⌞ i) } <-> forall i:U, i ∈ I -> Y ⊂ X_I ⌞ i.
  Proof.
    move => I Y X_I.
    rewrite /iff.
    split;[apply bigcap_of_family_set_included_a_collection_to_element_of_family_set_included_a_collection|
           apply element_of_family_set_included_a_collection_to_bigcap_of_family_set_included_a_collection].
  Qed.

  Theorem bigcap_intersection_indexed_set:
    forall (f_i: U -> Collection U) (I I1 I2:Collection U) (X_I: TypeOfSetOfFamilySet U),
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
    forall(I:Collection U) (X_I: TypeOfSetOfFamilySet U),
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
    forall (I:Collection U) (X_I: TypeOfSetOfFamilySet U),
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
    forall (I Y:Collection U) (X_I: TypeOfSetOfFamilySet U),
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
    forall (I Y:Collection U) (X_I: TypeOfSetOfFamilySet U),
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
    forall (I Y:Collection U) (X_I: TypeOfSetOfFamilySet U),
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

  Theorem a_collection_minus_bigcap_eq_bigcup_a_collection_minus_element_of_family_set:
    forall (I Y:Collection U) (X_I: TypeOfSetOfFamilySet U),
      Y \ ⋂{ I , (fun i:U => (X_I ⌞ i)) } = ⋃{ I , (fun i:U => Y \ (X_I ⌞ i)) }.
  Proof.
    move => I Y X_I.
    apply mutally_included_to_eq.
    split => x H.
    inversion H.
    split.
    apply DoubleNegativeElimination.
    move => Hn.
    have L1: forall i:U, ~(i ∈ I /\ x ∈ Y \ X_I ⌞ i).
    move => i HnP.
    apply Hn.
    exists i.
    apply HnP.
    apply H1.
    split => i HiI.
    move: (L1 i) => L1i.
    apply DoubleNegativeElimination.
    move => HnxXI.
    apply L1i.
    split.
    apply HiI.
    split.
    apply H0.
    apply HnxXI.
    inversion H.
    inversion H0 as [i].
    inversion H2 as [HiI [x' HxY HnxXIi]].
    split.
    trivial.
    move => Hin.
    apply HnxXIi.
    inversion Hin.
    apply H3 in HiI.
    assumption.
  Qed.

  Theorem a_collection_minus_bigcup_eq_bigcap_a_collection_minus_element_of_family_set:
    forall (I Y:Collection U) (X_I: TypeOfSetOfFamilySet U),
      I <> `Ø` ->
      Y \ ⋃{ I , (fun i:U => (X_I ⌞ i)) } = ⋂{ I , (fun i:U => Y \ (X_I ⌞ i)) }.
  Proof.
    move => I Y X_I HneI.
    apply mutally_included_to_eq.
    split => x H.
    inversion H.
    split => i HiI.
    split.
    trivial.
    move => HxXI.
    apply H1.
    split.
    exists i.
    split;assumption.
    inversion H.
    apply not_empty_collection_has_least_a_element in HneI.
    inversion HneI as [i].
    apply H0 in H2.
    inversion H2.
    split.
    trivial.
    move => H''.
    inversion H''.
    inversion H6 as [i0 [Hi0I Hx1XI]].
    apply H0 in Hi0I.
    inversion Hi0I.
    apply H9.
    trivial.
  Qed.

  Goal
    forall (I J:Collection U) (X_I Y_J: TypeOfSetOfFamilySet U),
    forall x:U,
      x ∈ ⋂{ I × J, (fun ij:TypeOfOrderedPair U => (fun x:U => forall i j:U, ij=<|i,j|> -> x ∈ X_I ⌞ i ∪ Y_J ⌞ j))} -> forall i j:U, i∈I -> j∈J -> x ∈ X_I ⌞ i ∪ Y_J ⌞ j.
  Proof.
    move => I J X_I Y_J x H i j HiI HjJ.
    have L1: <|i,j|> ∈ I × J.
    apply in_and_to_ordered_pair_in_direct_product.
    split;trivial.
    inversion H.
    apply H0 in L1.
    apply L1.
    reflexivity.
  Qed.

  Goal
    forall (I J:Collection U) (X_I Y_J: TypeOfSetOfFamilySet U),
    forall x:U,
      (forall i j:U, i∈I -> j∈J -> x ∈ X_I ⌞ i ∪ Y_J ⌞ j) -> x ∈ ⋂{ I × J, (fun ij:TypeOfOrderedPair U => (fun x:U => forall i j:U, ij=<|i,j|> -> x ∈ X_I ⌞ i ∪ Y_J ⌞ j))}.
  Proof.
    move => I J X_I Y_J x H.
    split => ij HijIJ i j Heq.
    rewrite Heq in HijIJ.
    apply ordered_pair_in_direct_product_to_in_and in HijIJ.
    apply H.
    apply HijIJ.
    apply HijIJ.
  Qed.

  Goal
    forall (I J:Collection U) (X_I Y_J: TypeOfSetOfFamilySet U),
    forall x:U,
      (forall i j:U, i∈I -> j∈J -> x ∈ X_I ⌞ i ∪ Y_J ⌞ j) -> (forall i:U, i ∈ I -> x ∈ X_I ⌞ i) \/ (forall j:U, j ∈ J -> x ∈ Y_J ⌞ j).
  Proof.
    move => I J X_I Y_J x H.
    apply forall_bound_or_in => i j.
    apply not_imply_to_or.
    move => Hn HiJ.
    apply DoubleNegativeElimination.
    move => Hn0.
    apply Hn.
    move => HiI.
    move: Hn0.
    apply imply_iff_notOr.
    suff: x ∈ X_I ⌞ i ∪ Y_J ⌞ j.
    case => x' Hx'XI.
    right.
    trivial.
    left.
    apply DoubleNegative.
    trivial.
    apply H.
    trivial.
    assumption.
  Qed.

  Theorem union_bigcap_family_set_eq_bigcap_ordered_pair_index:
    forall (I J:Collection U) (X_I Y_J: TypeOfSetOfFamilySet U),
      ⋂{ I , (fun i:U => (X_I ⌞ i)) } ∪ ⋂{ J , (fun j:U => (Y_J ⌞ j)) } =
      ⋂{ I × J, (fun ij:TypeOfOrderedPair U => (fun x:U => forall i j:U, ij=<|i,j|> -> x ∈ X_I ⌞ i ∪ Y_J ⌞ j))}.
  Proof.
    move => I J X_I Y_J.
    apply mutally_included_to_eq.
    split => x H.
    split => ij HijIJ i j Heq.
    rewrite Heq in HijIJ.
    apply ordered_pair_in_direct_product_to_in_and in HijIJ.
    inversion HijIJ as [HiI HjJ].
    inversion H.
    inversion H0.
    apply H2 in HiI.
    left.
    trivial.
    inversion H0.
    apply H2 in HjJ.
    right.
    apply H2.
    apply HijIJ.
    have L1: forall i j:U, i∈I -> j∈J -> x ∈ X_I ⌞ i ∪ Y_J ⌞ j.
    move => i j HiI HjJ.
    have L1: <|i,j|> ∈ I × J.
    apply in_and_to_ordered_pair_in_direct_product.
    split;trivial.
    inversion H.
    apply H0 in L1.
    apply L1.
    reflexivity.
    have L2: (forall i:U, i ∈ I -> x ∈ X_I ⌞ i) \/ (forall j:U, j ∈ J -> x ∈ Y_J ⌞ j).
    apply forall_bound_or_in => i j.
    apply not_imply_to_or.
    move => Hn HiJ.
    apply DoubleNegativeElimination.
    move => Hn0.
    apply Hn.
    move => HiI.
    move: Hn0.
    apply imply_iff_notOr.
    suff: x ∈ X_I ⌞ i ∪ Y_J ⌞ j.
    case => x' Hx'XI.
    right.
    trivial.
    left.
    apply DoubleNegative.
    trivial.
    apply L1.
    trivial.
    assumption.
    case L2 => H';[left|right];split;assumption.
  Qed.

  Theorem intersection_bigcup_family_set_eq_bigcup_ordered_pair_index:
    forall (I J:Collection U) (X_I Y_J: TypeOfSetOfFamilySet U),
      ⋃{ I , (fun i:U => (X_I ⌞ i)) } ∩ ⋃{ J , (fun j:U => (Y_J ⌞ j)) } =
      ⋃{ I × J, (fun ij:TypeOfOrderedPair U => (fun x:U => exists i j:U, ij=<|i,j|> /\ x ∈ X_I ⌞ i ∩ Y_J ⌞ j))}.
  Proof.
    move => I J X_I Y_J.
    apply mutally_included_to_eq.
    split => x H.
    inversion H.
    split.
    inversion H0.
    inversion H3 as [i [HiI HxXI]].
    inversion H1.
    inversion H5 as [j [HjJ HxYJ]].
    exists <|i,j|>.
    split.
    apply in_and_to_ordered_pair_in_direct_product.
    split;trivial.
    exists i.
    exists j.
    split.
    reflexivity.
    split; assumption.
    inversion H.
    inversion H0 as [ij].
    inversion H2 as [HijIJ].
    inversion H3 as [i [j]].
    inversion H4.
    rewrite H5 in HijIJ.
    inversion H6.
    apply ordered_pair_in_direct_product_to_in_and in HijIJ.
    inversion HijIJ as [HiI HjJ].
    split;split;[exists i|exists j];split;trivial.
  Qed.

  Theorem image_of_bigcup_eq_bigcup_image_of_family_set:
    forall (I:Collection U) (X_I: TypeOfSetOfFamilySet U) (F:TypeOfDirectProduct U),
      𝕴𝖒( F ,  ⋃{ I , (fun i:U => X_I ⌞ i) } ) = ⋃{ I , (fun i:U => (fun y:U => y ∈ 𝕴𝖒( F , X_I ⌞ i)))}.
  Proof.
    move => I X_I F.
    apply mutally_included_to_eq.
    split => y H.
    split.
    inversion H.
    inversion H0 as [x].
    inversion H2.
    inversion H3.
    inversion H5 as [i].
    inversion H7.
    exists i.
    split.
    trivial.
    split.
    exists x.
    split.
    trivial.
    assumption.
    inversion H as [y0].
    inversion H0 as [i].
    inversion H2.
    inversion H4.
    inversion H5 as [x].
    split.
    exists x.
    inversion H7.
    split.
    split.
    exists i.
    split;trivial.
    assumption.
  Qed.

  Theorem image_of_bigcap_included_bigcap_image_of_family_set:
    forall (I:Collection U) (X_I: TypeOfSetOfFamilySet U) (F:TypeOfDirectProduct U),
      𝕴𝖒( F ,  ⋂{ I , (fun i:U => X_I ⌞ i) } ) ⊂ ⋂{ I , (fun i:U => (fun y:U => y ∈ 𝕴𝖒( F , X_I ⌞ i)))}.
  Proof.
    move => I X_I F y H.
    split => i HiI.
    inversion H as [y0 [x0 []]].
    inversion H0.
    split.
    exists x0.
    apply H3 in HiI.
    split;trivial.
  Qed.

  Theorem inverse_image_of_bigcup_included_bigcup_inverse_image_of_family_set:
    forall (J:Collection U) (Y_J: TypeOfSetOfFamilySet U) (F:TypeOfDirectProduct U),
      𝕴𝖒( F ^-1 ,  ⋃{ J , (fun j:U => Y_J ⌞ j) } ) = ⋃{ J , (fun j:U => (fun x:U => x ∈ 𝕴𝖒( F^-1 , Y_J ⌞ j)))}.
  Proof.
    move => J Y_J F.
    apply mutally_included_to_eq.
    split => x H.
    split.
    inversion H as [x0].
    inversion H0 as [y].
    inversion H2.
    inversion H3 as [y0 [j]].
    exists j.
    inversion H5 as [HjJ HyYJ].
    split;trivial.
    split.
    exists y.
    split;trivial.
    inversion H.
    inversion H as [x1 [j [HjJ HxIm]]].
    split.
    inversion HxIm as [x2 [y [HyYJ]]].
    exists y.
    split.
    split.
    exists j.
    split;trivial.
    assumption.
  Qed.

  Theorem inverse_image_of_bigcap_included_bigcap_inverse_image_of_family_set:
    forall (f:U -> U) (J A B:Collection U) (Y_J: TypeOfSetOfFamilySet U) (F:TypeOfDirectProduct U),
      J<>`Ø` ->
      MappingFunction f A B ->
      F = GraphOfFunction f A B ->
      𝕴𝖒( F ^-1 ,  ⋂{ J , (fun j:U => Y_J ⌞ j) } ) = ⋂{ J , (fun j:U => (fun x:U => x ∈ 𝕴𝖒( F^-1 , Y_J ⌞ j)))}.
  Proof.
    move => f J A B Y_J F HnEJ Hf HF.
    apply mutally_included_to_eq.
    split => x H.
    inversion H as [x0 [y [HyI HFI]]].
    inversion HyI as [y0].
    split => j HjJ.
    apply H1 in HjJ.
    split.
    exists y.
    split;trivial.
    apply not_empty_collection_to_exists_element_in_collection in HnEJ.
    inversion HnEJ as [j].
    inversion H as [x0].
    apply H1 in H0.
    inversion H0 as [x1].
    split.
    inversion H3 as [y].
    inversion H5.
    exists y.
    split.
    split => j0 Hj0J.
    apply H1 in Hj0J.
    inversion Hj0J as [x2].
    inversion H8 as [y'].
    inversion H10.
    inversion H7 as [x'' y''].
    inversion H12 as [x''' y'''].
    apply ordered_pair_swap in H14.
    apply ordered_pair_swap in H16.
    rewrite H14 in H13.
    rewrite H16 in H15.
    suff: y=y'.
    move => H'.
    rewrite H'.
    trivial.
    rewrite HF in H13.
    rewrite HF in H15.
    inversion H13 as [Z3 [x3 [y3]]].
    inversion H15 as [Z4 [x4 [y4]]].
    inversion H17 as [Heq1 [Hyfx]].
    inversion H19 as [Heq2 [Hy'fx]].
    apply ordered_pair_to_and in Heq1.
    apply ordered_pair_to_and in Heq2.
    inversion Heq1 as [Hxeqx3 Hyeqy3].
    inversion Heq2 as [Hxeqx4 Hy'eqy4].
    rewrite -Hxeqx3 -Hyeqy3 in Hyfx.
    rewrite -Hxeqx4 -Hy'eqy4 in Hy'fx.
    rewrite Hyfx Hy'fx.
    reflexivity.
    assumption.
  Qed.

  Theorem a_element_of_covering_family_set_is_subset_of_covered_set:
    forall(I X:Collection U) (X_I: TypeOfSetOfFamilySet U),
      CoveringByFamilySet X I (fun i:U => X_I ⌞ i) ->
      forall i:U, i ∈ I -> X_I ⌞ i ⊂ X.
  Proof.
    move =>  I X X_I HC i HiI x HXIi.
    inversion HC.
    split.
    exists i.
    split;trivial.
  Qed.

  Theorem collection_of_family_set_is_subset_of_power_set:
    forall (I X:Collection U) (X_I: TypeOfSetOfFamilySet U),
      CoveringByFamilySet X I (fun i:U => X_I ⌞ i) ->
      BuilderOfFamilySet I (fun i:U => X_I ⌞ i) ⊂ 𝔓(X).
  Proof.
    move => I X X_I HC Xi HXiXI.
    split => x H.
    inversion HC.
    split.
    inversion HXiXI.
    inversion H1 as [i].
    inversion H3 as [HiI Heq].
    exists i.
    split.
    trivial.
    rewrite -Heq.
    assumption.
  Qed.

  Theorem bigcup_of_familyset_eq_bigcup_of_collection_of_familyset:
    forall (I:Collection U) (X_I: TypeOfSetOfFamilySet U),
      ⋃{ I , fun i:U => X_I ⌞ i } = ⋃ (BuilderOfFamilySet I (fun i:U => X_I ⌞ i)).
  Proof.
    move => I X_I.
    apply mutally_included_to_eq.
    split => x H.
    split.
    inversion H.
    inversion H0 as [i].
    inversion H2.
    exists (X_I ⌞ i).
    split;[trivial|
           split;exists i;split;trivial].
    inversion H.
    inversion H0 as [Xi].
    inversion H2.
    inversion H4.
    inversion H5 as [i].
    split.
    inversion H7.
    exists i.
    split;[trivial|rewrite -H9;trivial].
  Qed.



  
End FamilyCollection.
