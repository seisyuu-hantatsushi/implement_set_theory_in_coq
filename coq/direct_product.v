From mathcomp Require Import ssreflect.

Require Import collect_operator.

Inductive DirectProduct {U:Type} (X Y:Collection U) : Collection (Collection (Collection U)) :=
| definition_of_direct_product:
    forall Z: Collection (Collection U),
      (exists x:U, exists y:U, (x ∈ X /\ y ∈ Y /\ Z = <|x, y|>)) -> Z ∈ DirectProduct X Y.

Notation "A × B" := (DirectProduct A B) (right associativity, at level 29).

Inductive FirstProjection {U:Type} (G: Collection (Collection (Collection U))) : Collection U :=
| first_projection_accessor: forall x:U, (exists y:U, <|x,y|> ∈ G) -> FirstProjection G x.

Inductive SecondProjection {U:Type} (G: Collection (Collection (Collection U))) : Collection U :=
| second_projection_accessor: forall y:U, (exists x:U, <|x,y|> ∈ G) -> SecondProjection G y.

Section DirectProduct.
  Variable U:Type.

  Theorem ordered_pair_in_direct_product_to_in_and:
    forall (A B: Collection U) (a b:U), <|a,b|> ∈ A × B -> a ∈ A /\ b ∈ B.
  Proof.
    move => A B a b H.
    inversion H.
    inversion H0 as [x].
    inversion H2 as [y].
    case: H3 => H3. case => H4 H5.
    apply ordered_pair_to_and in H5.
    case: H5 => H5 H6.
    split; [rewrite H5 | rewrite H6]; by[].
  Qed.

  Theorem in_and_to_ordered_pair_in_direct_product:
    forall (A B: Collection U) (a b:U), a ∈ A /\ b ∈ B -> <|a,b|> ∈ A × B.
  Proof.
    move => A B a b.
    case => H0 H1.
    split.
    exists a. exists b.
    split;[by []|split; by[]].
  Qed.

  Theorem ordered_pair_in_direct_product_iff_in_and:
    forall (A B: Collection U) (a b:U), <|a,b|> ∈ A × B <-> a ∈ A /\ b ∈ B.
  Proof.
    move => A B a b.
    rewrite /iff. split.
    apply ordered_pair_in_direct_product_to_in_and.
    apply in_and_to_ordered_pair_in_direct_product.
  Qed.

  Theorem direct_product_empty_l:
    forall X: Collection U, `Ø` × X = `Ø`.
  Proof.
    move => X.
    apply mutally_included_to_eq.
    split => Z' H.
    inversion H as [X' H1].
    inversion H1 as [x H2].
    inversion H2 as [y].
    case: H3 => H3. case => H4 H5.
    apply DoubleNegativeElimination.
    move => H6.
    move: H3.
    apply noone_in_empty.
    apply DoubleNegativeElimination.
    move => HN.
    move: H.
    apply noone_in_empty.
  Qed.

  Theorem direct_product_empty_r:
    forall X: Collection U, X × `Ø` = `Ø`.
  Proof.
    move => X.
    apply mutally_included_to_eq.
    split => Z' H.
    inversion H as [X' H1].
    inversion H1 as [x H2].
    inversion H2 as [y].
    case: H3 => H3. case => H4 H5.
    apply DoubleNegativeElimination => H6.
    move: H4.
    apply noone_in_empty.
    apply DoubleNegativeElimination.
    move => HN.
    move: H.
    apply noone_in_empty.
  Qed.

  Theorem direct_product_empty_comm:
    forall X: Collection U, X × `Ø` = `Ø` × X.
  Proof.
    move => X.
    rewrite direct_product_empty_r.
    rewrite direct_product_empty_l.
    reflexivity.
  Qed.

  Theorem direct_product_included_empty: forall (X Y : Collection U), `Ø` ⊂ X × Y.
  Proof.
    move => X Y z.
    apply Contraposition => H.
    apply noone_in_empty.
  Qed.

  Theorem direct_product_is_empty_to_or_empty:
    forall (X Y : Collection U), X × Y = `Ø` -> X = `Ø` \/ Y = `Ø`.
  Proof.
    move => X Y.
    apply Contraposition => H.
    apply LawOfDeMorgan_NegtationOfDisjunction in H.
    inversion H as [HX HY].
    suff: (exists x:U, x ∈ X) /\ (exists y:U, y ∈ Y).
    move => H0 H1.
    apply exists_bound_and_out in H0.
    move: H0.
    apply DeMorganNotExists => x.
    apply DeMorganNotExists => y.
    move => H0.
    apply ordered_pair_in_direct_product_iff_in_and in H0.
    move: H0.
    rewrite H1.
    apply noone_in_empty.
    split; apply DeMorganNotForallNot_Open; move => H0; [apply HX|apply HY]; apply empty_collection_is_noone_in_collection; by [].
  Qed.

  Theorem or_empty_to_direct_product_is_empty:
    forall (X Y : Collection U), X = `Ø` \/ Y = `Ø` -> X × Y = `Ø`.
  Proof.
    move => X Y.
    case => H; rewrite H; [apply direct_product_empty_l|apply direct_product_empty_r].
  Qed.

  Theorem direct_product_is_empty_iff_or_empty:
    forall (X Y : Collection U), X × Y = `Ø` <-> X = `Ø` \/ Y = `Ø`.
  Proof.
    move => X Y.
    rewrite /iff. split.
    apply direct_product_is_empty_to_or_empty.
    apply or_empty_to_direct_product_is_empty.
  Qed.

  Theorem direct_product_included_concrete_ordered_pair:
    forall (X Y W Z:Collection U), W × Z ⊂ X × Y -> forall (x y:U), <|x, y|> ∈ W × Z -> <|x, y|> ∈ X × Y.
  Proof.
    move => X Y W Z H x y H0.
    apply H. by [].
  Qed.

  Theorem ordered_pair_in_direct_product_included_to_and:
    forall (X Y W Z:Collection U), (forall (x y:U), <|x, y|> ∈ W × Z -> <|x, y|> ∈ X × Y) -> (forall (x y:U), (x ∈ W /\ y ∈ Z) -> (x ∈ X /\ y ∈ Y)).
  Proof.
    move => X Y W Z H x y H0.
    apply ordered_pair_in_direct_product_iff_in_and.
    apply ordered_pair_in_direct_product_iff_in_and in H0.
    move: H0.
    apply H.
  Qed.

  Theorem direct_product_included_to_and:
    forall (X Y W Z:Collection U), W × Z ⊂ X × Y -> forall (x y:U), (x ∈ W /\ y ∈ Z) -> (x ∈ X /\ y ∈ Y).
  Proof.
    move => X Y W Z H x y.
    apply ordered_pair_in_direct_product_included_to_and.
    move => x0 y0.
    apply: (direct_product_included_concrete_ordered_pair X Y W Z).
    apply H.
  Qed.

  Theorem each_included_to_direct_product_included:
    forall (X Y W Z:Collection U), W × Z = `Ø` \/ (W ⊂ X /\ Z ⊂ Y) -> W × Z ⊂ X × Y.
  Proof.
    move => X Y W Z.
    case;[move => H0;rewrite H0;apply direct_product_included_empty|
          case => H0 H1 X';case => [Y' [x [y [HxW [HyZ HY']]]]];
                                   rewrite HY';
                                   apply in_and_to_ordered_pair_in_direct_product;
                                   split; [apply H0|apply H1]]; by[].
  Qed.

  Theorem direct_product_included_to_each_included:
    forall (X Y W Z:Collection U), W × Z ⊂ X × Y -> W × Z = `Ø` \/ (W ⊂ X /\ Z ⊂ Y).
  Proof.
    move => X Y W Z H.
    suff: ((forall x:U, x ∉ Z) \/ W ⊂ X) /\ ((forall x:U, x ∉ W) \/ Z ⊂ Y).
    move => H0.
    inversion H0.
    inversion H1 as [H3|];
      [left; apply empty_collection_is_noone_in_collection in H3; rewrite H3; apply direct_product_empty_r|
       inversion H2 as [H4|];
       [left;apply empty_collection_is_noone_in_collection in H4; rewrite H4; apply direct_product_empty_l|
        right;split;by []]].
    have L1: forall (x y:U), (x ∈ W /\ y ∈ Z) -> (x ∈ X /\ y ∈ Y).
    move: H. apply direct_product_included_to_and.
    have L2: forall (x y:U), ((x ∈ W /\ y ∈ Z) -> x ∈ X) /\ ((x ∈ W /\ y ∈ Z) -> y ∈ Y).
    move => x y.
    apply and_imply_and_dist.
    apply L1.
    have L3: forall (x y:U), (x ∉ W \/ y ∉ Z \/ x ∈ X) /\ (x ∉ W \/ y ∉ Z \/ y ∈ Y).
    move => x y.
    case: (L2 x y) => LH0 LH1.
    split;
      apply LawOfAssociateAtOr;
      apply not_imply_to_or => H0;
                                 apply LawOfDeMorgan_NegtationOfDisjunction in H0;
                                 [apply LH0|apply LH1];
                                 case H0 => H1 H2;
                                              apply DoubleNegativeElimination in H1;
                                              apply DoubleNegativeElimination in H2;
                                              split; by [].
    have L4: forall (x y:U), y ∉ Z \/ x ∉ W \/ x ∈ X.
    move => x y.
    case: (L3 x y) => H0 H1; case H0 => H2;
                                          [right; left; by []|
                                           case H2 => H3; [left|right;right]; by []].
    have L5: forall (x y:U), x ∉ W \/ y ∉ Z \/ y ∈ Y.
    move => x y.
    case: (L3 x y) => H0 H1. by [].
    have L6: (forall (x y:U), y ∉ Z \/ (x ∈ W -> x ∈ X)) /\ forall x y : U, x ∉ W \/ (y ∈ Z -> y ∈ Y).
    split; move => x y; [move: (L4 x y) => L4xy; case L4xy => H0;[left;apply H0|
                                                                  right;apply imply_iff_notOr]|
                         move: (L5 x y) => L5xy; case L5xy => H0;[left;apply H0|
                                                                  right;apply imply_iff_notOr]]; by[].
    case L6 => L61 L62.
    split; apply forall_bound_or_in; by[].
  Qed.

  Theorem direct_product_included_iff:
    forall (X Y W Z:Collection U), W × Z ⊂ X × Y <-> W × Z = `Ø` \/ (W ⊂ X /\ Z ⊂ Y).
  Proof.
    move => X Y W Z.
    rewrite /iff. split.
    apply direct_product_included_to_each_included.
    apply each_included_to_direct_product_included.
  Qed.

  Theorem direct_product_dist_union_l:
    forall (A B C:Collection U), A × ( B ∪ C ) = A × B ∪ A × C.
  Proof.
    move => A B C.
    apply mutally_included_to_eq.
    split => Z' H0.
    inversion H0.
    inversion H as [x [y [HA [HBC]]]].
    rewrite H2.
    case HBC => y0 HB;[left|right];
                  apply ordered_pair_in_direct_product_iff_in_and;
                  split; by[].
    inversion H0 as [Z0' HAX|Z0' HAX];
      inversion HAX as [Z1' [x [y [HA [HB HZ']]]]];
      rewrite HZ';
      apply ordered_pair_in_direct_product_iff_in_and.
    split; [|left]; by [].
    split; [|right]; by [].
  Qed.

  Theorem direct_product_dist_union_r:
    forall (A B C:Collection U), ( A ∪ B ) × C = A × C ∪ B × C.
  Proof.
    move => A B C.
    apply mutally_included_to_eq.
    split; move => Z' H.
    inversion H as [Z0' [x [y [HAB [HC]]]]].
    inversion HAB as [x0 HA|x0 HB];
      [left|right];
      rewrite H0; apply ordered_pair_in_direct_product_iff_in_and;
        split; by[].
    inversion H as [Z0' HAC|Z0' HBC];
      [inversion HAC as [Z1' [x [y [HA [HC HZ']]]]]
      |inversion HBC as [Z1' [x [y [HB [HC HZ']]]]]];
      rewrite HZ';
      apply ordered_pair_in_direct_product_iff_in_and;
      split.
    left. by []. by[].
    right. by []. by [].
  Qed.

  Theorem direct_product_dist_intersection_l:
    forall (A B C:Collection U), A × ( B ∩ C ) = A × B ∩ A × C.
  Proof.
    move => A B C.
    apply mutally_included_to_eq.
    split => Z' H.
    +inversion H as [Z0' [x [y [HA [HBC HZ]]]]].
     inversion HBC as [HB HC].
     rewrite HZ.
     split; apply ordered_pair_in_direct_product_iff_in_and; split; by [].
    -inversion H as [Z0' HAB HAC HZ].
     inversion HAB as [Z1' [x0 [y0 [HA0 [HB0 HZ1]]]]].
     inversion HAC as [Z2' [x1 [y1 [HA1 [HC1 HZ2]]]]].
     rewrite HZ1.
     have L1: x0 = x1 /\ y0 = y1.
     rewrite HZ1 in HZ2.
     apply ordered_pair_to_and in HZ2. by [].
     inversion L1.
     apply ordered_pair_in_direct_product_iff_in_and.
     split;[by []|apply in_and_to_in_intersection].
     split;[|rewrite H3];by [].
  Qed.

  Theorem direct_product_dist_intersection_r:
    forall (A B C:Collection U), ( A ∩ B ) × C = A × C ∩ B × C.
  Proof.
    move => A B C.
    apply mutally_included_to_eq.
    split => Z' H.
    +inversion H as [Z0' [x [y [HAB [HC HZ]]]]].
     inversion HAB as [x0 HA HB].
     split; rewrite HZ; apply ordered_pair_in_direct_product_iff_in_and; split; by [].
    +inversion H as [Z0' HAB HAC HZ].
     inversion HAB as [Z1' [x0 [y0 [HA0 [HB0 HZ1]]]]].
     inversion HAC as [Z2' [x1 [y1 [HB1 [HC1 HZ2]]]]].
     rewrite HZ1.
     have L1: x0 = x1 /\ y0 = y1.
     rewrite HZ1 in HZ2.
     apply ordered_pair_to_and in HZ2. by [].
     inversion L1.
     apply ordered_pair_in_direct_product_iff_in_and.
     rewrite -H2 in HB1.
     split; by[].
  Qed.
  
End DirectProduct.

