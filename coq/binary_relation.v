From mathcomp Require Import ssreflect.

Require Import collect_operator.
Require Import direct_product.

Definition BinaryRelation U := U -> U -> Prop.

Inductive GraphOfBinaryRelation {U:Type} (R:BinaryRelation U) (A B:Collection U)
  : TypeOfDirectProduct U :=
| definition_of_graph_of_binary_relation:
    forall Z:TypeOfOrderedPair U, (exists x y:U, Z = <|x,y|> /\ R x y /\ <|x,y|> ∈ A × B) -> Z ∈ GraphOfBinaryRelation R A B.

Inductive DomainOfCorrespondence {U:Type} (G:TypeOfDirectProduct U) : Collection U :=
| definition_of_domain_of_correspondence:
    forall x:U, x ∈ FirstProjection G -> x ∈ DomainOfCorrespondence G.

Inductive RangeOfCorrespondence {U:Type} (G:TypeOfDirectProduct U) : Collection U :=
| definition_of_range_of_correspondence:
    forall y:U, y ∈ SecondProjection G -> y ∈ RangeOfCorrespondence G.

Inductive ImageOfCorrespondence {U:Type} (G:TypeOfDirectProduct U) (C:Collection U) : Collection U :=
| definition_of_image_of_correspondence:
    forall y:U, (exists x:U, x ∈ C /\ <|x,y|> ∈ G) -> y ∈ ImageOfCorrespondence G C.

Inductive TransposeOfCorrespondence {U:Type} (G:TypeOfDirectProduct U) : TypeOfDirectProduct U :=
| definition_of_transpose_correspondene:
   forall x y:U, <|x,y|> ∈ G -> <|y,x|> ∈ TransposeOfCorrespondence G.

(* 𝕯: Unicode:1D56F, 𝕽: Unicode:1D57D *)
Notation "𝕯( G )" := (DomainOfCorrespondence G) (at level 45).
Notation "𝕽( G )" := (RangeOfCorrespondence G) (at level 45).
Notation "𝕴𝖒( G , C )" := (ImageOfCorrespondence G C) (at level 45).
Notation "G ^-1" := (TransposeOfCorrespondence G) (at level 34).

Section BinaryRelation.

  Variable U:Type.
  Variable R: BinaryRelation U.

  Theorem graph_of_binary_releation_empty_range:
    forall (A:Collection U), GraphOfBinaryRelation R A (`Ø`) = `Ø`.
  Proof.
    move => A.
    apply empty_collection_is_noone_in_collection => Z.
    case => Z0.
    case => [x [y [HZ0 [HR HA]]]].
    apply (exists_element_in_collection_to_not_empty_collection (TypeOfOrderedPair U) (A × `Ø`)).
    exists Z0.
    rewrite HZ0.
    trivial.
    apply direct_product_empty_r.
  Qed.

  Theorem graph_of_binary_releation_empty_domaion:
    forall (B:Collection U), GraphOfBinaryRelation R (`Ø`) B = `Ø`.
  Proof.
    move => B.
    apply empty_collection_is_noone_in_collection => Z.
    case => Z0.
    case => [x [y [HZ0 [HR HB]]]].
    apply (exists_element_in_collection_to_not_empty_collection (TypeOfOrderedPair U) (`Ø` × B)).
    exists Z0.
    rewrite -HZ0 in HB.
    trivial.
    apply direct_product_empty_l.
  Qed.

  Theorem relation_determine_domain:
    forall (A B:Collection U) (G:TypeOfDirectProduct U),
      G = GraphOfBinaryRelation R A B -> 𝕯( G ) ⊂ A.
  Proof.
    move => A B G HG x HDG.
    inversion HDG as [x0 HFG].
    inversion HFG as [x1 H0].
    case: H0 => y HGp.
    rewrite HG in HGp.
    inversion HGp.
    inversion H0 as [x2 [y2 [Hp [HR HAB]]]].
    rewrite -Hp in HAB.
    apply ordered_pair_in_direct_product_to_in_and in HAB.
    inversion HAB.
    trivial.
  Qed.

  Theorem relation_determine_range:
    forall (A B:Collection U) (G:TypeOfDirectProduct U),
      G = GraphOfBinaryRelation R A B -> 𝕽( G ) ⊂ B.
  Proof.
    move => A B G HG y HRG.
    inversion HRG as [y0 HSG].
    inversion HSG as [y1 H0].
    case: H0 => x HGp.
    rewrite HG in HGp.
    inversion HGp.
    inversion H0 as [x2 [y2 [Hp [HR HAB]]]].
    inversion H2.
    rewrite -Hp in HAB.
    apply ordered_pair_in_direct_product_to_in_and in HAB.
    inversion HAB.
    trivial.
  Qed.

  Theorem correspondence_to_inverse_correspondence:
    forall (x y:U) (A B:Collection U) (G:TypeOfDirectProduct U),
      G = GraphOfBinaryRelation R A B -> <|x,y|> ∈ G -> <|y,x|> ∈ G ^-1.
  Proof.
    move => x y A B G HG.
    rewrite HG.
    move => H.
    split. by [].
  Qed.

  Theorem inverse_correspondence_to_correspondence:
    forall (x y:U) (A B:Collection U) (G:TypeOfDirectProduct U),
      G = GraphOfBinaryRelation R A B -> <|y,x|> ∈ G ^-1 -> <|x,y|> ∈ G.
  Proof.
    move => x y A B G HG.
    rewrite HG => H0.
    inversion H0.
    apply ordered_pair_swap in H.
    rewrite H in H1. by [].
  Qed.

  Theorem correspondence_iff_inverse_correspondence:
    forall (x y:U) (A B:Collection U) (G:TypeOfDirectProduct U),
      G = GraphOfBinaryRelation R A B -> <|x,y|> ∈ G <-> <|y,x|> ∈ G ^-1.
  Proof.
    move => x y A B G HG.
    rewrite /iff; split;
      [apply (correspondence_to_inverse_correspondence x y A B G)|
       apply (inverse_correspondence_to_correspondence x y A B G)]; by [].
  Qed.

  Theorem correspondence_to_double_inverse_correspondence:
    forall (x y:U) (A B:Collection U) (G:TypeOfDirectProduct U),
      G = GraphOfBinaryRelation R A B -> <|x,y|> ∈ G -> <|x,y|> ∈ G ^-1 ^-1.
  Proof.
    move => x y A B G HG HIIG.
    split.
    split. trivial.
  Qed.

  Theorem double_inverse_correspondence_to_correspondence:
    forall (x y:U) (A B:Collection U) (G:TypeOfDirectProduct U),
      G = GraphOfBinaryRelation R A B -> <|x,y|> ∈ G ^-1 ^-1 -> <|x,y|> ∈ G.
  Proof.
    move => x y A B G HG HIIG.
    inversion HIIG as [y0 x0 H0].
    inversion H0 as [x1 y1].
    apply ordered_pair_swap in H2.
    rewrite H2 in H1. trivial.
  Qed.

  Theorem binary_relation_to_in_graph:
    forall (x y:U) (A B:Collection U) (G:TypeOfDirectProduct U),
      <|x,y|> ∈ A × B /\ G = GraphOfBinaryRelation R A B -> (R x y -> <|x,y|> ∈ G).
  Proof.
    move => x y A B G.
    case => [HAB HG HR].
    rewrite HG.
    split.
    exists x.
    exists y.
    split; by[].
  Qed.

  Theorem in_graph_to_binary_relation:
      forall (x y:U) (A B:Collection U) (G:TypeOfDirectProduct U),
        <|x,y|> ∈ A × B /\ G = GraphOfBinaryRelation R A B -> (<|x,y|> ∈ G -> R x y).
  Proof.
    move => x y A B G.
    case => [HAB HG].
    rewrite HG => H.
    inversion H.
    inversion H0 as [x0 [y0 [H2 [HR0 HAB0]]]].
    rewrite -H2 in HAB0.
    apply ordered_pair_to_and in H2.
    inversion H2.
    rewrite H3 H4.
    trivial.
  Qed.

  Theorem binary_relation_iff_in_graph:
    forall (x y:U) (A B:Collection U) (G:TypeOfDirectProduct U),
      <|x,y|> ∈ A × B /\ G = GraphOfBinaryRelation R A B -> (R x y <-> <|x,y|> ∈ G).
  Proof.
    move => x y A B G.
    case => [HAB HG].
    rewrite /iff.
    split;
      [apply (binary_relation_to_in_graph x y A B G)|
       apply (in_graph_to_binary_relation x y A B G)];
      split; by [].
  Qed.

  Theorem graph_of_correspondence_is_subset_of_direct_product:
    forall (A B:Collection U) (G:TypeOfDirectProduct U),
      G = GraphOfBinaryRelation R A B ->
      G ⊂ A × B.
  Proof.
    move => A B G HG Z HZG.
    rewrite HG in HZG.
    inversion HZG as [Z' H HZZ].
    inversion H as [x [y [HZ [HR HAB]]]].
    rewrite HZ.
    apply HAB.
  Qed.

  Theorem image_of_graph_is_subset_range:
    forall (A B C:Collection U) (G:TypeOfDirectProduct U),
      G = GraphOfBinaryRelation R A B -> 𝕴𝖒( G , C ) ⊂ B.
  Proof.
    move => A B C G HG y HI.
    inversion HI as [y0 [x [HC HGp]]].
    rewrite HG in HGp.
    inversion HGp.
    inversion H0 as [x1 [y1 [Heq [HR1 HAB1]]]].
    rewrite -Heq in HAB1.
    apply ordered_pair_in_direct_product_to_in_and in HAB1.
    apply HAB1.
  Qed.

  Theorem image_of_domain_is_empty_is_empty:
    forall (A B:Collection U) (G:TypeOfDirectProduct U),
      G = GraphOfBinaryRelation R A B -> 𝕴𝖒( G , `Ø` ) = `Ø`.
  Proof.
    move => A B G HG.
    apply mutally_included_to_eq.
    split.
    move => y.
    case => y0.
    case => x0.
    case => H Hp.
    rewrite HG in Hp.
    inversion Hp.
    inversion H0 as [x1 [y1 [Hxy [HR HxyG]]]].
    rewrite -Hxy in HxyG.
    apply ordered_pair_in_direct_product_to_in_and in HxyG.
    inversion HxyG.
    have L1: x0 ∈ `Ø` /\ y0 ∈ B.
    split; trivial.
    apply in_and_to_ordered_pair_in_direct_product in L1.
    rewrite -direct_product_empty_comm in L1.
    apply ordered_pair_in_direct_product_to_in_and in L1.
    inversion L1.
    trivial.
    apply all_collection_included_empty.
  Qed.

  Theorem condition_of_exists_element_in_image_of_binary_relation:
    forall (A B C:Collection U) (G:TypeOfDirectProduct U),
      (forall x:U, x ∈ A -> exists y:U, R x y /\ y ∈ B) ->
      C <> `Ø` ->
      C ⊂ A ->
      G = GraphOfBinaryRelation R A B ->
      exists y:U, y ∈ 𝕴𝖒( G , C ).
  Proof.
    move => A B C G HR HNC HCA HG.
    apply (not_empty_collection_has_least_a_element U C) in HNC.
    inversion HNC as [x HC].
    move: (HR x) => HRx.
    have HA: x ∈ A.
    apply HCA. trivial.
    have HEy: exists y :U, R x y /\ y ∈ B.
    apply HRx. trivial.
    inversion HEy as [y].
    exists y.
    split.
    exists x.
    split;[trivial|rewrite HG].
    split.
    exists x.
    exists y.
    split;[reflexivity|
           inversion H;split;
           [trivial|
            apply ordered_pair_in_direct_product_iff_in_and;split;trivial]].
  Qed.

  Theorem cup_domain_cup_image:
    forall (A B C D:Collection U) (G:TypeOfDirectProduct U),
      G = GraphOfBinaryRelation R A B ->
      𝕴𝖒( G , C ∪ D ) = 𝕴𝖒( G , C ) ∪ 𝕴𝖒( G , D ).
  Proof.
    move => A B C D G HG.
    apply mutally_included_to_eq.
    split => y H.
    inversion H as [y0 [x]].
    inversion H0.
    rewrite HG in H3.
    inversion H3 as [Z [x1 [y1]]].
    inversion H2; [left|right];
      split; exists x; split;
        trivial; rewrite HG; trivial.
    split.
    inversion H as [y0 H0|y0 H0];
      inversion H0;
      inversion H2 as [x];
      inversion H4;
      exists x.
    split;[left;trivial|trivial].
    split;[right;trivial|trivial].
  Qed.

  Theorem cap_image_included_cap_domain:
    forall (A B C D:Collection U) (G:TypeOfDirectProduct U),
      G = GraphOfBinaryRelation R A B ->
      𝕴𝖒( G , C ∩ D ) ⊂ 𝕴𝖒( G , C ) ∩ 𝕴𝖒( G , D ).
  Proof.
    move => A B C D G HG y H.
    inversion H as [y0].
    inversion H0 as [x].
    inversion H2.
    inversion H3.
    split; split; exists x; split; trivial.
  Qed.

End BinaryRelation.
