From mathcomp Require Import ssreflect.

Require Import collect_operator.
Require Import direct_product.
Require Import binary_relation.

Definition GraphOfMapping {U:Type} (G:TypeOfDirectProduct U) (A B:Collection U) :=
  G ⊂ A × B /\ forall x:U, x ∈ A -> exists! y:U, <|x,y|> ∈ G.

Definition MappingFunction {U:Type} (f: U -> U) (A B:Collection U) :=
  forall x:U, x ∈ A -> exists y:U, y = f x /\ y ∈ B.

Definition GraphOfFunction {U:Type} (f: U -> U) (A B:Collection U) :
  TypeOfDirectProduct U := GraphOfBinaryRelation (fun (x y:U) => y = f x) A B.

Section Mapping.
  Variable U:Type.
  Variable f: U -> U.

  Theorem function_determine_domain:
    forall (A B:Collection U) (G:TypeOfDirectProduct U),
      G = GraphOfFunction f A B -> 𝕯( G ) ⊂ A.
  Proof.
    move => A B G HG.
    move: (relation_determine_domain U (fun (x y:U) => y = f x) A B G).
    apply.
    rewrite HG.
    reflexivity.
  Qed.

  Theorem function_determine_range:
    forall (A B:Collection U) (G:TypeOfDirectProduct U),
      G = GraphOfFunction f A B -> 𝕽( G ) ⊂ B.
  Proof.
    move => A B G HG.
    move: (relation_determine_range U (fun (x y:U) => y = f x) A B G).
    apply.
    rewrite HG.
    reflexivity.
  Qed.

  Theorem direct_product_included_graph_of_function:
    forall (A B:Collection U) (G:TypeOfDirectProduct U),
      G = GraphOfFunction f A B -> G ⊂ A × B.
  Proof.
    move => A B G.
    apply graph_of_correspondence_is_subset_of_direct_product.
  Qed.

  Lemma rewrite_function_range:
    forall (A B:Collection U),
      (forall x:U, exists y:U, y = f x /\ <|x, y|> ∈ A × B) ->
      (forall x:U, exists y:U, x ∈ A /\ y = f x /\ y ∈ B).
  Proof.
    move => A B H x.
    move: (H x) => Hx.
    inversion Hx as [y [Hf HAB]].
    exists y.
    apply ordered_pair_in_direct_product_to_in_and in HAB.
    inversion HAB as [HA HB].
    split;[trivial|split; trivial].
  Qed.

  Theorem function_satisfies_graph_of_mapping:
    forall (A B:Collection U) (G:TypeOfDirectProduct U),
      (forall x:U, exists y:U, y = f x /\ <|x, y|> ∈ A × B) ->
      G = GraphOfFunction f A B ->
      GraphOfMapping G A B.
  Proof.
    move => A B G HF HG.
    split.
    +apply direct_product_included_graph_of_function. by [].
    +move => x HA.
     move: (HF x) => HFx.
     inversion HFx as [y []].
     exists y.
     split.
     rewrite HG.
     split.
     exists x.
     exists y.
     split; [reflexivity|split;trivial].
     move => z HG0.
     rewrite HG in HG0.
     inversion HG0.
     inversion H1 as [x0 [z0 [Heqz [Hfz HABz]]]].
     apply ordered_pair_to_and in Heqz.
     inversion Heqz.
     rewrite -H3 -H4 in Hfz.
     rewrite -Hfz in H.
     trivial.
  Qed.

  Theorem image_of_function_of_domain_is_empty_is_empty:
    forall (A B:Collection U) (G:TypeOfDirectProduct U),
      G = GraphOfFunction f A B -> 𝕴𝖒( G , `Ø` ) = `Ø`.
  Proof.
    move => A B G HG.
    apply (image_of_domain_is_empty_is_empty U (fun x y:U => y = f x) A B).
    rewrite HG.
    reflexivity.
  Qed.

  Theorem condition_of_image_is_not_empty:
    forall (A B C:Collection U) (G:TypeOfDirectProduct U),
      MappingFunction f A B ->
      C <> `Ø` -> C ⊂ A ->
      G = GraphOfFunction f A B ->
      exists (y:U), y ∈ 𝕴𝖒( G , C ).
  Proof.
    move => A B C G HF HNEC HCA HG.
    apply not_empty_collection_has_least_a_element in HNEC.
    inversion HNEC as [x HC].
    have L1: x ∈ A.
    apply HCA.
    trivial.
    apply HF in L1.
    inversion L1 as [y].
    exists y.
    split.
    exists x.
    split; [apply HC|rewrite HG].
    split.
    exists x.
    exists y.
    split;[trivial|split;[apply H|apply in_and_to_ordered_pair_in_direct_product]].
    split;[apply HCA;trivial|apply H].
  Qed.

  Goal
    forall (A B C D:Collection U) (G:TypeOfDirectProduct U),
      G = GraphOfFunction f A B ->
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
    inversion H as [y0 H0|y0 H0].
    inversion H0.
    inversion H2 as [x].
    exists x.
    inversion H4.
    split.
    left.
    trivial.
    trivial.
  Qed.
End Mapping.
