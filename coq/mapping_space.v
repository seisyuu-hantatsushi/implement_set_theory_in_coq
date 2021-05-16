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

  Theorem element_of_mapping_space_is_function:
    forall (X Y: Collection U) (F:TypeOfDirectProduct U),
      F ∈ MappingSpace X Y -> exists f:U->U,MappingFunction f X Y /\ F = GraphOfFunction f X Y.
  Proof.
    move => X Y F HFM.
    inversion HFM.
    apply H.
  Qed.

  Theorem powerset_of_product_included_mapping_space:
    forall (X Y: Collection U), MappingSpace X Y ⊂ 𝔓(X × Y).
  Proof.
    move => X Y F H.
    split => f H'.
    inversion H.
    inversion H0 as [f' [Hf HF]].
    rewrite HF in H'.
    inversion H'.
    inversion H2 as [x [y [Heq [Hyf'x HXY]]]].
    rewrite -Heq in HXY.
    assumption.
  Qed.

  Theorem element_of_mapping_space_to_graph:
    forall (A B:Collection U) (G:TypeOfDirectProduct U),
      G ∈ MappingSpace A B -> GraphOfMapping G A B.
  Proof.
    move => A B G H.
    inversion H.
    inversion H0 as [g].
    inversion H2.
    split.
    apply (direct_product_included_graph_of_function U g A B G).
    trivial.
    move => a HaA.
    exists (g a).
    split.
    rewrite H4.
    split.
    exists a.
    exists (g a).
    split;[reflexivity|split;[reflexivity|]].
    have L1: exists b:U, b = g a /\ b ∈ B.
    apply H3.
    trivial.
    inversion L1 as [b [Hbga HbB]].
    rewrite -Hbga.
    apply in_and_to_ordered_pair_in_direct_product.
    split;trivial.
    move => b' HG'.
    rewrite H4 in HG'.
    inversion HG'.
    inversion H5 as [a0 [b0 [Heq [Hb'ga Hab'AB]]]].
    apply ordered_pair_to_and in Heq.
    inversion Heq as [Heql Heqr].
    rewrite Heqr Heql.
    apply sym_eq.
    assumption.
  Qed.

    
End MappingSpace.
