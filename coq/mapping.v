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

Definition IdentityFunction U : U -> U := fun x:U => x.

Definition GraphOfIdentity {U:Type} (X:Collection U) : TypeOfDirectProduct U :=
  GraphOfFunction (IdentityFunction U) X X.

Definition CompoundFunction {U:Type} (g f: U -> U) : U -> U :=
  fun x:U => g ( f x ).

(* Unicode ◦ :25E6*)
Notation "g ◦ f" :=  (CompoundFunction g f) (right associativity, at level 33).

Axiom AxiomOfFuncionalExtensionality: forall (U:Type) (f g :U -> U),
    (forall x:U, f x = g x) -> f = g.

Section Mapping.
  Variable U:Type.

  Theorem function_determine_domain:
    forall {f:U -> U} (A B:Collection U) (G:TypeOfDirectProduct U),
      G = GraphOfFunction f A B -> 𝕯( G ) ⊂ A.
  Proof.
    move => f A B G HG.
    move: (relation_determine_domain U (fun (x y:U) => y = f x) A B G).
    apply.
    rewrite HG.
    reflexivity.
  Qed.

  Theorem function_determine_range:
    forall {f:U -> U} (A B:Collection U) (G:TypeOfDirectProduct U),
      G = GraphOfFunction f A B -> 𝕽( G ) ⊂ B.
  Proof.
    move => f A B G HG.
    move: (relation_determine_range U (fun (x y:U) => y = f x) A B G).
    apply.
    rewrite HG.
    reflexivity.
  Qed.

  Theorem direct_product_included_graph_of_function:
    forall (f:U -> U) (A B:Collection U) (G:TypeOfDirectProduct U),
      G = GraphOfFunction f A B -> G ⊂ A × B.
  Proof.
    move => A B G.
    apply graph_of_correspondence_is_subset_of_direct_product.
  Qed.

  Lemma rewrite_function_range:
    forall (f:U -> U) (A B:Collection U),
      (forall x:U, exists y:U, y = f x /\ <|x, y|> ∈ A × B) ->
      (forall x:U, exists y:U, x ∈ A /\ y = f x /\ y ∈ B).
  Proof.
    move => f A B H x.
    move: (H x) => Hx.
    inversion Hx as [y [Hf HAB]].
    exists y.
    apply ordered_pair_in_direct_product_to_in_and in HAB.
    inversion HAB as [HA HB].
    split;[trivial|split; trivial].
  Qed.

  Theorem function_satisfies_graph_of_mapping:
    forall (f:U -> U) (A B:Collection U) (G:TypeOfDirectProduct U),
      (forall x:U, exists y:U, y = f x /\ <|x, y|> ∈ A × B) ->
      G = GraphOfFunction f A B ->
      GraphOfMapping G A B.
  Proof.
    move => f A B G HF HG.
    split.
    +apply (direct_product_included_graph_of_function f). by [].
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
    forall (f:U -> U) (A B:Collection U) (G:TypeOfDirectProduct U),
      G = GraphOfFunction f A B -> 𝕴𝖒( G , `Ø` ) = `Ø`.
  Proof.
    move => f A B G HG.
    apply (image_of_domain_is_empty_is_empty U (fun x y:U => y = f x) A B).
    rewrite HG.
    reflexivity.
  Qed.

  Theorem condition_of_image_of_function_is_not_empty:
    forall (f:U -> U) (A B C:Collection U) (G:TypeOfDirectProduct U),
      MappingFunction f A B ->
      C <> `Ø` -> C ⊂ A ->
      G = GraphOfFunction f A B ->
      exists (y:U), y ∈ 𝕴𝖒( G , C ).
  Proof.
    move => f A B C G HF HNEC HCA HG.
    apply: (condition_of_image_of_binary_relation_is_not_empty U (fun x y:U => y = f x) A B).
    apply HF.
    apply HNEC.
    apply HCA.
    trivial.
  Qed.

  Theorem mapping_function_to_singleton_image:
    forall (f:U -> U) (X Y:Collection U) (F:TypeOfDirectProduct U) (x y:U),
      MappingFunction f X Y ->
      F = GraphOfFunction f X Y ->
      x ∈ X ->
      y = f x ->
      {|y|} = 𝕴𝖒( F , {|x|} ).
  Proof.
    move => f X Y F x y Hf HF HxX Hyfx.
    have L1: exists y:U, y = f x /\ y ∈ Y.
    apply Hf.
    trivial.
    apply mutally_included_to_eq.
    split.
    +move => y0 H.
     apply singleton_to_eq in H.
     split.
     exists x.
     split.
     apply eq_to_singleton.
     reflexivity.
     rewrite H.
     rewrite HF.
     split.
     inversion L1 as [y1].
     exists x.
     exists y.
     split.
     reflexivity.
     split.
     trivial.
     apply ordered_pair_in_direct_product_iff_in_and.
     split.
     trivial.
     inversion H0.
     rewrite H1 in H2.
     rewrite Hyfx.
     assumption.
    +move => y0 H.
     inversion H as [y1].
     inversion H0 as [x0].
     inversion H2.
     apply singleton_to_eq in H3.
     rewrite H3 in H4.
     rewrite HF in H4.
     inversion H4 as [Z' [x1 [y2]]].
     inversion H5.
     apply ordered_pair_to_and in H7.
     inversion H7.
     rewrite -H10 -H9 in H8.
     inversion H8.
     rewrite H11.
     apply eq_to_singleton.
     apply eq_sym.
     assumption.
  Qed.

  Theorem singleton_image_to_mapping_function:
    forall (f:U -> U) (X Y:Collection U) (F:TypeOfDirectProduct U) (x y:U),
      MappingFunction f X Y ->
      F = GraphOfFunction f X Y ->
      x ∈ X ->
      {|y|} = 𝕴𝖒( F , {|x|} ) ->
      y = f x.
  Proof.
    move => f X Y F x y Hf HF HxX H.
    have L1: exists y:U, y = f x /\ y ∈ Y.
    apply Hf.
    trivial.
    apply mutally_included_iff_eq in H.
    inversion H.
    inversion L1 as [y0].
    inversion H2.
    rewrite -H3.
    apply eq_sym.
    apply singleton_to_eq.
    apply: (H1 y0).
    split.
    exists x.
    split.
    apply singleton_iff_eq.
    reflexivity.
    rewrite HF.
    split.
    exists x.
    exists y0.
    split.
    reflexivity.
    split.
    trivial.
    apply ordered_pair_in_direct_product_iff_in_and.
    split; assumption.
  Qed.

  Theorem mapping_function_iff_singleton_image:
    forall (f:U -> U) (X Y:Collection U) (F:TypeOfDirectProduct U) (x y:U),
      MappingFunction f X Y ->
      F = GraphOfFunction f X Y ->
      x ∈ X ->
      y = f x <->
      {|y|} = 𝕴𝖒( F , {|x|} ).
  Proof.
    move => f X Y F x y Hf HF HxX.
    rewrite /iff; split;
      [apply: (mapping_function_to_singleton_image f X Y)|
       apply: (singleton_image_to_mapping_function f X Y)];
      trivial;
      trivial;
      assumption.
  Qed.

  Theorem singleton_domain_image_eq_to_function_eq:
    forall (f g:U -> U) (X Y:Collection U) (F G:TypeOfDirectProduct U) (x:U),
      MappingFunction f X Y ->
      MappingFunction g X Y ->
      F = GraphOfFunction f X Y ->
      G = GraphOfFunction g X Y ->
      x ∈ X ->
      𝕴𝖒( F , {|x|} ) = 𝕴𝖒( G , {|x|} ) ->
      f x = g x.
  Proof.
    move => f g X Y F G x Hf Hg HF HG HxX HI.
    have L1: exists y:U, y = f x /\ y ∈ Y.
    apply Hf.
    trivial.
    have L2: exists y:U, y = g x /\ y ∈ Y.
    apply Hg.
    trivial.
    inversion L1 as [y0].
    inversion L2 as [y1].
    inversion H.
    inversion H0.
    apply eq_sym.
    rewrite -H3.
    apply: (singleton_image_to_mapping_function f X Y F x y1).
    trivial.
    trivial.
    trivial.
    rewrite HI.
    apply: (mapping_function_to_singleton_image g X Y G x y1).
    trivial.
    trivial.
    trivial.
    assumption.
  Qed.

  Theorem function_eq_to_singleton_domain_image_eq:
    forall (f g:U -> U) (X Y:Collection U) (F G:TypeOfDirectProduct U) (x:U),
      MappingFunction f X Y ->
      MappingFunction g X Y ->
      F = GraphOfFunction f X Y ->
      G = GraphOfFunction g X Y ->
      x ∈ X ->
      f x = g x ->
      𝕴𝖒( F , {|x|} ) = 𝕴𝖒( G , {|x|} ).
  Proof.
    move => f g X Y F G x Hf Hg HF HG HxX Heq.
    apply mutally_included_to_eq.
    split => y H;
               inversion H as [y0 [x0]];
               inversion H0;
               apply singleton_to_eq in H2;
               rewrite H2 in H3;[rewrite HF in H3|
                                 rewrite HG in H3];
               split;
               exists x; split.
    +apply singleton_iff_eq;reflexivity.
     rewrite HG.
     inversion H3.
     inversion H4 as [x1 [y1]].
     inversion H6.
     apply ordered_pair_to_and in H7.
     inversion H7.
     rewrite -H9 -H10 in H8.
     split.
     exists x.
     exists y.
     split;[reflexivity|rewrite Heq in H8;assumption].
    +apply singleton_iff_eq;reflexivity.
     rewrite HF.
     inversion H3.
     inversion H4 as [x1 [y1]].
     inversion H6.
     apply ordered_pair_to_and in H7.
     inversion H7.
     rewrite -H9 -H10 in H8.
     split.
     exists x.
     exists y.
     split;[reflexivity|rewrite -Heq in H8;assumption].
  Qed.

  Theorem singleton_domain_image_eq_iff_function_eq:
    forall (f g:U -> U) (X Y:Collection U) (F G:TypeOfDirectProduct U) (x:U),
      MappingFunction f X Y ->
      MappingFunction g X Y ->
      F = GraphOfFunction f X Y ->
      G = GraphOfFunction g X Y ->
      x ∈ X ->
      𝕴𝖒( F , {|x|} ) = 𝕴𝖒( G , {|x|} ) <->
      f x = g x.
  Proof.
    move => f g X Y F G x Hf Hg HF HG HxX.
    rewrite /iff.
    split;[apply (singleton_domain_image_eq_to_function_eq f g X Y)|
           apply (function_eq_to_singleton_domain_image_eq f g X Y)];
    trivial;
    trivial;
    trivial;
    trivial.
  Qed.

  Theorem graph_of_function_eq_to_function_eq:
    forall (f g:U -> U) (X Y:Collection U) (F G:TypeOfDirectProduct U),
      MappingFunction f X Y ->
      MappingFunction g X Y ->
      F = GraphOfFunction f X Y ->
      G = GraphOfFunction g X Y ->
      F = G -> (forall x:U, x ∈ X -> f x = g x).
  Proof.
    move => f g X Y F G Hf Hg HF HG Heq x HxX.
    apply (singleton_domain_image_eq_to_function_eq f g X Y F G).
    trivial.
    trivial.
    trivial.
    trivial.
    trivial.
    rewrite Heq.
    reflexivity.
  Qed.

  Theorem function_eq_to_graph_of_function_eq:
    forall (f g:U -> U) (X Y:Collection U) (F G:TypeOfDirectProduct U),
      MappingFunction f X Y ->
      MappingFunction g X Y ->
      F = GraphOfFunction f X Y ->
      G = GraphOfFunction g X Y ->
      (forall x:U, x ∈ X -> f x = g x) ->
      F = G.
  Proof.
    move => f g X Y F G Hf Hg HF HG Heq.
    rewrite HF HG.
    apply mutally_included_to_eq.
    split => Z' H; inversion H as [Z0' [x0 [y0]]];
               [inversion H0 as [HZ0' [Hy0fx0 HX0Y0]]|
                inversion H0 as [HZ0' [Hy0gx0 HX0Y0]]];
               apply ordered_pair_in_direct_product_iff_in_and in HX0Y0;
               inversion HX0Y0;
               split;
               exists x0;
               exists y0;
               move: (Heq x0) => Heqx0;
                                   apply Heqx0 in H2;
                                   [rewrite -H2|rewrite H2];trivial.
  Qed.

  Theorem graph_of_function_eq_iff_function_eq:
    forall (f g:U -> U) (X Y:Collection U) (F G:TypeOfDirectProduct U),
      MappingFunction f X Y ->
      MappingFunction g X Y ->
      F = GraphOfFunction f X Y ->
      G = GraphOfFunction g X Y ->
      F = G <-> (forall x:U, x ∈ X -> f x = g x).
  Proof.
    move => f g X Y F G Hf Hg HF HG.
    rewrite /iff.
    split;[apply (graph_of_function_eq_to_function_eq f g X Y F G)|
           apply (function_eq_to_graph_of_function_eq f g X Y F G)];
    trivial.
  Qed.

  Theorem singleton_image_to_ordered_pair_in_graph:
    forall (f:U -> U) (X Y:Collection U) (F:TypeOfDirectProduct U) (x y:U),
      MappingFunction f X Y ->
      F = GraphOfFunction f X Y ->
      x ∈ X ->
      {| y |} = 𝕴𝖒( F , {| x |} ) ->
      <|x,y|> ∈ F.
  Proof.
    move => f X Y F x y Hf HF HxX HI.
    have L1: exists y:U, y = f x /\ y ∈ Y.
    apply Hf.
    trivial.
    inversion L1 as [y0 [Hy0fx HY]].
    apply (singleton_image_to_mapping_function f X Y F) in HI.
    rewrite HF.
    split.
    exists x.
    exists y0.
    rewrite -HI in Hy0fx.
    rewrite Hy0fx.
    rewrite Hy0fx in HY.
    split;[reflexivity|split;[trivial|
                              apply ordered_pair_in_direct_product_iff_in_and;
                              split;
                              trivial]].
    trivial.
    trivial.
    trivial.
  Qed.

  Theorem ordered_pair_in_graph_to_singleton_image:
    forall (f:U -> U) (X Y:Collection U) (F:TypeOfDirectProduct U) (x y:U),
      MappingFunction f X Y ->
      F = GraphOfFunction f X Y ->
      x ∈ X ->
      <|x,y|> ∈ F ->
      {| y |} = 𝕴𝖒( F , {| x |} ).
  Proof.
    move => f X Y F x y Hf HF HxX HoF.
    have L1: exists y:U, y = f x /\ y ∈ Y.
    apply Hf.
    trivial.
    inversion L1 as [y0 [Hy0fx HY]].
    apply (mapping_function_to_singleton_image f X Y F).
    trivial.
    trivial.
    trivial.
    rewrite HF in HoF.
    inversion HoF.
    inversion H as [x1 [y1]].
    inversion H1.
    apply ordered_pair_to_and in H2.
    inversion H2.
    rewrite -H4 -H5 in H3.
    apply H3.
  Qed.

  Theorem singleton_image_iff_ordered_pair_in_graph:
    forall (f:U -> U) (X Y:Collection U) (F:TypeOfDirectProduct U) (x y:U),
      MappingFunction f X Y ->
      F = GraphOfFunction f X Y ->
      x ∈ X ->
      {| y |} = 𝕴𝖒( F , {| x |} ) <->
      <|x, y|> ∈ F.
  Proof.
    move => f X Y F x y Hf HF HxX.
    rewrite /iff; split;
      [apply (singleton_image_to_ordered_pair_in_graph f X Y F)|
       apply (ordered_pair_in_graph_to_singleton_image f X Y F)];
      trivial;
      trivial;
      assumption.
  Qed.

  Theorem singleton_image_is_unique:
    forall (f:U -> U) (X Y:Collection U) (F:TypeOfDirectProduct U) (x y y':U),
      MappingFunction f X Y ->
      F = GraphOfFunction f X Y ->
      x ∈ X ->
      {|y|} = 𝕴𝖒( F , {|x|} ) /\ {|y'|} = 𝕴𝖒( F , {|x|} ) ->
      y = y'.
  Proof.
    move => f X Y F x y y' Hf HF HxX [Hy Hy'].
    apply (singleton_image_to_mapping_function f X Y) in Hy.
    apply (singleton_image_to_mapping_function f X Y) in Hy'.
    rewrite Hy Hy'.
    reflexivity.
    trivial.
    trivial.
    trivial.
    trivial.
    trivial.
    assumption.
  Qed.

  Theorem cup_domain_is_cup_image_in_function:
    forall (f:U -> U) (A B C D:Collection U) (G:TypeOfDirectProduct U),
      G = GraphOfFunction f A B ->
      𝕴𝖒( G , C ∪ D ) = 𝕴𝖒( G , C ) ∪ 𝕴𝖒( G , D ).
  Proof.
    move => f A B C D G HG.
    apply (cup_domain_is_cup_image U (fun x y:U => y = f x) A B).
    apply HG.
  Qed.

  Theorem image_of_correspondence_function_include_chain_image:
    forall (f g:U -> U) (X Y Z:Collection U) (F G GF:TypeOfDirectProduct U),
      F = GraphOfFunction f X Y ->
      G = GraphOfFunction g Y Z ->
      GF = GraphOfCompoundCorrespondence G F ->
      𝕴𝖒( G ,  𝕴𝖒( F, X ) ) ⊂ 𝕴𝖒( GF, X ).
  Proof.
    move => f g X Y Z F G GF HF HG HGF z.
    apply: (image_of_correspondence_include_chain_image
              U (fun x y => y = f x) (fun y z => z = g y) X Y Z F G GF).
    trivial.
    trivial.
    trivial.
  Qed.

  Theorem chain_image_include_image_of_correspondence_function:
    forall (f g:U -> U) (X Y Z:Collection U) (F G GF:TypeOfDirectProduct U),
      F = GraphOfFunction f X Y ->
      G = GraphOfFunction g Y Z ->
      GF = GraphOfCompoundCorrespondence G F ->
      𝕴𝖒( GF, X ) ⊂ 𝕴𝖒( G, 𝕴𝖒( F , X )).
  Proof.
    move => f g X Y Z F G GF HF HG HGF z.
    apply: (chain_image_include_image_of_correspondence
              U (fun x y => y = f x) (fun y z => z = g y) X Y Z F G GF).
    trivial.
    trivial.
    trivial.
  Qed.

  Theorem chain_image_is_image_of_correspondence_function:
    forall (f g:U -> U) (X Y Z:Collection U) (F G GF:TypeOfDirectProduct U),
      F = GraphOfFunction f X Y ->
      G = GraphOfFunction g Y Z ->
      GF = GraphOfCompoundCorrespondence G F ->
      𝕴𝖒( G, 𝕴𝖒( F , X )) = 𝕴𝖒( GF, X ).
  Proof.
    move => f g X Y Z F G GF HF HG HGF.
    apply (chain_image_is_image_of_correspondence U (fun x y => y = f x) (fun y z => z = g y) X Y Z F G GF).
    trivial.
    trivial.
    trivial.
  Qed.

  Theorem compound_graph_of_function_include_graph_of_compound_function:
    forall (f g:U -> U) (X Y Z:Collection U) (F G GF:TypeOfDirectProduct U),
      MappingFunction f X Y ->
      F = GraphOfFunction f X Y ->
      G = GraphOfFunction g Y Z ->
      GF = GraphOfFunction (CompoundFunction g f) X Z ->
      GF ⊂ G ⊙ F.
  Proof.
    move => f g X Y Z F G GF Hf HF HG HGF Z' H.
    rewrite HGF in H.
    inversion H as [Z0'].
    inversion H0 as [x [z]].
    inversion H2.
    inversion H4.
    split.
    exists x.
    exists z.
    split;[trivial|].
    apply ordered_pair_in_direct_product_iff_in_and in H6.
    inversion H6.
    apply Hf in H7.
    inversion H7 as [y].
    inversion H9.
    exists y.
    split;[rewrite HF|rewrite HG];split.
    exists x.
    exists y.
    split;[reflexivity|split;
                       [trivial|
                        apply ordered_pair_in_direct_product_iff_in_and;
                        split;[apply H6|trivial]]].
    exists y.
    exists z.
    split;[reflexivity|split;
                       [rewrite H10;trivial|
                        apply ordered_pair_in_direct_product_iff_in_and;
                        split;trivial]].
  Qed.

  Theorem graph_of_compound_function_include_compound_graph_of_function:
    forall (f g:U -> U) (X Y Z:Collection U) (F G GF:TypeOfDirectProduct U),
      F = GraphOfFunction f X Y ->
      G = GraphOfFunction g Y Z ->
      GF = GraphOfFunction (CompoundFunction g f) X Z ->
      G ⊙ F ⊂ GF.
  Proof.
    move => f g X Y Z F G GF HF HG HGF Z' H.
    inversion H as [Z0'].
    inversion H0 as [x [z]].
    inversion H2.
    inversion H4 as [y].
    inversion H5.
    rewrite H3.
    rewrite HGF.
    split.
    exists x.
    exists z.
    split;[reflexivity|].
    rewrite HF in H6.
    rewrite HG in H7.
    inversion H6 as [Y' [x0 [y0]]].
    inversion H8.
    inversion H11.
    inversion H7.
    inversion H7 as [Z1' [y1 [z1]]].
    inversion H16.
    inversion H19.
    apply ordered_pair_to_and in H10.
    inversion H10.
    rewrite -H22 -H23 in H12.
    apply ordered_pair_to_and in H18.
    inversion H18.
    rewrite -H24 -H25 in H20.
    rewrite H12 in H20.
    split.
    trivial.
    rewrite -H22 -H23 in H13.
    rewrite -H24 -H25 in H21.
    apply ordered_pair_in_direct_product_iff_in_and in H13.
    apply ordered_pair_in_direct_product_iff_in_and in H21.
    apply ordered_pair_in_direct_product_iff_in_and.
    split;[apply H13|apply H21].
  Qed.

  Theorem compound_graph_of_function_eq_graph_of_compound_function:
    forall (f g:U -> U) (X Y Z:Collection U) (F G GF:TypeOfDirectProduct U),
      MappingFunction f X Y ->
      F = GraphOfFunction f X Y ->
      G = GraphOfFunction g Y Z ->
      GF = GraphOfFunction (CompoundFunction g f) X Z ->
      GF = G ⊙ F.
  Proof.
    move => f g X Y Z F G GF Hf HF HG HGF.
    apply mutally_included_iff_eq.
    split;[apply (compound_graph_of_function_include_graph_of_compound_function f g X Y Z F G GF)|
           apply (graph_of_compound_function_include_compound_graph_of_function f g X Y Z F G GF)];
    trivial.
  Qed.

  Theorem compound_function_to_in_image_of_graph_function:
    forall (f g:U -> U) (X Y Z:Collection U) (F G GF:TypeOfDirectProduct U) (x z:U),
      MappingFunction f X Y ->
      MappingFunction g Y Z ->
      F = GraphOfFunction f X Y ->
      G = GraphOfFunction g Y Z ->
      GF = GraphOfFunction (CompoundFunction g f) X Z ->
      x ∈ X ->
      z = (CompoundFunction g f) x -> z ∈ 𝕴𝖒(GF, {|x|}).
  Proof.
    move => f g X Y Z F G GF x z Hf Hg HF HG HGF HxX H.
    split.
    exists x.
    split.
    apply singleton_iff_eq.
    reflexivity.
    rewrite HGF.
    split.
    exists x.
    exists z.
    split.
    reflexivity.
    split.
    trivial.
    apply ordered_pair_in_direct_product_iff_in_and.
    split;[trivial|].
    apply Hf in HxX.
    inversion HxX as [y Hfx].
    unfold MappingFunction in Hg.
    inversion Hfx as [Hyfx HyY].
    apply Hg in HyY.
    inversion HyY as [z0].
    rewrite Hyfx in H0.
    inversion H0.
    unfold CompoundFunction in H.
    rewrite -H in H1.
    rewrite -H1.
    trivial.
  Qed.

  Theorem in_image_of_graph_function_to_compound_function:
    forall (f g:U -> U) (X Y Z:Collection U) (F G GF:TypeOfDirectProduct U) (x z:U),
      F = GraphOfFunction f X Y ->
      G = GraphOfFunction g Y Z ->
      GF = GraphOfFunction (CompoundFunction g f) X Z ->
      x ∈ X ->
      z ∈ (𝕴𝖒(GF, {|x|})) -> z = (CompoundFunction g f) x.
  Proof.
    move => f g X Y Z F G GF x z HF HG HGF HxX H.
    inversion H as [z0].
    inversion H0 as [x0].
    inversion H2.
    rewrite HGF in H4.
    apply singleton_to_eq in H3.
    rewrite H3 in H4.
    inversion H4.
    inversion H5 as [x1 [z1]].
    inversion H7.
    apply ordered_pair_to_and in H8.
    inversion H8.
    inversion H9.
    rewrite H10 H11.
    trivial.
  Qed.

  Theorem compound_function_iff_in_image_of_graph_function:
    forall (f g:U -> U) (X Y Z:Collection U) (F G GF:TypeOfDirectProduct U) (x z:U),
      MappingFunction f X Y ->
      MappingFunction g Y Z ->
      F = GraphOfFunction f X Y ->
      G = GraphOfFunction g Y Z ->
      GF = GraphOfFunction (CompoundFunction g f) X Z ->
      x ∈ X ->
      z = (g ◦ f) x <-> z ∈ 𝕴𝖒(GF, {|x|}).
  Proof.
    move => f g X Y Z F G GF x z Hf Hg HF HG HGF HxX.
    rewrite /iff.
    split;[apply (compound_function_to_in_image_of_graph_function f g X Y Z F G GF)|
           apply (in_image_of_graph_function_to_compound_function f g X Y Z F G GF)];
    trivial.
  Qed.

  Theorem mapping_compound_function_to_singleton_image:
    forall (f g:U -> U) (X Y Z:Collection U) (F G:TypeOfDirectProduct U) (x z:U),
      MappingFunction f X Y ->
      MappingFunction g Y Z ->
      F = GraphOfFunction f X Y ->
      G = GraphOfFunction g Y Z ->
      x ∈ X ->
      z = (g ◦ f) x ->
      {|z|} = 𝕴𝖒( G ⊙ F , {|x|} ).
  Proof.
    move => f g X Y Z F G x z Hf Hg HF HG HxX Hgf.
    rewrite -(compound_graph_of_function_eq_graph_of_compound_function f g X Y Z F G (GraphOfFunction (g ◦ f) X Z)).
    apply (mapping_function_iff_singleton_image (g ◦ f) X Z (GraphOfFunction (g ◦ f) X Z) x z).
    move => x' Hx'X.
    apply Hf in Hx'X.
    inversion Hx'X as [y'].
    inversion H.
    apply Hg in H1.
    inversion H1 as [z'].
    inversion H2.
    exists z'.
    split.
    rewrite H0 in H3.
    trivial.
    trivial.
    reflexivity.
    trivial.
    trivial.
    trivial.
    trivial.
    trivial.
    reflexivity.
  Qed.

  Theorem singleton_image_to_mapping_compound_function:
    forall (f g:U -> U) (X Y Z:Collection U) (F G:TypeOfDirectProduct U) (x z:U),
      MappingFunction f X Y ->
      MappingFunction g Y Z ->
      F = GraphOfFunction f X Y ->
      G = GraphOfFunction g Y Z ->
      x ∈ X ->
      {|z|} = 𝕴𝖒( G ⊙ F , {|x|} ) ->
      z = (g ◦ f) x.
  Proof.
    move => f g X Y Z F G x z Hf Hg HF HG HxX HI.
    apply (singleton_image_to_mapping_function (g ◦ f) X Z (GraphOfFunction (g ◦ f) X Z) x z).
    move => x' Hx'X.
    apply Hf in Hx'X.
    inversion Hx'X as [y'].
    inversion H.
    apply Hg in H1.
    inversion H1 as [z'].
    inversion H2.
    exists z'.
    rewrite H0 in H3.
    split.
    trivial.
    trivial.
    reflexivity.
    trivial.
    rewrite (compound_graph_of_function_eq_graph_of_compound_function f g X Y Z F G (GraphOfFunction (g ◦ f) X Z)).
    trivial.
    trivial.
    trivial.
    trivial.
    reflexivity.
  Qed.

  Theorem mapping_compound_function_iff_singleton_image:
    forall (f g:U -> U) (X Y Z:Collection U) (F G:TypeOfDirectProduct U) (x z:U),
      MappingFunction f X Y ->
      MappingFunction g Y Z ->
      F = GraphOfFunction f X Y ->
      G = GraphOfFunction g Y Z ->
      x ∈ X ->
      z = (g ◦ f) x <->
      {|z|} = 𝕴𝖒( G ⊙ F , {|x|} ).
  Proof.
    move => f g X Y Z F G x z Hf Hg HF HG HxX.
    rewrite /iff.
    split;
      [apply (mapping_compound_function_to_singleton_image f g X Y Z F G x z)|
       apply (singleton_image_to_mapping_compound_function f g X Y Z F G x z)];
    trivial.
  Qed.

  Theorem compound_function_value_exists_unique:
    forall (f g:U -> U) (X Y Z:Collection U) (F G:TypeOfDirectProduct U),
      MappingFunction f X Y ->
      MappingFunction g Y Z ->
      F = GraphOfFunction f X Y ->
      G = GraphOfFunction g Y Z ->
      forall x:U, x ∈ X ->
                  exists z:U, {|z|} = 𝕴𝖒( G ⊙ F , {|x|} ) ->
                              forall z':U, {|z'|} = 𝕴𝖒( G ⊙ F , {|x|} ) -> z = z'.
  Proof.
    move => f g X Y Z F G Hf Hg HF HG x HxX.
    move Hfgz: (g (f x)) => z.
    exists z.
    move => H z' H0.
    apply (mapping_compound_function_iff_singleton_image f g X Y Z F G x z') in H0.
    rewrite H0 -Hfgz.
    reflexivity.
    trivial.
    trivial.
    trivial.
    trivial.
    trivial.
  Qed.

  Theorem compound_function_value_unique:
    forall (f g:U -> U) (X Y Z:Collection U) (F G:TypeOfDirectProduct U),
      F = GraphOfFunction f X Y ->
      G = GraphOfFunction g Y Z ->
      forall x z z':U, x ∈ X ->
                       {|z|} = 𝕴𝖒( G ⊙ F , {|x|} ) ->
                       {|z'|} = 𝕴𝖒( G ⊙ F , {|x|} ) -> z = z'.
  Proof.
    move => f g X Y Z F G HF HG x z z' HxX HIz HIz'.
    apply singleton_eq_iff_element_eq.
    rewrite HIz HIz'.
    reflexivity.
  Qed.

  Theorem image_singleton_domain_of_graph_of_identity_eq_singleton_domain:
    forall (X:Collection U) (x:U),
      x ∈ X -> {|x|} = 𝕴𝖒( GraphOfIdentity X , {|x|} ).
  Proof.
    move => X x HxX.
    apply mutally_included_to_eq.
    split; move => x0 H.
    apply singleton_to_eq in H.
    split.
    exists x0.
    split;[apply singleton_iff_eq;trivial|
           split;
           exists x0;
           exists x0;
           split;[reflexivity|
                  split]].
    trivial.
    rewrite H.
    apply ordered_pair_in_direct_product_iff_in_and.
    split; trivial.
    inversion H as [x'].
    inversion H0 as [x0'].
    inversion H2.
    inversion H4.
    inversion H5 as [x1 [x2]].
    inversion H7.
    inversion H9.
    rewrite H10 in H8.
    apply ordered_pair_to_and in H8.
    inversion H8.
    rewrite -H12 in H13.
    rewrite H13.
    assumption.
  Qed.

  Theorem ordered_pair_in_graph_of_identity:
    forall (X:Collection U) (x:U),
      x ∈ X -> <|x,x|> ∈ GraphOfIdentity X.
  Proof.
    move => X x HxX.
    split.
    exists x.
    exists x.
    split;[reflexivity|split;
                       [reflexivity|
                        apply ordered_pair_in_direct_product_iff_in_and;
                        split;
                        assumption]].
  Qed.

  Theorem ordered_pair_in_graph_to_eq:
    forall (X:Collection U) (x x':U),
      <|x,x'|> ∈ GraphOfIdentity X -> x = x'.
  Proof.
    move => X x x' H.
    inversion H as [Z [x0 [x0']]].
    inversion H0 as [H2 [H3]].
    apply ordered_pair_to_and in H2.
    inversion H2.
    rewrite -H5 -H6 in H3.
    rewrite H3.
    reflexivity.
  Qed.

  Theorem same_element_pair_in_identity:
    forall (X:Collection U) (x x':U),
      x ∈ X /\ x = x' -> <|x,x'|> ∈ GraphOfIdentity X.
  Proof.
    move => X x x'.
    case => HxX Heq.
    rewrite -Heq.
    apply ordered_pair_in_graph_of_identity.
    assumption.
  Qed.

  Theorem ordered_pair_in_graph_iff_eq:
    forall (X:Collection U) (x x':U),
      x ∈ X /\ x = x' <-> <|x,x'|> ∈ GraphOfIdentity X.
  Proof.
    move => X x x'.
    rewrite /iff.
    split.
    +case => HxX Heq.
     rewrite -Heq.
     apply ordered_pair_in_graph_of_identity.
     assumption.
    +move => H.
     inversion H.
     inversion H0 as [x0 [x'0]].
     inversion H2.
     inversion H4.
     rewrite -H3 in H6.
     apply ordered_pair_in_direct_product_iff_in_and in H6.
     inversion H6.
     apply ordered_pair_to_and in H3.
     inversion H3.
     rewrite -H9 -H10 in H5.
     split;[trivial|apply eq_sym;assumption].
  Qed.

  Theorem compound_identity_function_r:
    forall (f:U -> U) (X Y:Collection U) (F:TypeOfDirectProduct U),
      F = GraphOfFunction f X Y ->
      F = F ⊙ GraphOfIdentity X.
  Proof.
    move => f' X Y F HF.
    rewrite HF.
    apply mutally_included_to_eq.
    split => Z HFZ;
               inversion HFZ as [Z0 [x0 [y0]]];
               inversion H.
    inversion H2.
    split.
    exists x0.
    exists y0.
    split;[trivial|].
    exists x0.
    split.
    apply ordered_pair_in_graph_of_identity.
    apply ordered_pair_in_direct_product_to_in_and in H4.
    apply H4.
    split.
    exists x0.
    exists y0.
    split;[reflexivity|trivial].
    inversion H2 as [x0'].
    inversion H3.
    apply ordered_pair_in_graph_to_eq in H4.
    rewrite -H4 in H5.
    rewrite H1.
    assumption.
  Qed.

  Theorem compound_identity_function_l:
    forall (f:U -> U) (X Y:Collection U) (F:TypeOfDirectProduct U),
      F = GraphOfFunction f X Y ->
      F = GraphOfIdentity Y ⊙ F.
  Proof.
    move => f' X Y F HF.
    rewrite HF.
    apply mutally_included_to_eq.
    split => Z H;
               inversion H;
               inversion H0 as [x [y]].
    +inversion H2 as [H3 [H4 H5]].
     split.
     exists x.
     exists y.
     split;[trivial|exists y;
                    rewrite -H3;
                    split;[trivial|
                           apply ordered_pair_in_graph_of_identity;
                           apply ordered_pair_in_direct_product_iff_in_and in H5;
                           apply H5]].
    +inversion H2 as [H3 H4].
     inversion H4 as [y' [H5 H6]].
     apply ordered_pair_in_graph_to_eq in H6.
     rewrite H6 in H5.
     rewrite H3.
     assumption.
  Qed.

  Theorem associativity_of_graph_of_function:
    forall (f g h:U -> U) (X Y Z W:Collection U) (F G H:TypeOfDirectProduct U),
      F = GraphOfFunction f X Y ->
      G = GraphOfFunction g Y Z ->
      H = GraphOfFunction h Z W ->
      (H ⊙ G) ⊙ F = H ⊙ (G ⊙ F).
  Proof.
    move => f' g' h' X Y Z W F G H HF HG HH.
    apply (associativity_of_graph_of_binary_relation U
                                                     (fun x y => y = f' x)
                                                     (fun x y => y = g' x)
                                                     (fun x y => y = h' x)
                                                     X Y Z W F G H).
    trivial.
    trivial.
    trivial.
  Qed.

End Mapping.

Require Export binary_relation.
