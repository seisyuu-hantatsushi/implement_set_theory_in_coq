From mathcomp Require Import ssreflect.

Require Import collect_operator.
Require Import direct_product.
Require Import mapping.

Definition InvertibleMapping {U} (f:U->U) (X Y:Collection U) (F:TypeOfDirectProduct U) :=
  exists (g:U->U) (G:TypeOfDirectProduct U),
    MappingFunction g Y X /\
    G = GraphOfFunction g Y X /\
    G ⊙ F = GraphOfIdentity X /\
    F ⊙ G = GraphOfIdentity Y.

Section InverseMapping.
  Variable U:Type.

  Theorem graph_of_invertible_mapping_is_unique:
    forall (f g h:U -> U) (X Y:Collection U) (F G H:TypeOfDirectProduct U),
      F = GraphOfFunction f X Y ->
      G = GraphOfFunction g Y X ->
      H = GraphOfFunction h Y X ->
      G ⊙ F = GraphOfIdentity X ->
      F ⊙ H = GraphOfIdentity Y ->
      G = H.
  Proof.
    move => f g h X Y F G H HF HG HH HGF HFH.
    rewrite (compound_identity_function_r U g Y X G).
    rewrite -HFH.
    rewrite -(associativity_of_graph_of_function U h f g Y X Y X H F G).
    rewrite HGF.
    rewrite -(compound_identity_function_l U h Y X H).
    reflexivity.
    trivial.
    trivial.
    trivial.
    trivial.
    assumption.
  Qed.

  Theorem function_to_inverse_function:
    forall (f:U->U) (X Y:Collection U) (F:TypeOfDirectProduct U),
      F = GraphOfFunction f X Y -> forall (x y:U), <|x,y|> ∈ F -> <|y,x|> ∈ F ^-1.
  Proof.
    move => f X Y F HF x y.
    apply (correspondence_to_inverse_correspondence U (fun x y => y = f x) x y X Y).
    trivial.
  Qed.

  Theorem inverse_function_to_function:
    forall (f:U->U) (X Y:Collection U) (F:TypeOfDirectProduct U),
      F = GraphOfFunction f X Y -> forall (x y:U), <|y,x|> ∈ F ^-1 -> <|x,y|> ∈ F.
    move => f X Y F HF x y.
    apply (inverse_correspondence_to_correspondence U (fun x y => y = f x) x y X Y).
    trivial.
  Qed.

  Theorem function_iff_inverse_function:
    forall (f:U->U) (X Y:Collection U) (F:TypeOfDirectProduct U),
      F = GraphOfFunction f X Y -> forall (x y:U), <|x,y|> ∈ F <-> <|y,x|> ∈ F ^-1.
  Proof.
    move => f X Y F HF x y.
    rewrite /iff.
    split;[apply (correspondence_to_inverse_correspondence U (fun x y => y = f x) x y X Y)|
           apply (inverse_correspondence_to_correspondence U (fun x y => y = f x) x y X Y)];
    trivial.
  Qed.

  Theorem identity_pair_in_graph_of_compound_inverse_function_self:
    forall (f:U->U) (X Y:Collection U) (F:TypeOfDirectProduct U),
      MappingFunction f X Y ->
      F = GraphOfFunction f X Y ->
      forall x:U, x ∈ X -> <|x,x|> ∈ F^-1 ⊙ F.
  Proof.
    move => f X Y F Hf HF x HxX.
    split.
    exists x.
    exists x.
    split.
    reflexivity.
    exists (f x).
    rewrite HF.
    split.
    split.
    exists x.
    exists (f x).
    split.
    reflexivity.
    split;[reflexivity|
           apply ordered_pair_in_direct_product_iff_in_and;
           split;[trivial|
                  apply Hf in HxX;
                  inversion HxX as [y];
                  inversion H;
                  rewrite -H0;
                  assumption]].
    split.
    split.
    exists x.
    exists (f x).
    split;[reflexivity|
           split;[reflexivity|apply ordered_pair_in_direct_product_iff_in_and;[
                                split;
                                trivial;
                                apply Hf in HxX;
                                inversion HxX as [y];
                                inversion H;
                                rewrite H0 in H1;
                                assumption]]].
  Qed.

  Theorem compound_self_inverse_function_exists_identity:
    forall (f:U->U) (X Y:Collection U) (F:TypeOfDirectProduct U),
      X <> `Ø` ->
      MappingFunction f X Y ->
      F = GraphOfFunction f X Y ->
      exists y:U, y ∈ Y /\ <|y,y|> ∈ F ⊙ (F^-1).
  Proof.
    move => f X Y F HxX Hf HF.
    apply not_empty_collection_to_exists_element_in_collection in HxX.
    inversion HxX.
    have L1: exists y : U, y = f x /\ y ∈ Y.
    apply Hf.
    trivial.
    inversion L1 as [y].
    exists y.
    split.
    apply H0.
    have L2: <|x,y|> ∈ F.
    rewrite HF.
    split.
    exists x.
    exists y.
    split;[reflexivity|split].
    apply H0.
    apply ordered_pair_in_direct_product_iff_in_and.
    split;[trivial|apply H0].
    split.
    exists y.
    exists y.
    split;[reflexivity|exists x;split;[split;trivial|trivial]].
  Qed.

  Theorem invertible_function_iff_original_function:
    forall (f:U->U) (X Y:Collection U) (F:TypeOfDirectProduct U),
      MappingFunction f X Y ->
      F = GraphOfFunction f X Y ->
      InvertibleMapping f X Y F ->
      exists g:U->U, forall x y:U, x ∈ X /\ y ∈ Y -> (y = f x <-> x = g y).
  Proof.
    move => f X Y F Hf HF HIF.
    inversion HIF as [g [G [Hg [HG [HGF HFG]]]]].
    exists g.
    move => x y [HxX HyY].
    have L1: x = (g ◦ f) x.
    apply (singleton_image_to_mapping_compound_function U f g X Y X F G x x).
    trivial.
    trivial.
    trivial.
    trivial.
    trivial.
    rewrite HGF.
    apply image_singleton_domain_of_graph_of_identity_eq_singleton_domain.
    trivial.
    have L2: y = (f ◦ g) y.
    apply (singleton_image_to_mapping_compound_function U g f Y X Y G F y y).
    trivial.
    trivial.
    trivial.
    trivial.
    trivial.
    rewrite HFG.
    apply image_singleton_domain_of_graph_of_identity_eq_singleton_domain.
    trivial.
    rewrite /iff.
    split => H;rewrite H;[
               unfold CompoundFunction in L1;
               rewrite -L1;
               reflexivity|
               unfold CompoundFunction in L2;
               rewrite -L2;
               reflexivity].
  Qed.

  Theorem invertible_function_source_is_unique:
    forall (f:U->U) (X Y:Collection U) (F:TypeOfDirectProduct U),
      MappingFunction f X Y ->
      F = GraphOfFunction f X Y ->
      InvertibleMapping f X Y F ->
      forall x x' y:U, <|x,y|> ∈ F /\ <|x',y|> ∈ F -> x = x'.
  Proof.
    move => f X Y F Hf HF HIF x x' y.
    case => HFx HFx'.
    inversion HIF as [g [G [Hg [HG [HGF HFG]]]]].
    have Lx: x ∈ X.
    rewrite HF in HFx.
    inversion HFx as [Z [x0 [y0]]].
    inversion H.
    inversion H2.
    rewrite -H1 in H4.
    apply ordered_pair_in_direct_product_iff_in_and in H4.
    apply H4.
    have Lx': x' ∈ X.
    rewrite HF in HFx'.
    inversion HFx' as [Z [x0 [y0]]].
    inversion H.
    inversion H2.
    rewrite -H1 in H4.
    apply ordered_pair_in_direct_product_iff_in_and in H4.
    apply H4.
    have Ly: y ∈ Y.
    rewrite HF in HFx.
    inversion HFx as [Z [x0 [y0]]].
    inversion H.
    inversion H2.
    rewrite -H1 in H4.
    apply ordered_pair_in_direct_product_iff_in_and in H4.
    apply H4.
    have L1: x = (g ◦ f) x.
    apply (singleton_image_to_mapping_compound_function U f g X Y X F G x x).
    trivial.
    trivial.
    trivial.
    trivial.
    rewrite HF in HFx.
    inversion HFx as [Z0 [x0 [y0]]].
    inversion H as [H1 [H2 H3]].
    rewrite -H1 in H3.
    apply ordered_pair_in_direct_product_iff_in_and in H3.
    apply H3.
    rewrite HGF.
    apply image_singleton_domain_of_graph_of_identity_eq_singleton_domain.
    trivial.
    have L2: y = (f ◦ g) y.
    apply (singleton_image_to_mapping_compound_function U g f Y X Y G F y y).
    trivial.
    trivial.
    trivial.
    trivial.
    trivial.
    rewrite HFG.
    apply image_singleton_domain_of_graph_of_identity_eq_singleton_domain.
    trivial.
    have L3: x' = (g ◦ f) x'.
    apply (singleton_image_to_mapping_compound_function U f g X Y X F G x' x').
    trivial.
    trivial.
    trivial.
    trivial.
    rewrite HF in HFx'.
    inversion HFx' as [Z0 [x0 [y0]]].
    inversion H as [H1 [H2 H3]].
    rewrite -H1 in H3.
    apply ordered_pair_in_direct_product_iff_in_and in H3.
    apply H3.
    rewrite HGF.
    apply image_singleton_domain_of_graph_of_identity_eq_singleton_domain.
    trivial.
    have L4: y = f x.
    rewrite HF in HFx.
    inversion HFx as [Z0 [x0 [y0]]].
    inversion H.
    inversion H2.
    apply ordered_pair_to_and in H1.
    inversion H1.
    rewrite -H5 -H6 in H3.
    trivial.
    have L5: y = f x'.
    rewrite HF in HFx'.
    inversion HFx' as [Z0 [x0 [y0]]].
    inversion H.
    inversion H2.
    apply ordered_pair_to_and in H1.
    inversion H1.
    rewrite -H5 -H6 in H3.
    trivial.
    unfold CompoundFunction in L1.
    unfold CompoundFunction in L3.
    rewrite -L4 in L1.
    rewrite -L5 in L3.
    rewrite L1 L3.
    reflexivity.
  Qed.

End InverseMapping.

