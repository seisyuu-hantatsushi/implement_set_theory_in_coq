From mathcomp Require Import ssreflect.
Require Import collect_operator.
Require Import direct_product.
Require Import mapping.
Require Import inverse_mapping.

Definition InjectionGraph {U:Type} (F:TypeOfDirectProduct U) :=
  forall (x x' y:U), <|x,y|> ∈ F /\ <|x',y|> ∈ F -> x = x'.

Definition SurjectionGraph {U:Type} (F:TypeOfDirectProduct U) (R:Collection U) :=
  forall (y:U), y ∈ R -> exists x:U, <|x,y|> ∈ F.

Definition BijectionGraph {U:Type} (F:TypeOfDirectProduct U) (R:Collection U) :=
  InjectionGraph F /\ SurjectionGraph F R.

Section MappingMorphism.
  Variable U:Type.

  Theorem not_injection_graph:
    forall (f:U -> U) (X Y:Collection U) (F:TypeOfDirectProduct U),
      MappingFunction f X Y ->
      F = GraphOfFunction f X Y ->
      ~ InjectionGraph F -> exists x x' y:U, x <> x' /\ <|x,y|> ∈ F /\ <|x',y|> ∈ F.
  Proof.
    move => f X Y F Hf HF HNIF.
    unfold InjectionGraph in HNIF.
    apply (DeMorganNotForall_Triple_Open) in HNIF.
    case HNIF => [x [x' [y H]]].
    apply not_imply_to_and in H.
    apply and_comm in H.
    exists x.
    exists x'.
    exists y.
    trivial.
  Qed.

  Theorem compound_injection_graph_is_injection_graph:
    forall (f g:U -> U) (X Y Z:Collection U) (F G:TypeOfDirectProduct U),
      MappingFunction f X Y ->
      F = GraphOfFunction f X Y ->
      InjectionGraph F ->
      MappingFunction g Y Z ->
      G = GraphOfFunction g Y Z ->
      InjectionGraph G ->
      InjectionGraph (G ⊙ F).
  Proof.
    move => f g X Y Z F G Hf HF HFI Hg HG HGI.
    move => x x' z [H0 H1].
    inversion H0 as [Z0 [x0 [z0 [HZ0 HC0]]]].
    inversion HC0 as [y0 [HF0 HG0]].
    inversion H1 as [Z1 [x1 [z1 [HZ1 HC1]]]].
    inversion HC1 as [y1 [HF1 HG1]].
    apply ordered_pair_to_and in HZ0.
    inversion HZ0 as [HZ00 HZ01].
    apply ordered_pair_to_and in HZ1.
    inversion HZ1 as [HZ10 HZ11].
    rewrite -HZ00 in HF0.
    rewrite -HZ10 in HF1.
    rewrite -HZ01 in HG0.
    rewrite -HZ11 in HG1.
    suff: y0 = y1.
    move => H'.
    rewrite -H' in HF1.
    apply (HFI x x' y0).
    split; trivial.
    apply (HGI y0 y1 z).
    split; trivial.
  Qed.

  Theorem compound_surjection_graph_is_surjection_graph:
    forall (f g:U -> U) (X Y Z:Collection U) (F G:TypeOfDirectProduct U),
      MappingFunction f X Y ->
      F = GraphOfFunction f X Y ->
      SurjectionGraph F Y ->
      MappingFunction g Y Z ->
      G = GraphOfFunction g Y Z ->
      SurjectionGraph G Z ->
      SurjectionGraph (G ⊙ F) Z.
  Proof.
    move => f g X Y Z F G Hf HF HFS Hg HG HGS z HzZ.
    apply HGS in HzZ.
    inversion HzZ as [y HZG].
    rewrite HG in HZG.
    inversion HZG as [YZ' [y0 [z0 [HYZ [Hzgy]]]]].
    apply ordered_pair_in_direct_product_iff_in_and in H.
    inversion H.
    apply HFS in H1.
    inversion H1 as [x].
    exists x.
    split.
    exists x.
    exists z.
    split.
    reflexivity.
    exists y0.
    split.
    trivial.
    rewrite H0 in HYZ.
    apply ordered_pair_to_and in HYZ.
    inversion HYZ.
    rewrite H5.
    rewrite HG.
    split.
    exists y0.
    exists z0.
    split.
    reflexivity.
    split.
    trivial.
    apply ordered_pair_in_direct_product_iff_in_and.
    assumption.
  Qed.

  Theorem compound_graph_is_injection_to_source_graph_is_injection:
    forall (f g:U -> U) (X Y Z:Collection U) (F G:TypeOfDirectProduct U),
      MappingFunction f X Y ->
      F = GraphOfFunction f X Y ->
      MappingFunction g Y Z ->
      G = GraphOfFunction g Y Z ->
      InjectionGraph (G ⊙ F) ->
      InjectionGraph F.
  Proof.
    move => f g X Y Z F G Hf HF Hg HG HGFI x x' y [HF0 HF1].
    unfold InjectionGraph in HGFI.
    have L1: y ∈ Y.
    rewrite HF in HF0.
    inversion HF0 as [Z0 [x0 [y0 [HZ0 [Hyfx HXY]]]]].
    rewrite HZ0 in H.
    rewrite H in HXY.
    apply ordered_pair_in_direct_product_iff_in_and in HXY.
    apply HXY.
    have L2: exists z : U, z = g y /\ z ∈ Z.
    apply Hg in L1.
    trivial.
    inversion L2 as [z].
    apply (HGFI x x' z).
    split; split; [exists x|exists x']; exists z; split.
    reflexivity.
    exists y.
    split;[trivial|
           rewrite HG;split;exists y;exists z;split;[reflexivity|split;[apply H|apply ordered_pair_in_direct_product_iff_in_and;split;[trivial|apply H]]]].
    reflexivity.
    exists y.
    split;[trivial|
           rewrite HG;split;exists y;exists z;split;[reflexivity|split;[apply H|apply ordered_pair_in_direct_product_iff_in_and;split;[trivial|apply H]]]].
  Qed.

  Theorem compound_graph_is_surjection_to_destination_graph_is_surjection:
    forall (f g:U -> U) (X Y Z:Collection U) (F G:TypeOfDirectProduct U),
      MappingFunction f X Y ->
      F = GraphOfFunction f X Y ->
      SurjectionGraph F Y ->
      MappingFunction g Y Z ->
      G = GraphOfFunction g Y Z ->
      SurjectionGraph (G ⊙ F) Z ->
      SurjectionGraph G Z.
  Proof.
    move => f g X Y Z F G Hf HF HFS Hg HG HGS z HzZ.
    apply HGS in HzZ.
    inversion HzZ as [x].
    inversion H.
    inversion H0 as [x' [z']].
    inversion H2.
    inversion H4 as [y'].
    inversion H5.
    apply ordered_pair_to_and in H3.
    inversion H3.
    exists y'.
    rewrite H9.
    assumption.
  Qed.

  Theorem compound_graph_is_source_identity_graph_to_injection:
    forall (f g:U -> U) (X Y:Collection U) (F G:TypeOfDirectProduct U),
      MappingFunction f X Y ->
      F = GraphOfFunction f X Y ->
      MappingFunction g Y X ->
      G = GraphOfFunction g Y X ->
      G ⊙ F = GraphOfIdentity X ->
      InjectionGraph F.
  Proof.
    move => f g X Y F G Hf HF Hg HG H.
    move => x x' y [HF0 HF1].
    have Hgf: forall x:U, x ∈ X -> x = (g ◦ f) x.
    move => x0 Hx0X.
    apply (mapping_compound_function_iff_singleton_image U f g X Y X F G x0 x0); trivial.
    rewrite H.
    apply image_singleton_domain_of_graph_of_identity_eq_singleton_domain.
    trivial.
    have L1: forall x z z' : U,
        x ∈ X -> {|z|} = 𝕴𝖒( G ⊙ F, {|x|}) -> {|z'|} = 𝕴𝖒( G ⊙ F, {|x|}) -> z = z'.
    apply (compound_function_value_unique U f g X Y X F G).
    trivial.
    trivial.
    move :(L1 x x x') => L2.
    have L3: x ∈ X.
    rewrite HF in HF0.
    inversion HF0 as [Z0 [x0 [y0 []]]].
    inversion H1.
    rewrite -H0 in H4.
    apply ordered_pair_in_direct_product_iff_in_and in H4.
    apply H4.
    apply L2.
    trivial.
    rewrite H.
    apply image_singleton_domain_of_graph_of_identity_eq_singleton_domain.
    trivial.
    apply (singleton_image_of_compound_graph_iff_ordered_pair_in_compound_graph U f g X Y X F G x x'); trivial.
    split.
    exists x.
    exists x'.
    split;[reflexivity|exists y].
    split;[trivial|].
    rewrite HG.
    split.
    exists y.
    exists x'.
    split.
    reflexivity.
    rewrite HF in HF1.
    inversion HF1 as [Z1 [x1 [y1]]].
    inversion H0 as [Heq1 [Hyfx1 Hxy1]].
    apply ordered_pair_to_and in Heq1.
    inversion Heq1 as [Heq1x Heq1y].
    rewrite -Heq1x -Heq1y in Hyfx1.
    rewrite -Heq1x in Hxy1.
    rewrite -Heq1y in Hxy1.
    split.
    rewrite Hyfx1.
    apply Hgf.
    apply ordered_pair_in_direct_product_iff_in_and in Hxy1.
    apply Hxy1.
    apply ordered_pair_in_direct_product_trans.
    assumption.
  Qed.

  Theorem compound_graph_is_source_identity_graph_to_injection_2:
    forall (f g:U -> U) (X Y:Collection U) (F G:TypeOfDirectProduct U),
      MappingFunction f X Y /\ F = GraphOfFunction f X Y ->
      MappingFunction g Y X /\ G = GraphOfFunction g Y X ->
      G ⊙ F = GraphOfIdentity X ->
      InjectionGraph F.
  Proof.
    move => f g X Y F G HF HG H.
    inversion HF.
    inversion HG.
    apply (compound_graph_is_source_identity_graph_to_injection f g X Y F G);trivial.
  Qed.

  Theorem compound_graph_is_source_identity_graph_to_surjection:
    forall (f g:U -> U) (X Y:Collection U) (F G:TypeOfDirectProduct U),
      MappingFunction f X Y ->
      F = GraphOfFunction f X Y ->
      MappingFunction g Y X ->
      G = GraphOfFunction g Y X ->
      G ⊙ F = GraphOfIdentity X ->
      SurjectionGraph G X.
  Proof.
    move => f g X Y F G Hf HF Hg HG H x HxX.
    have Hgf: forall x:U, x ∈ X -> x = (g ◦ f) x.
    move => x0 Hx0X.
    apply (mapping_compound_function_iff_singleton_image U f g X Y X F G x0 x0);trivial.
    rewrite H.
    apply image_singleton_domain_of_graph_of_identity_eq_singleton_domain.
    trivial.
    have L1: exists y : U, y = f x /\ y ∈ Y.
    apply Hf.
    trivial.
    inversion L1 as [y [Hyfx HyY]].
    exists y.
    rewrite HG.
    split.
    exists y.
    exists x.
    split;[reflexivity|split].
    rewrite Hyfx.
    apply Hgf.
    trivial.
    apply ordered_pair_in_direct_product_iff_in_and.
    split;trivial.
  Qed.

  Theorem compound_graph_is_source_identity_graph_to_injection_and_surjection:
    forall (f g:U -> U) (X Y:Collection U) (F G:TypeOfDirectProduct U),
      MappingFunction f X Y ->
      F = GraphOfFunction f X Y ->
      MappingFunction g Y X ->
      G = GraphOfFunction g Y X ->
      G ⊙ F = GraphOfIdentity X ->
      InjectionGraph F /\ SurjectionGraph G X.
  Proof.
    move => f g X Y F G Hf HF Hg HG H.
    split; [apply (compound_graph_is_source_identity_graph_to_injection f g X Y F G)|
            apply (compound_graph_is_source_identity_graph_to_surjection f g X Y F G)];
    trivial.
  Qed.

  Theorem mutally_compound_function_is_idenitify_to_bijection_function:
    forall (f g:U -> U) (X Y:Collection U) (F G:TypeOfDirectProduct U),
      MappingFunction f X Y ->
      F = GraphOfFunction f X Y ->
      MappingFunction g Y X ->
      G = GraphOfFunction g Y X ->
      G ⊙ F = GraphOfIdentity X /\ F ⊙ G = GraphOfIdentity Y ->
      BijectionGraph F Y /\ BijectionGraph G X.
  Proof.
    move => f g X Y F G Hf HF Hg HG [HGFX HFGY].
    split.
    split;[apply (compound_graph_is_source_identity_graph_to_injection f g X Y F G)|
           apply (compound_graph_is_source_identity_graph_to_surjection g f Y X G F)];trivial.
    split;[apply (compound_graph_is_source_identity_graph_to_injection g f Y X G F)|
           apply (compound_graph_is_source_identity_graph_to_surjection f g X Y F G)];trivial.
  Qed.

  Theorem compound_graph_is_mutally_identity_graph_to_invertible_function_left:
    forall (f g:U -> U) (X Y:Collection U) (F G:TypeOfDirectProduct U),
      MappingFunction f X Y ->
      F = GraphOfFunction f X Y ->
      MappingFunction g Y X ->
      G = GraphOfFunction g Y X ->
      G ⊙ F = GraphOfIdentity X /\ F ⊙ G = GraphOfIdentity Y ->
      G = F ^-1.
  Proof.
    move => f g X Y F G Hf HF Hg HG [HGFX HFGY].
    have Hgf: forall x:U, x ∈ X -> x = (g ◦ f) x.
    move => x HxX.
    apply (mapping_compound_function_iff_singleton_image U f g X Y X F G x x);trivial.
    rewrite HGFX.
    apply image_singleton_domain_of_graph_of_identity_eq_singleton_domain; trivial.
    have Hfg: forall y:U, y ∈ Y -> y = (f ◦ g) y.
    move => y HyY.
    apply (mapping_compound_function_iff_singleton_image U g f Y X Y G F y y);trivial.
    rewrite HFGY.
    apply image_singleton_domain_of_graph_of_identity_eq_singleton_domain; trivial.
    apply mutally_included_to_eq; split => Z H.
    +rewrite HG in H.
     inversion H as [Z0 [y [x [HZ0 [Hxeqgy HyYxX]]]]].
     rewrite HZ0 in H0.
     rewrite -H0.
     split.
     rewrite HF.
     split.
     exists x.
     exists y.
     split;[reflexivity|split].
     apply ordered_pair_in_direct_product_to_in_and in HyYxX.
     inversion HyYxX.
     rewrite Hxeqgy.
     apply Hfg in H1.
     trivial.
     apply ordered_pair_in_direct_product_trans.
     assumption.
    +inversion H.
     rewrite HF in H0.
     inversion H0 as [Z0 [x0 [y0 [HZ0 [Hyeqfx HxXyY]]]]].
     rewrite H2 in HZ0.
     apply ordered_pair_to_and in HZ0.
     inversion HZ0.
     rewrite -H3 -H4 in Hyeqfx.
     rewrite -H3 -H4 in HxXyY.
     apply ordered_pair_in_direct_product_to_in_and in HxXyY.
     inversion HxXyY as [HxX HyY].
     rewrite HG.
     split.
     exists y.
     exists x.
     split;[reflexivity|split].
     rewrite Hyeqfx.
     apply Hgf in HxX.
     trivial.
     apply in_and_to_ordered_pair_in_direct_product.
     apply and_comm.
     assumption.
  Qed.

  Theorem compound_graph_is_mutally_identity_graph_to_invertible_function_right:
    forall (f g:U -> U) (X Y:Collection U) (F G:TypeOfDirectProduct U),
      MappingFunction f X Y ->
      F = GraphOfFunction f X Y ->
      MappingFunction g Y X ->
      G = GraphOfFunction g Y X ->
      G ⊙ F = GraphOfIdentity X /\ F ⊙ G = GraphOfIdentity Y ->
      F = G ^-1.
  Proof.
    move => f g X Y F G Hf HF Hg HG [HGFX HFGY].
    have Hgf: forall x:U, x ∈ X -> x = (g ◦ f) x.
    move => x HxX.
    apply (mapping_compound_function_iff_singleton_image U f g X Y X F G x x);trivial.
    rewrite HGFX.
    apply image_singleton_domain_of_graph_of_identity_eq_singleton_domain; trivial.
    have Hfg: forall y:U, y ∈ Y -> y = (f ◦ g) y.
    move => y HyY.
    apply (mapping_compound_function_iff_singleton_image U g f Y X Y G F y y);trivial.
    rewrite HFGY.
    apply image_singleton_domain_of_graph_of_identity_eq_singleton_domain; trivial.
    apply mutally_included_to_eq; split => Z H.
    +rewrite HF in H.
     inversion H as [Z0 [x [y [HZ0 [Hxeqgy HxXyY]]]]].
     rewrite HZ0 in H0.
     rewrite -H0.
     split.
     rewrite HG.
     split.
     exists y.
     exists x.
     split;[reflexivity|split].
     rewrite Hxeqgy.
     apply ordered_pair_in_direct_product_to_in_and in HxXyY.
     inversion HxXyY.
     apply Hgf in H1.
     trivial.
     apply ordered_pair_in_direct_product_trans.
     assumption.
    +inversion H as [y x].
     rewrite HG in H0.
     inversion H0 as [Z0 [y0 [x0 [HZ0 [Hxeqgy HyYxX]]]]].
     rewrite H2 in HZ0.
     apply ordered_pair_to_and in HZ0.
     inversion HZ0.
     rewrite -H3 -H4 in Hxeqgy.
     rewrite -H3 -H4 in HyYxX.
     rewrite HF.
     split.
     exists x.
     exists y.
     split;[reflexivity|split].
     rewrite Hxeqgy.
     apply ordered_pair_in_direct_product_to_in_and in HyYxX.
     inversion HyYxX.
     apply Hfg in H5.
     trivial.
     apply ordered_pair_in_direct_product_trans.
     assumption.
  Qed.

  Theorem compound_graph_is_mutally_identity_graph_to_invertible_function:
    forall (f g:U -> U) (X Y:Collection U) (F G:TypeOfDirectProduct U),
      MappingFunction f X Y ->
      F = GraphOfFunction f X Y ->
      MappingFunction g Y X ->
      G = GraphOfFunction g Y X ->
      G ⊙ F = GraphOfIdentity X /\ F ⊙ G = GraphOfIdentity Y ->
      G = F ^-1 /\ F = G ^-1.
  Proof.
    move => f g X Y F G Hf HF Hg HG HId.
    split;[apply (compound_graph_is_mutally_identity_graph_to_invertible_function_left f g X Y)|
           apply (compound_graph_is_mutally_identity_graph_to_invertible_function_right f g X Y)];trivial.
  Qed.

  Theorem invertible_mapping_to_exists_invertible_graph:
    forall (f:U -> U) (X Y:Collection U) (F:TypeOfDirectProduct U),
      MappingFunction f X Y ->
      F = GraphOfFunction f X Y ->
      InvertibleMapping f X Y F ->
      exists G:TypeOfDirectProduct U, G = F ^-1 /\ F = G ^-1.
  Proof.
    move => f X Y F HF Hf HGI.
    inversion HGI as [g [G [Hg [HG HId]]]].
    exists G.
    apply (compound_graph_is_mutally_identity_graph_to_invertible_function f g X Y);trivial.
  Qed.

  Theorem injection_graph_to_compound_self_inverse_graph_eq_identity_graph:
    forall (f:U -> U) (X Y:Collection U) (F:TypeOfDirectProduct U),
      MappingFunction f X Y ->
      F = GraphOfFunction f X Y ->
      InjectionGraph F ->
      (F ^-1) ⊙ F = GraphOfIdentity X.
  Proof.
    move => f X Y F Hf HF HFI.
    apply mutally_included_to_eq.
    split => Z H;
               inversion H as [Z0 [x [x']]];
               inversion H0 as [HZ].
    +inversion H2 as [y].
     split.
     exists x.
     exists x'.
     split;[trivial|].
     ++split.
       apply sym_eq.
       apply: (HFI x x' y).
       inversion H3.
       inversion H5.
       apply ordered_pair_swap in H6.
       rewrite -H6.
       split;assumption.
     ++inversion H3.
       inversion H5.
       apply ordered_pair_swap in H6.
       rewrite H6 in H7.
       rewrite HF in H4.
       rewrite HF in H7.
       inversion H4 as [Z1 [x1 [y1]]].
       inversion H8.
       inversion H11.
       rewrite -H10 in H13.
       apply ordered_pair_in_direct_product_to_in_and in H13.
       inversion H13.
       inversion H7 as [Z2 [x2 [y2]]].
       inversion H16.
       inversion H19.
       rewrite -H18 in H21.
       apply ordered_pair_in_direct_product_to_in_and in H21.
       inversion H21.
       apply ordered_pair_in_direct_product_iff_in_and.
       split; assumption.
    +inversion H2.
     split.
     exists x.
     exists x'.
     split.
     trivial.
     apply ordered_pair_in_direct_product_iff_in_and in H4.
     inversion H4.
     apply Hf in H5.
     apply Hf in H6.
     inversion H4.
     inversion H5 as [y].
     inversion H9.
     exists y.
     split;[rewrite HF;split|split; rewrite HF; split].
     exists x.
     exists y.
     split;[reflexivity|split;[trivial|apply ordered_pair_in_direct_product_iff_in_and;split;trivial]].
     inversion H6 as [y0].
     inversion H12.
     rewrite H3 in H13.
     exists x'.
     exists y0.
     split;[rewrite H10 H13;reflexivity|
            split;[rewrite H3;trivial|
                   apply ordered_pair_in_direct_product_iff_in_and;
                   split;
                   trivial]].
  Qed.

  Theorem surjection_graph_to_compound_self_inverse_graph_eq_identity_graph:
    forall (f:U -> U) (X Y:Collection U) (F:TypeOfDirectProduct U),
      MappingFunction f X Y ->
      F = GraphOfFunction f X Y ->
      SurjectionGraph F Y ->
      F ⊙ (F ^-1) = GraphOfIdentity Y.
  Proof.
    move => f X Y F Hf HF HFS.
    apply mutally_included_to_eq.
    split => Z H.
    inversion H as [Z0 [y [y' [HZ0 [x [HF0 HF1]]]]]].
    rewrite HZ0 in H0.
    rewrite -H0.
    inversion HF0.
    apply ordered_pair_swap in H1.
    rewrite H1 in H2.
    rewrite HF in HF1.
    rewrite HF in H2.
    inversion HF1 as [Z1 [x1 [y1 [Heq1 [Hyeqfx1]]]]].
    rewrite Heq1 in H4.
    rewrite H4 in H3.
    apply ordered_pair_to_and in H4.
    inversion H4.
    rewrite H5 H6 in Hyeqfx1.
    inversion H2 as [Z2 [x2 [y2 [Heq2 [Hyeqfx2]]]]].
    rewrite Heq2 in H8.
    rewrite H8 in H7.
    apply ordered_pair_to_and in H8.
    inversion H8.
    rewrite H9 H10 in Hyeqfx2.
    rewrite Hyeqfx1 Hyeqfx2.
    apply ordered_pair_in_graph_of_identity.
    rewrite -Hyeqfx1.
    apply ordered_pair_in_direct_product_to_in_and in H3.
    apply H3.
    inversion H as [Z0 [y [y' [HZ0 [HId]]]]].
    rewrite HZ0 in H1.
    rewrite -H1.
    split.
    exists y.
    exists y'.
    split;[reflexivity|].
    apply ordered_pair_in_direct_product_to_in_and in H0.
    inversion H0.
    apply HFS in H2.
    apply HFS in H3.
    inversion H2 as [x].
    inversion H3 as [x'].
    exists x.
    split.
    split.
    trivial.
    rewrite HId.
    trivial.
  Qed.

  Theorem bijection_graph_to_compound_self_inverse_graph_eq_identity_graph:
    forall (f:U -> U) (X Y:Collection U) (F:TypeOfDirectProduct U),
      MappingFunction f X Y ->
      F = GraphOfFunction f X Y ->
      BijectionGraph F Y ->
      (F ^-1) ⊙ F = GraphOfIdentity X /\ F ⊙ (F ^-1) = GraphOfIdentity Y.
  Proof.
    move => f X Y F Hf HF [HIF HSF].
    split;[apply (injection_graph_to_compound_self_inverse_graph_eq_identity_graph f X Y F)|
           apply (surjection_graph_to_compound_self_inverse_graph_eq_identity_graph f X Y F)];trivial.
  Qed.

  Theorem outer_of_composite_function_is_injection_to_inner_is_unique:
    forall (f0 f1 g:U -> U) (X Y Z:Collection U) (F0 F1 G:TypeOfDirectProduct U),
      MappingFunction f0 X Y ->
      F0 = GraphOfFunction f0 X Y ->
      MappingFunction f1 X Y ->
      F1 = GraphOfFunction f1 X Y ->
      MappingFunction g Y Z ->
      G = GraphOfFunction g Y Z ->
      InjectionGraph G -> (G ⊙ F0 = G ⊙ F1 -> F0 = F1).
  Proof.
    move => f0 f1 g X Y Z F0 F1 G Hf0 HF0 Hf1 HF1 Hg HG HIG Heq.
    have Heqfg: forall x:U, x ∈ X -> (g ◦ f0) x = (g ◦ f1) x.
    apply (compound_graph_eq_iff_compound_function_eq U f0 f1 g g X Y Z F0 F1 G G);trivial.
    apply (function_eq_to_graph_of_function_eq U f0 f1 X Y F0 F1);trivial.
    move => x HxX.
    have Heqfgx: (g ◦ f0) x = (g ◦ f1) x.
    apply Heqfg.
    trivial.
    unfold InjectionGraph in HIG.
    apply (HIG (f0 x) (f1 x) ((g ◦ f0) x)).
    split;rewrite HG;split.
    exists (f0 x).
    exists ((g ◦ f0) x).
    split;[reflexivity|split;[reflexivity|]].
    apply Hf0 in HxX.
    inversion HxX as [y' [Hy'f0x Hy'Y]].
    rewrite Hy'f0x in Hy'Y.
    apply in_and_to_ordered_pair_in_direct_product.
    split.
    trivial.
    apply Hg in Hy'Y.
    inversion Hy'Y as [z' [Hzgf0x Hz'Z]].
    rewrite Hzgf0x in Hz'Z.
    trivial.
    exists (f1 x).
    exists ((g ◦ f0) x).
    split;[reflexivity|split;[rewrite Heqfgx;reflexivity|]].
    apply Hf1 in HxX.
    inversion HxX as [y' [Hy'f1x Hy'Y]].
    rewrite Hy'f1x in Hy'Y.
    apply in_and_to_ordered_pair_in_direct_product.
    split;trivial.
    apply Hg in Hy'Y.
    inversion Hy'Y as [z' [Hzgf1x Hz'Z]].
    rewrite Hzgf1x in Hz'Z.
    rewrite Heqfgx.
    trivial.
  Qed.

  Theorem injection_graph_has_inversible_graph:
    forall (f:U -> U) (X Y:Collection U) (F:TypeOfDirectProduct U),
      MappingFunction f X Y ->
      F = GraphOfFunction f X Y ->
      (InjectionGraph F -> (exists g:U->U, exists G:TypeOfDirectProduct U,
                                 (MappingFunction g Y X /\ G = GraphOfFunction g Y X) ->
                                 G ⊙ F = GraphOfIdentity X) \/ X = `Ø`).
  Proof.
    move => f X Y F Hf HF HIF.
    suff:  X = `Ø` \/ X <> `Ø`.
    case => HX.
    right.
    trivial.
    left.
    apply not_empty_collection_to_exists_element_in_collection in HX.
    inversion HX as [x HxX].
    move: (fun _:U => x) => g.
    exists g.
    exists (F ^-1).
    case =>[Hg HG].
    apply (injection_graph_to_compound_self_inverse_graph_eq_identity_graph f X Y);trivial.
    apply LawOfExcludedMiddle.
  Qed.

  Goal forall (f:U -> U) (X Y:Collection U) (F:TypeOfDirectProduct U),
      MappingFunction f X Y ->
      F = GraphOfFunction f X Y ->
      (((exists g:U->U, exists G:TypeOfDirectProduct U,
              MappingFunction g Y X /\
              G = GraphOfFunction g Y X /\
              G ⊙ F = GraphOfIdentity X) \/ X = `Ø`) -> InjectionGraph F).
  Proof.
    move => f X Y F Hf HF [H|H].
    inversion H as [g [G [Hg [HG HGF]]]].
    apply (compound_graph_is_source_identity_graph_to_injection f g X Y F G);trivial.
    move => x x' y.
    rewrite HF.
    move => [HF0 HF1].
    inversion HF0 as [Z0 [x0' [y0' [Heq0 [Hyfx0 HxXyY0]]]]].
    rewrite Heq0 in H0.
    rewrite H0 in HxXyY0.
    inversion HF1 as [Z1 [x1' [y1' [Heq1 [Hyfx1 HxXyY1]]]]].
    rewrite Heq1 in H1.
    rewrite H1 in HxXyY1.
    apply ordered_pair_in_direct_product_to_in_and in HxXyY0.
    inversion HxXyY0 as [HxX HyY0].
    apply ordered_pair_in_direct_product_to_in_and in HxXyY1.
    inversion HxXyY1 as [Hx'X HyY1].
    rewrite H in HxX.
    rewrite H in Hx'X.
    apply DoubleNegativeElimination.
    move => Hxx'.
    move: HxX.
    apply noone_in_empty.
  Qed.

End MappingMorphism.
