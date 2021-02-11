From mathcomp Require Import ssreflect.

Require Import collect_operator.
Require Import direct_product.
Require Import mapping.

Definition InvertibleMapping {U} (f:U->U) (X Y:Collection U) (F:TypeOfDirectProduct U) :=
  exists (g:U->U) (G:TypeOfDirectProduct U), G = GraphOfFunction g Y X /\
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
    rewrite -(associativity_of_graph_of_function h f g Y X Y X H F G).
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

  Goal
    forall (f:U->U) (X Y:Collection U) (F:TypeOfDirectProduct U),
      F = GraphOfFunction f X Y ->
      InvertibleMapping f X Y F ->
      forall (x x' y:U), <|x,y|> ∈ F /\ <|x',y|> ∈ F -> x = x'.
  Proof.
    move => f X Y F HF HIF x x' y.
    case => H0 H1.
    inversion HIF as [g [G [HG [HGF HFG]]]].
    move HCGF: (GraphOfFunction (CompoundFunction g f) X X) => GF.
    move HCFG: (GraphOfFunction (CompoundFunction f g) Y Y) => FG.
    have L1: G = F^-1.
    rewrite HF HG.
    apply mutally_included_to_eq.
    split.
    move => Z H.
    inversion H as [Z0 [y0 [x0]]].
    inversion H2.
    rewrite H4.
    split.

    rewrite -(compound_graph_of_function_eq_graph_of_compound_function U f g X Y X F G (GraphOfIdentity X)) in HGF.
    rewrite (compound_graph_of_function_eq_graph_of_compound_function U f g X Y X F G (GraphOfIdentity X)) in HGF.
    
End InverseMapping.
