From mathcomp Require Import ssreflect.

Require Import collect_operator.
Require Import direct_product.

Definition BinaryRelation U := U -> U -> Prop.

Definition GraphOfMapping {U:Type} (G:TypeOfDirectProduct U) (A B:Collection U) :=
  G ⊂ A × B /\ forall x:U, x ∈ A -> exists! y:U, <|x,y|> ∈ G.

Inductive GraphOfBinaryRelation {U:Type} (R:BinaryRelation U) (A B:Collection U) :
  TypeOfDirectProduct U :=
| definition_of_graph_of_binary_relation:
    forall x y:U, (R x y /\ <|x,y|> ∈ A × B) -> <|x,y|> ∈ GraphOfBinaryRelation R A B.

Definition GraphOfFunction {U:Type} (f: U -> U) (A B:Collection U) :
  TypeOfDirectProduct U := GraphOfBinaryRelation (fun (x y:U) => y = f x) A B.

Inductive DomainOfGraph {U:Type} (G:TypeOfDirectProduct U) : Collection U :=
| definition_of_domain_of_map: forall x:U, x ∈ FirstProjection G -> x ∈ DomainOfGraph G.

Inductive RangeOfGraph {U:Type} (G:TypeOfDirectProduct U) : Collection U :=
| definition_of_range_of_map: forall y:U, y ∈ SecondProjection G -> y ∈ RangeOfGraph G.

Section Mapping.
  Variable U:Type.
  Variable f: U -> U.

  Theorem relation_determine_domain:
    forall (R:BinaryRelation U) (A B:Collection U) (G:TypeOfDirectProduct U),
      G = GraphOfBinaryRelation R A B -> DomainOfGraph G ⊂ A.
  Proof.
    move => R A B G HG x HDG.
    inversion HDG as [x0 HFG].
    inversion HFG as [x1 H0].
    case: H0 => y HGp.
    rewrite HG in HGp.
    inversion HGp.
    inversion H2.
    rewrite H0 in H4.
    apply ordered_pair_in_direct_product_to_in_and in H4.
    inversion H4.
      by [].
  Qed.

  Theorem relation_determine_range:
    forall (R:BinaryRelation U) (A B:Collection U) (G:TypeOfDirectProduct U),
      G = GraphOfBinaryRelation R A B -> RangeOfGraph G ⊂ B.
  Proof.
    move => R A B G HG y HRG.
    inversion HRG as [y0 HSG].
    inversion HSG as [y1 H0].
    case: H0 => x HGp.
    rewrite HG in HGp.
    inversion HGp.
    inversion H2.
    rewrite H0 in H4.
    apply ordered_pair_in_direct_product_to_in_and in H4.
    inversion H4.
      by [].
  Qed.

  Theorem function_determine_domain:
    forall (A B:Collection U) (G:TypeOfDirectProduct U),
      G = GraphOfFunction f A B -> DomainOfGraph G ⊂ A.
  Proof.
    move => A B G HG.
    move: (relation_determine_domain (fun (x y:U) => y = f x) A B G).
    apply.
    rewrite HG.
    reflexivity.
  Qed.

  Theorem function_determine_range:
    forall (A B:Collection U) (G:TypeOfDirectProduct U),
      G = GraphOfFunction f A B -> RangeOfGraph G ⊂ B.
  Proof.
    move => A B G HG.
    move: (relation_determine_range (fun (x y:U) => y = f x) A B G).
    apply.
    rewrite HG.
    reflexivity.
  Qed.

  Theorem direct_product_included_graph_of_function:
    forall (A B:Collection U) (G:TypeOfDirectProduct U),
      G = GraphOfFunction f A B -> G ⊂ A × B.
  Proof.
    move => A B G HG.
    rewrite HG.
    move => Z'.
    split.
    inversion H.
    exists x.
    exists y.
    inversion H0.
    apply ordered_pair_in_direct_product_to_in_and in H3.
    inversion H3.
    split; [by []|split;[by []|reflexivity]].
  Qed.

  Theorem function_satisfies_graph_of_mapping:
    forall (A B:Collection U) (G:TypeOfDirectProduct U),
      (forall x y:U, y = f x /\ <|x, y|> ∈ A × B) ->
      G = GraphOfFunction f A B ->
      GraphOfMapping G A B.
  Proof.
    move => A B G HF HG.
    split.
    +apply direct_product_included_graph_of_function. by [].
    +move => x.
     move Hf: (f x) => y HA.
     exists y.
     split.
     rewrite HG.
     split.
     split.
     rewrite Hf.
     reflexivity.
    +case: (HF x y) => Hfy HABy. by [].
    +move => z H0.
     case: (HF x z) => Hfz HABz.
     rewrite -Hf -Hfz.
     reflexivity.
  Qed.
  
End Mapping.
