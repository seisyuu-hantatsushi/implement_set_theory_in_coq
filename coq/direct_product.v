From mathcomp Require Import ssreflect.

Require Import collect_operator.

Inductive DirectProduct {U:Type} (X Y:Collection U) : Collection (Collection (Collection U)) :=
| definition_of_direct_product:
    forall Z: Collection (Collection U),
      (exists x:U, exists y:U, (x ∈ X /\ y ∈ Y /\ Z = <|x, y|>)) -> Z ∈ DirectProduct X Y.

Notation "A × B" := (DirectProduct A B) (right associativity, at level 30).

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

End DirectProduct.
    

