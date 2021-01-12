From mathcomp Require Import ssreflect.

Require Import collect_operator.

Inductive DirectProduct {U:Type} (X Y:Collection U) : Collection (Collection (Collection U)) :=
| definition_of_direct_product:
    forall Z: Collection (Collection U),
      (exists x:U, exists y:U, (x ∈ X /\ y ∈ Y /\ Z = <|x, y|>)) -> Z ∈ DirectProduct X Y.

Inductive FirstProjection {U:Type} (G: Collection (Collection (Collection U))) : Collection U :=
| first_projection_accessor: forall x:U, (exists y:U, <|x,y|> ∈ G) -> FirstProjection G x.

Inductive SecondProjection {U:Type} (G: Collection (Collection (Collection U))) : Collection U :=
| second_projection_accessor: forall y:U, (exists x:U, <|x,y|> ∈ G) -> SecondProjection G y.
