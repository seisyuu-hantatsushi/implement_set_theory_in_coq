From mathcomp Require Import ssreflect.

Require Import collect_operator.

Inductive DirectProduct (U:Type) (X Y:Collection U) : Collection (Collection (Collection U)) :=
| definition_of_direct_product:
    forall Z: Collection (Collection U),
      (exists x:U, exists y:U, (x ∈ X /\ y ∈ Y /\ Z = <|x, y|>)) -> Z ∈ DirectProduct U X Y.




