From mathcomp Require Import ssreflect.

Require Import relation.

Axiom AxiomOfPower:
  forall U:Type, forall x: Collection U, exists y':Collection (Collection U), forall z:Collection U,
          (z ⊂ x -> z ∈ y').

Inductive PowerCollection (U:Type) (A:Collection U) : Collection (Collection U) :=
| definition_of_power: forall x':Collection U, x' ⊂ A -> x' ∈ PowerCollection U A.

Section AxiomOfPowerTest.
  Variable U:Type.

  Goal
    forall x: Collection U, forall Z:Collection (Collection U),
        Z = PowerCollection U x ->
        exists y':Collection (Collection U), forall z:Collection U, (z ⊂ x -> z ∈ y').
  Proof.
    move => x' Z HZ.
    exists Z.
    rewrite HZ.
    move => z Hzx'.
    apply definition_of_power.
    apply Hzx'.
  Qed.
End AxiomOfPowerTest.
