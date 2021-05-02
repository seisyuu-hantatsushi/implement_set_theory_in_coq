From mathcomp Require Import ssreflect.

Require Import relation.

Axiom AxiomOfPower:
  forall U:Type, forall x: Collection U, exists y':Collection (Collection U), forall z:Collection U,
          (z ⊂ x -> z ∈ y').

Inductive PowerCollection {U:Type} (A:Collection U) : Collection (Collection U) :=
| definition_of_power: forall x':Collection U, x' ⊂ A -> x' ∈ PowerCollection A.

(* 𝔓:Unicode 1D513 *)
Notation "𝔓( X )" := (PowerCollection X) (at level 15).

Section AxiomOfPowerTest.
  Variable U:Type.

  Goal
    forall x': Collection U, forall Z:Collection (Collection U),
        Z = PowerCollection x' ->
        exists y':Collection (Collection U), forall z:Collection U, (z ⊂ x' -> z ∈ y').
  Proof.
    move => x' Z HZ.
    exists Z.
    rewrite HZ.
    move => z Hzx'.
    apply definition_of_power.
    apply Hzx'.
  Qed.
End AxiomOfPowerTest.

